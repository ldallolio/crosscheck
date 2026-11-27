// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Solver.hpp"

#include <z3++.h>

#include "Z3Limits.hpp"

#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>

namespace crosscheck {

namespace {


z3::expr intConst(z3::context& ctx, std::int64_t v) {
  return ctx.int_val(static_cast<int64_t>(v));
}

z3::expr realConst(z3::context& ctx, std::int64_t v) {
  return ctx.real_val(static_cast<int64_t>(v));
}

void collectSymbols(const LinExpr& e, std::set<SymId>& out) {
  for (const auto& [s, c] : e.terms()) out.insert(s);
}

/// Range facts `lo <= s <= hi` of the given symbols, as constraints.
std::vector<Constraint> rangeFacts(const SymbolTable& syms, const std::set<SymId>& used) {
  std::vector<Constraint> out;
  for (SymId s : used) {
    const Symbol& sym = syms[s];
    if (sym.lo) out.push_back(ge(LinExpr::symbol(s), LinExpr::constant(*sym.lo)));
    if (sym.hi) out.push_back(le(LinExpr::symbol(s), LinExpr::constant(*sym.hi)));
  }
  return out;
}

/// Integer encoding of `e` (must not be poisoned).
z3::expr encodeInt(z3::context& ctx, const LinExpr& e) {
  z3::expr acc = intConst(ctx, e.constantTerm());
  for (const auto& [s, c] : e.terms())
    acc = acc + intConst(ctx, c) * ctx.int_const(("s" + std::to_string(s)).c_str());
  return acc;
}

/// Drops poisoned constraints (dropping a premise is always sound) and adds the
/// ranges of every symbol mentioned, including those in `extra`.
std::vector<Constraint> closePremises(const SymbolTable& syms,
                                      const std::vector<Constraint>& facts,
                                      const std::vector<LinExpr>& extra) {
  std::vector<Constraint> out;
  std::set<SymId> used;
  for (const Constraint& c : facts) {
    if (c.e.poisoned()) continue;
    out.push_back(c);
    collectSymbols(c.e, used);
  }
  for (const LinExpr& e : extra) collectSymbols(e, used);
  for (Constraint& c : rangeFacts(syms, used)) out.push_back(std::move(c));
  return out;
}

// --- memoisation ----------------------------------------------------------------
// The queries below are functions of the closed premises (the facts with the ranges of
// their symbols) and the goal, so their answers are cached under a textual key: the
// analysis asks the same questions many times when it re-runs the bodies of nested
// loops. A cached answer is the answer Z3 gave the first time; the cache is cleared when
// it grows large.
constexpr std::size_t kCacheLimit = 1u << 20;

void keyOf(std::string& k, const LinExpr& e) {
  k += std::to_string(e.constantTerm());
  for (const auto& [s, c] : e.terms()) {
    k += ' ';
    k += std::to_string(s);
    k += '*';
    k += std::to_string(c);
  }
  k += ';';
}

std::string keyOf(char kind, const std::vector<Constraint>& closed, const LinExpr* goal) {
  std::string k(1, kind);
  for (const Constraint& c : closed) keyOf(k, c.e);
  k += '|';
  if (goal) keyOf(k, *goal);
  return k;
}

template <class V>
std::unordered_map<std::string, V>& cache() {
  static thread_local std::unordered_map<std::string, V> m;
  if (m.size() > kCacheLimit) m.clear();
  return m;
}

std::uint64_t& callCounter() {
  static thread_local std::uint64_t n = 0;
  return n;
}

bool feasibleClosedRaw(const std::vector<Constraint>& closed);

/// One Z3 context per thread for the cached queries (each query has its own solver),
/// renewed now and then so that its tables do not grow without limit; creating a
/// context per query dominated the time of small queries.
z3::context& sharedContext() {
  static thread_local std::unique_ptr<z3::context> ctx;
  static thread_local unsigned uses = 0;
  if (!ctx || ++uses > 20000) {
    ctx.reset();
    ctx = std::make_unique<z3::context>();
    uses = 0;
  }
  return *ctx;
}

bool feasibleClosed(const std::vector<Constraint>& closed) {
  callCounter() += closed.size() + 1;
  auto& m = cache<bool>();
  std::string k = keyOf('F', closed, nullptr);
  if (auto it = m.find(k); it != m.end()) return it->second;
  bool r = feasibleClosedRaw(closed);
  m.emplace(std::move(k), r);
  return r;
}

bool feasibleClosedRaw(const std::vector<Constraint>& closed) {
  try {
    z3::context& ctx = sharedContext();
    z3::solver solver(ctx);
    z3::params p(ctx);
    z3limits::apply(p);
    solver.set(p);
    for (const Constraint& c : closed) solver.add(encodeInt(ctx, c.e) <= 0);
    return z3limits::check(solver) != z3::unsat;
  } catch (const z3::exception&) {
    return true;
  }
}

std::optional<Rational> toRational(const z3::expr& v) {
  if (!v.is_numeral()) return std::nullopt;
  std::int64_t num = 0, den = 1;
  if (v.is_int()) {
    if (!v.is_numeral_i64(num)) return std::nullopt;
    return Rational{num, 1};
  }
  if (!v.numerator().is_numeral_i64(num) || !v.denominator().is_numeral_i64(den))
    return std::nullopt;
  return Rational{num, den};
}

/// One term `u * L` of a Farkas target, `u` being an unknown (or constant) of
/// the template and `L` a known affine expression.
struct TargetTerm {
  z3::expr u;
  LinExpr l;
};

/// Adds to `opt` the Farkas certificate constraints for
///   forall x.  (/\_i  P_i(x) <= 0)  ==>  sum_t u_t * L_t(x) + k <= 0.
/// Writing `P_i = p_i . x + q_i` and the target as `c . x + d`, the certificate
/// is a vector `lambda >= 0` with `sum_i lambda_i p_i = c` and
/// `d <= sum_i lambda_i q_i`. Soundness is the easy direction of Farkas' Lemma
/// (Lean: `farkas_sound`); it does not need the premises to be satisfiable.
void addFarkas(z3::context& ctx, z3::optimize& opt, const std::vector<Constraint>& premises,
               const std::vector<TargetTerm>& target, const z3::expr& k, unsigned& fresh) {
  std::set<SymId> used;
  for (const Constraint& c : premises) collectSymbols(c.e, used);
  for (const TargetTerm& t : target) collectSymbols(t.l, used);

  std::vector<z3::expr> lambda;
  for (std::size_t i = 0; i < premises.size(); ++i) {
    lambda.push_back(ctx.real_const(("l" + std::to_string(fresh++)).c_str()));
    opt.add(lambda.back() >= 0);
  }
  for (SymId s : used) {
    z3::expr lhs = realConst(ctx, 0);
    for (std::size_t i = 0; i < premises.size(); ++i) {
      std::int64_t c = premises[i].e.coefficient(s);
      if (c != 0) lhs = lhs + lambda[i] * realConst(ctx, c);
    }
    z3::expr rhs = realConst(ctx, 0);
    for (const TargetTerm& t : target) {
      std::int64_t c = t.l.coefficient(s);
      if (c != 0) rhs = rhs + t.u * realConst(ctx, c);
    }
    opt.add(lhs == rhs);
  }
  z3::expr d = k;
  for (const TargetTerm& t : target)
    if (t.l.constantTerm() != 0) d = d + t.u * realConst(ctx, t.l.constantTerm());
  z3::expr q = realConst(ctx, 0);
  for (std::size_t i = 0; i < premises.size(); ++i)
    if (premises[i].e.constantTerm() != 0)
      q = q + lambda[i] * realConst(ctx, premises[i].e.constantTerm());
  opt.add(d <= q);
}

}  // namespace

std::string Rational::str() const {
  return den == 1 ? std::to_string(num) : std::to_string(num) + "/" + std::to_string(den);
}

bool isFeasible(const SymbolTable& syms, const std::vector<Constraint>& facts) {
  return feasibleClosed(closePremises(syms, facts, {}));
}

std::uint64_t solverCalls() { return callCounter(); }

std::uint64_t solverTimeouts() { return z3limits::timeouts(); }

bool entails(const SymbolTable& syms, const std::vector<Constraint>& facts,
             const Constraint& goal) {
  if (goal.e.poisoned()) return false;
  if (goal.e.isConstant()) {
    if (goal.e.constantTerm() <= 0) return true;
    // A false goal is entailed only by contradictory facts.
  }
  std::vector<Constraint> closed = closePremises(syms, facts, {goal.e});
  callCounter() += closed.size() + 1;
  auto& m = cache<bool>();
  std::string key = keyOf('E', closed, &goal.e);
  if (auto it = m.find(key); it != m.end()) return it->second;
  bool r = [&] {
  try {
    z3::context& ctx = sharedContext();
    z3::solver solver(ctx);
    z3::params p(ctx);
    z3limits::apply(p);
    solver.set(p);
    for (const Constraint& c : closed) solver.add(encodeInt(ctx, c.e) <= 0);
    solver.add(encodeInt(ctx, goal.e) > 0);
    return z3limits::check(solver) == z3::unsat;
  } catch (const z3::exception&) {
    return false;
  }
  }();
  m.emplace(std::move(key), r);
  return r;
}

std::optional<Interval> boundsOf(const SymbolTable& syms, const std::vector<Constraint>& facts,
                                 const LinExpr& e) {
  if (e.poisoned()) return Interval{};
  if (e.isConstant()) return Interval{e.constantTerm(), e.constantTerm()};
  std::vector<Constraint> closed = closePremises(syms, facts, {e});
  callCounter() += closed.size() + 1;
  auto& m = cache<std::optional<Interval>>();
  std::string key = keyOf('B', closed, &e);
  if (auto it = m.find(key); it != m.end()) return it->second;
  std::optional<Interval> res = [&]() -> std::optional<Interval> {
  Interval out;
  // A variable of `e` that no premise mentions makes `e` unbounded both ways when the premises
  // are satisfiable: answered without the optimiser, whose search for an end does not stop on
  // such an objective in some Z3 versions (4.8.12 runs to the backstop; 5.1.0 answers at once,
  // with no end on either side, as here).
  for (const auto& [s, _c] : e.terms()) {
    bool mentioned = false;
    for (const Constraint& c : closed)
      if (c.e.coefficient(s) != 0) { mentioned = true; break; }
    if (!mentioned) return feasibleClosed(closed) ? std::optional<Interval>(out) : std::nullopt;
  }
  for (bool upper : {true, false}) {
    std::optional<std::int64_t> end;
    try {
      z3::context& ctx = sharedContext();
      z3::optimize opt(ctx);
      z3::params p(ctx);
      z3limits::apply(p);
      opt.set(p);
      for (const Constraint& c : closed) opt.add(encodeInt(ctx, c.e) <= 0);
      z3::expr target = encodeInt(ctx, e);
      z3::optimize::handle h = upper ? opt.maximize(target) : opt.minimize(target);
      z3::check_result r = z3limits::check(opt);
      if (r == z3::unsat) return std::nullopt;
      if (r == z3::sat) {
        z3::expr v = upper ? opt.upper(h) : opt.lower(h);
        std::int64_t n = 0;
        if (v.is_numeral() && v.is_int() && v.is_numeral_i64(n)) end = n;
      }
    } catch (const z3::exception&) {
    }
    // Never trust the optimiser alone: the bound must be entailed.
    if (end) {
      Constraint goal = upper ? le(e, LinExpr::constant(*end)) : ge(e, LinExpr::constant(*end));
      if (!entails(syms, facts, goal)) end.reset();
    }
    (upper ? out.hi : out.lo) = end;
  }
  return out;
  }();
  m.emplace(std::move(key), res);
  return res;
}

std::optional<RankingResult> synthesizeRanking(const SymbolTable& syms,
                                               const RankingProblem& problem, bool unbounded) {
  const std::size_t n = problem.slots;
  RankingResult zero;
  zero.weights.assign(n, Rational{});

  if (problem.entry.size() != n) return std::nullopt;
  for (const LinExpr& e : problem.entry)
    if (e.poisoned()) return std::nullopt;

  // A loop that cannot be entered performs no step.
  std::vector<Constraint> entryFacts = closePremises(syms, problem.entryFacts, problem.entry);
  if (!feasibleClosed(entryFacts)) return zero;

  // Steps whose premises are contradictory are dead paths.
  struct LiveStep {
    const RankingProblem::Step* step;
    std::vector<Constraint> premises;
  };
  std::vector<LiveStep> live;
  for (const RankingProblem::Step& s : problem.steps) {
    if (s.pre.size() != n || s.post.size() != n) return std::nullopt;
    std::vector<LinExpr> mentioned = s.pre;
    mentioned.insert(mentioned.end(), s.post.begin(), s.post.end());
    for (const LinExpr& e : mentioned)
      if (e.poisoned()) return std::nullopt;
    std::vector<Constraint> closed = closePremises(syms, s.premises, mentioned);
    if (!feasibleClosed(closed)) continue;
    live.push_back(LiveStep{&s, std::move(closed)});
  }
  if (live.empty()) return zero;

  try {
    z3::context ctx;
    z3::optimize opt(ctx);
    z3::params p(ctx);
    z3limits::apply(p);
    opt.set(p);

    std::vector<z3::expr> w;
    for (std::size_t j = 0; j < n; ++j)
      w.push_back(ctx.real_const(("w" + std::to_string(j)).c_str()));
    z3::expr c0 = ctx.real_const("c0");
    z3::expr bound = ctx.real_const("K");
    unsigned fresh = 0;

    for (const LiveStep& ls : live) {
      // Descent: sum_j w_j * (post_j - pre_j) + 1 <= 0.
      std::vector<TargetTerm> descent;
      // Positivity: -sum_j w_j * pre_j - c0 + 1 <= 0.
      std::vector<TargetTerm> positivity;
      for (std::size_t j = 0; j < n; ++j) {
        LinExpr delta = ls.step->post[j] - ls.step->pre[j];
        if (delta.poisoned()) return std::nullopt;
        descent.push_back(TargetTerm{w[j], delta});
        positivity.push_back(TargetTerm{w[j], -ls.step->pre[j]});
      }
      addFarkas(ctx, opt, ls.premises, descent, realConst(ctx, 1), fresh);
      addFarkas(ctx, opt, ls.premises, positivity, realConst(ctx, 1) - c0, fresh);
    }

    // Bound: sum_j w_j * entry_j + c0 - K <= 0, with K >= 0 minimal.
    std::vector<TargetTerm> bounding;
    for (std::size_t j = 0; j < n; ++j) bounding.push_back(TargetTerm{w[j], problem.entry[j]});
    if (!unbounded) {
      addFarkas(ctx, opt, entryFacts, bounding, c0 - bound, fresh);
      opt.add(bound >= 0);
      opt.minimize(bound);
    } else {
      // No constant bound on entry is asked for; a small potential is preferred.
      z3::expr size = realConst(ctx, 0);
      for (std::size_t j = 0; j <= n; ++j) {
        z3::expr a = ctx.real_const(("a" + std::to_string(j)).c_str());
        const z3::expr& x = j < n ? w[j] : c0;
        opt.add(a >= x && a >= -x);
        size = size + a;
      }
      opt.add(bound == 0);
      opt.minimize(size);
    }

    if (z3limits::check(opt) != z3::sat) return std::nullopt;
    z3::model m = opt.get_model();

    RankingResult result;
    for (std::size_t j = 0; j < n; ++j) {
      std::optional<Rational> r = toRational(m.eval(w[j], true));
      if (!r) return std::nullopt;
      result.weights.push_back(*r);
    }
    std::optional<Rational> off = toRational(m.eval(c0, true));
    std::optional<Rational> k = toRational(m.eval(bound, true));
    if (!off || !k || k->den <= 0 || k->num < 0) return std::nullopt;
    result.offset = *off;
    result.bound = static_cast<std::uint64_t>(k->num / k->den);  // floor, K >= 0
    result.symbolic = unbounded;
    return result;
  } catch (const z3::exception&) {
    return std::nullopt;
  }
}

std::optional<RankingResult> synthesizeSizePotential(const SymbolTable& syms,
                                                     const SizeProblem& problem) {
  const std::size_t n = problem.slots;
  if (problem.entry.size() != n) return std::nullopt;
  for (const LinExpr& e : problem.entry)
    if (e.poisoned()) return std::nullopt;

  std::vector<Constraint> entryFacts = closePremises(syms, problem.entryFacts, problem.entry);

  struct LivePath {
    const SizeProblem::Path* path;
    std::vector<Constraint> premises;
  };
  std::vector<LivePath> live;
  for (const SizeProblem::Path& p : problem.paths) {
    if (p.pre.size() != n) return std::nullopt;
    std::vector<LinExpr> mentioned = p.pre;
    for (const auto& call : p.calls) {
      if (call.size() != n) return std::nullopt;
      mentioned.insert(mentioned.end(), call.begin(), call.end());
    }
    for (const LinExpr& e : mentioned)
      if (e.poisoned()) return std::nullopt;
    std::vector<Constraint> closed = closePremises(syms, p.premises, mentioned);
    if (!feasibleClosed(closed)) continue;
    live.push_back(LivePath{&p, std::move(closed)});
  }

  try {
    z3::context ctx;
    z3::optimize opt(ctx);
    z3::params prm(ctx);
    z3limits::apply(prm);
    opt.set(prm);

    std::vector<z3::expr> w;
    for (std::size_t j = 0; j < n; ++j)
      w.push_back(ctx.real_const(("w" + std::to_string(j)).c_str()));
    z3::expr c0 = ctx.real_const("c0");
    z3::expr bound = ctx.real_const("K");
    unsigned fresh = 0;

    for (const LivePath& lp : live) {
      // sum_j w_j * (sum_i call_i[j] - pre[j]) + (k - 1) * c0 + 1 <= 0.
      std::vector<TargetTerm> target;
      for (std::size_t j = 0; j < n; ++j) {
        LinExpr delta = -lp.path->pre[j];
        for (const auto& call : lp.path->calls) delta = delta + call[j];
        if (delta.poisoned()) return std::nullopt;
        target.push_back(TargetTerm{w[j], delta});
      }
      std::int64_t k = static_cast<std::int64_t>(lp.path->calls.size());
      addFarkas(ctx, opt, lp.premises, target, realConst(ctx, k - 1) * c0 + realConst(ctx, 1),
                fresh);
    }

    std::vector<TargetTerm> bounding;
    for (std::size_t j = 0; j < n; ++j) bounding.push_back(TargetTerm{w[j], problem.entry[j]});
    addFarkas(ctx, opt, entryFacts, bounding, c0 - bound, fresh);
    opt.add(bound >= 1);
    opt.minimize(bound);

    if (z3limits::check(opt) != z3::sat) return std::nullopt;
    z3::model m = opt.get_model();

    RankingResult result;
    for (std::size_t j = 0; j < n; ++j) {
      std::optional<Rational> r = toRational(m.eval(w[j], true));
      if (!r) return std::nullopt;
      result.weights.push_back(*r);
    }
    std::optional<Rational> off = toRational(m.eval(c0, true));
    std::optional<Rational> k = toRational(m.eval(bound, true));
    if (!off || !k || k->den <= 0 || k->num < 0) return std::nullopt;
    result.offset = *off;
    result.bound = static_cast<std::uint64_t>(k->num / k->den);
    return result;
  } catch (const z3::exception&) {
    return std::nullopt;
  }
}

}  // namespace crosscheck
