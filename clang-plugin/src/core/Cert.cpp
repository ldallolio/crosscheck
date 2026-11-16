// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Cert.hpp"

#include <z3++.h>

#include <algorithm>
#include <functional>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>

namespace crosscheck::cert {

namespace {

constexpr unsigned kTimeoutMs = 10000;
constexpr std::size_t kMaxConstraints = 64;

std::int64_t at(const Vec& v, std::size_t i) { return i < v.size() ? v[i] : 0; }

void trim(Vec& v) {
  while (!v.empty() && v.back() == 0) v.pop_back();
}

/// All variables (program: 0..; logical: offset) mentioned by a list of constraints.
std::size_t width(const Assn& p, bool logical) {
  std::size_t n = 0;
  for (const Lin& e : p) n = std::max(n, logical ? e.lv.size() : e.sv.size());
  return n;
}

z3::expr linExpr(z3::context& ctx, const Vec& v, const char* pfx) {
  z3::expr acc = ctx.real_val(0);
  for (std::size_t i = 0; i < v.size(); ++i)
    if (v[i] != 0)
      acc = acc + ctx.real_val(static_cast<int64_t>(v[i])) *
                      ctx.real_const((std::string(pfx) + std::to_string(i)).c_str());
  return acc;
}

z3::expr eval(z3::context& ctx, const Lin& e) {
  return linExpr(ctx, e.sv, "x") + linExpr(ctx, e.lv, "g") +
         ctx.real_val(static_cast<int64_t>(e.c));
}

bool rational(const z3::expr& v, std::int64_t& num, std::int64_t& den) {
  if (!v.is_numeral()) return false;
  if (v.is_int()) {
    den = 1;
    return v.is_numeral_i64(num);
  }
  return v.numerator().is_numeral_i64(num) && v.denominator().is_numeral_i64(den);
}

bool checkedMul(std::int64_t a, std::int64_t b, std::int64_t& r) {
  return !__builtin_mul_overflow(a, b, &r);
}

}  // namespace

// --- the checker's vector operations ------------------------------------------

Vec vadd(const Vec& a, const Vec& b) {
  Vec r(std::max(a.size(), b.size()), 0);
  for (std::size_t i = 0; i < r.size(); ++i) r[i] = at(a, i) + at(b, i);
  return r;
}

Vec vsmul(std::int64_t k, const Vec& a) {
  Vec r(a.size());
  for (std::size_t i = 0; i < a.size(); ++i) r[i] = k * a[i];
  return r;
}

Vec unitVec(std::size_t i) {
  Vec r(i + 1, 0);
  r[i] = 1;
  return r;
}

std::int64_t coeff(const Vec& a, std::size_t i) { return at(a, i); }

Lin toLin(const PExp& g) { return Lin{g.sv, {}, g.c}; }

Lin negLin(const PExp& g) { return Lin{vsmul(-1, g.sv), {}, 1 - g.c}; }

Lin subst(const Lin& e, std::size_t x, const PExp& a) {
  std::int64_t k = coeff(e.sv, x);
  return Lin{vadd(e.sv, vsmul(k, vadd(a.sv, vsmul(-1, unitVec(x))))), e.lv, e.c + k * a.c};
}

Lin ghost(const PExp& pot, std::size_t j, std::int64_t extra) {
  return Lin{pot.sv, vsmul(-1, unitVec(j)), pot.c + extra};
}

Lin ghostMul(const PExp& pot, std::size_t j, std::uint64_t b) {
  return Lin{vsmul(static_cast<std::int64_t>(b), pot.sv), vsmul(-1, unitVec(j)),
             static_cast<std::int64_t>(b) * pot.c};
}

Lin growEntry(const PExp& pot) { return Lin{vsmul(-1, pot.sv), {}, 1 - pot.c}; }

Lin ghostLow(const PExp& pot, std::size_t j) { return Lin{vsmul(-1, pot.sv), unitVec(j), -pot.c}; }

Lin ghostGrow(const PExp& pot, std::size_t j, std::uint64_t b) {
  return Lin{vsmul(-1, pot.sv), vsmul(static_cast<std::int64_t>(b), unitVec(j)), -pot.c};
}

std::uint64_t ilog(std::uint64_t b, std::uint64_t n) {
  std::uint64_t r = 0;
  while (b > 1 && n >= b) {
    n /= b;
    ++r;
  }
  return r;
}

std::uint64_t logIters(std::uint64_t b, std::int64_t k) {
  return k <= 0 ? 0 : ilog(b, static_cast<std::uint64_t>(k)) + 1;
}

bool SB::constant() const {
  return std::all_of(co.begin(), co.end(), [](std::uint64_t x) { return x == 0; });
}
bool SB::operator==(const SB& o) const {
  if (c != o.c) return false;
  for (std::size_t i = 0; i < std::max(co.size(), o.co.size()); ++i)
    if ((i < co.size() ? co[i] : 0) != (i < o.co.size() ? o.co[i] : 0)) return false;
  return true;
}
SB operator+(const SB& a, const SB& b) {
  SB r(a.c + b.c);
  r.co.resize(std::max(a.co.size(), b.co.size()), 0);
  for (std::size_t i = 0; i < a.co.size(); ++i) r.co[i] += a.co[i];
  for (std::size_t i = 0; i < b.co.size(); ++i) r.co[i] += b.co[i];
  return r;
}
SB smax(const SB& a, const SB& b) {
  SB r(std::max(a.c, b.c));
  r.co.resize(std::max(a.co.size(), b.co.size()), 0);
  for (std::size_t i = 0; i < r.co.size(); ++i)
    r.co[i] = std::max(i < a.co.size() ? a.co[i] : 0, i < b.co.size() ? b.co[i] : 0);
  return r;
}
SB scale(std::uint64_t k, const SB& a) {
  SB r(k * a.c);
  for (std::uint64_t x : a.co) r.co.push_back(k * x);
  return r;
}
bool sbLe(const SB& a, const SB& b) {
  if (a.c > b.c) return false;
  for (std::size_t i = 0; i < a.co.size(); ++i)
    if (a.co[i] > (i < b.co.size() ? b.co[i] : 0)) return false;
  return true;
}
std::uint64_t sbAt(const SB& a, const std::vector<std::uint64_t>& v) {
  std::uint64_t r = a.c;
  for (std::size_t i = 0; i < a.co.size(); ++i) r += a.co[i] * (i < v.size() ? v[i] : 0);
  return r;
}
std::string sbString(const SB& a, const std::vector<std::string>& names) {
  std::string s;
  for (std::size_t i = 0; i < a.co.size(); ++i) {
    if (!a.co[i]) continue;
    std::string g = i < names.size() ? names[i] : "g" + std::to_string(i);
    s += (s.empty() ? "" : " + ") + (a.co[i] == 1 ? "" : std::to_string(a.co[i]) + "*") + "max(0," + g + ")";
  }
  if (a.c || s.empty()) s = std::to_string(a.c) + (s.empty() ? "" : " + " + s);
  return s;
}

SB whileBound(std::int64_t k, std::uint64_t d, std::uint64_t w, const SB& wb) {
  // Lean: `(k / d).toNat` with Euclidean division; for d > 0 this is floor(k/d), then max 0.
  std::int64_t q = k >= 0 ? k / static_cast<std::int64_t>(d)
                          : -((-k + static_cast<std::int64_t>(d) - 1) / static_cast<std::int64_t>(d));
  std::uint64_t n = q > 0 ? static_cast<std::uint64_t>(q) : 0;
  return scale(n, SB(w) + wb) + SB(w);
}

std::optional<std::uint64_t> triBound(std::int64_t k, std::uint64_t d, std::uint64_t w,
                                      std::uint64_t a, std::uint64_t c) {
  // Lean `triBound2 w d a c k / 2` (the doubled value is even), with N = (k / d).toNat.
  std::int64_t q = k >= 0 ? k / static_cast<std::int64_t>(d)
                          : -((-k + static_cast<std::int64_t>(d) - 1) / static_cast<std::int64_t>(d));
  __int128 N = q > 0 ? q : 0;
  __int128 t2 = 2 * ((N + 1) * static_cast<__int128>(w) + N * static_cast<__int128>(a)) +
                static_cast<__int128>(c) * (2 * N * k - static_cast<__int128>(d) * N * (N - 1));
  if (t2 < 0 || t2 / 2 > static_cast<__int128>(std::numeric_limits<std::int64_t>::max())) return std::nullopt;
  return static_cast<std::uint64_t>(t2 / 2);
}

SB whileBoundSym(std::int64_t k, const std::vector<std::uint64_t>& kl, std::uint64_t d,
                 std::uint64_t w, std::uint64_t wb) {
  auto ceilDiv = [](std::int64_t a, std::int64_t b) { return a >= 0 ? (a + b - 1) / b : -((-a) / b); };
  std::int64_t W = static_cast<std::int64_t>(w + wb), D = static_cast<std::int64_t>(d);
  SB r(w + static_cast<std::uint64_t>(std::max<std::int64_t>(0, ceilDiv(W * k, D))));
  for (std::uint64_t x : kl) r.co.push_back(static_cast<std::uint64_t>(ceilDiv(W * static_cast<std::int64_t>(x), D)));
  return r;
}

std::optional<std::pair<std::int64_t, std::vector<std::uint64_t>>>
symbolicUpper(const Assn& p, const PExp& e, std::size_t t, std::size_t gammas, std::size_t lo) {
  Assn q = p;
  Lin up{vadd(e.sv, vsmul(-1, unitVec(t))), {}, e.c};    // e - t <= 0
  Lin down{vadd(vsmul(-1, e.sv), unitVec(t)), {}, -e.c};  // t - e <= 0
  q.push_back(up);
  q.push_back(down);
  std::size_t nv = 0;
  for (const Lin& l : q) nv = std::max(nv, l.sv.size());
  for (std::size_t x = 0; x < nv; ++x)
    if (x != t && mentions(q, x)) q = eliminate(q, x);
  std::optional<std::pair<std::int64_t, std::vector<std::uint64_t>>> best;
  for (const Lin& l : q) {
    std::int64_t a = coeff(l.sv, t);
    if (a <= 0) continue;
    bool other = false;
    for (std::size_t x = 0; x < l.sv.size(); ++x)
      if (x != t && l.sv[x] != 0) other = true;
    if (other) continue;
    // a*t + sum b_j g_j + c <= 0, i.e. t <= (-c - sum b_j g_j) / a, with every b_j <= 0.
    if (-l.c % a != 0) continue;
    std::vector<std::uint64_t> kl;
    bool ok = true;
    for (std::size_t g = 0; g < l.lv.size(); ++g) {
      std::int64_t b = l.lv[g];
      if (b != 0 && (g >= gammas || g < lo)) { ok = false; break; }
      if (b > 0 || (-b) % a != 0) { ok = false; break; }
      kl.push_back(static_cast<std::uint64_t>(-b / a));
    }
    if (!ok) continue;
    while (!kl.empty() && kl.back() == 0) kl.pop_back();
    if (kl.empty()) continue;  // a constant bound: upperBound finds the best one
    std::int64_t k = -l.c / a;
    // Prefer bounds with fewer symbolic terms, then smaller constants.
    auto key = [](const std::pair<std::int64_t, std::vector<std::uint64_t>>& b) {
      std::uint64_t s = 0;
      for (std::uint64_t x : b.second) s += x;
      return std::make_pair(s, b.first);
    };
    std::pair<std::int64_t, std::vector<std::uint64_t>> cand{k, kl};
    if (!best || key(cand) < key(*best)) best = cand;
  }
  return best;
}

std::int64_t symbolicScale(const Assn& p, const PExp& e, std::size_t t, std::size_t gammas) {
  Assn q = p;
  q.push_back(Lin{vadd(e.sv, vsmul(-1, unitVec(t))), {}, e.c});
  q.push_back(Lin{vadd(vsmul(-1, e.sv), unitVec(t)), {}, -e.c});
  std::size_t nv = 0;
  for (const Lin& l : q) nv = std::max(nv, l.sv.size());
  for (std::size_t x = 0; x < nv; ++x)
    if (x != t && mentions(q, x)) q = eliminate(q, x);
  std::int64_t best = 0;
  for (const Lin& l : q) {
    std::int64_t a = coeff(l.sv, t);
    if (a <= 1) continue;
    bool ok = true, sym = false;
    for (std::size_t x = 0; x < l.sv.size(); ++x)
      if (x != t && l.sv[x] != 0) ok = false;
    for (std::size_t g = 0; g < l.lv.size(); ++g) {
      if (l.lv[g] != 0 && g >= gammas) ok = false;
      if (l.lv[g] > 0) ok = false;
      if (l.lv[g] < 0) sym = true;
    }
    if (ok && sym && (!best || a < best)) best = a;
  }
  return best;
}

std::vector<std::size_t> writes(const Node& n, const std::vector<std::vector<std::size_t>>& mods) {
  std::vector<std::size_t> out;
  std::function<void(const Node&)> go = [&](const Node& m) {
    switch (m.kind) {
      case Node::Assign:
      case Node::Havoc:
      case Node::HavocC: out.push_back(m.x); break;
      case Node::Seq:
      case Node::Ite: go(*m.c1); go(*m.c2); break;
      case Node::While:
      case Node::WhileAnd:
      case Node::WhileLog:
      case Node::WhileGrow:
      case Node::Weaken:
      case Node::Dead: go(*m.c1); break;
      case Node::Call:
        if (m.f < mods.size()) out.insert(out.end(), mods[m.f].begin(), mods[m.f].end());
        break;
      case Node::Skip: break;
    }
  };
  go(n);
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

// --- reasoning -------------------------------------------------------------------

bool feasible(const Assn& p) {
  try {
    z3::context ctx;
    z3::solver s(ctx);
    z3::params prm(ctx);
    prm.set("timeout", kTimeoutMs);
    s.set(prm);
    for (const Lin& e : p) s.add(eval(ctx, e) <= 0);
    return s.check() != z3::unsat;
  } catch (const z3::exception&) {
    return true;
  }
}

std::optional<Farkas> farkas(const Assn& p, const Lin& g) {
  // Fast paths: the goal is a premise, or a trivially true constant.
  for (std::size_t i = 0; i < p.size(); ++i)
    if (p[i] == g || (p[i].c == g.c && [&] {
          Vec a = p[i].sv, b = g.sv, c = p[i].lv, d = g.lv;
          trim(a), trim(b), trim(c), trim(d);
          return a == b && c == d;
        }())) {
      Farkas f;
      f.lam.assign(p.size(), 0);
      f.lam[i] = 1;
      return f;
    }
  {
    Vec a = g.sv, b = g.lv;
    trim(a), trim(b);
    if (a.empty() && b.empty() && g.c <= 0) {
      Farkas f;
      f.lam.assign(p.size(), 0);
      return f;
    }
  }
  try {
    // Find rational lam >= 0 with  g - sum lam_i p_i  = constant <= 0.
    z3::context ctx;
    z3::solver s(ctx);
    z3::params prm(ctx);
    prm.set("timeout", kTimeoutMs);
    s.set(prm);
    std::vector<z3::expr> lam;
    for (std::size_t i = 0; i < p.size(); ++i) {
      lam.push_back(ctx.real_const(("l" + std::to_string(i)).c_str()));
      s.add(lam.back() >= 0);
    }
    std::size_t nsv = std::max(width(p, false), g.sv.size());
    std::size_t nlv = std::max(width(p, true), g.lv.size());
    for (int part = 0; part < 2; ++part)
      for (std::size_t v = 0; v < (part == 0 ? nsv : nlv); ++v) {
        z3::expr sum = ctx.real_val(0);
        for (std::size_t i = 0; i < p.size(); ++i) {
          std::int64_t c = at(part == 0 ? p[i].sv : p[i].lv, v);
          if (c != 0) sum = sum + lam[i] * ctx.real_val(static_cast<int64_t>(c));
        }
        s.add(sum == ctx.real_val(static_cast<int64_t>(at(part == 0 ? g.sv : g.lv, v))));
      }
    z3::expr q = ctx.real_val(0);
    for (std::size_t i = 0; i < p.size(); ++i)
      if (p[i].c != 0) q = q + lam[i] * ctx.real_val(static_cast<int64_t>(p[i].c));
    s.add(ctx.real_val(static_cast<int64_t>(g.c)) - q <= 0);
    if (s.check() != z3::sat) return std::nullopt;
    z3::model m = s.get_model();
    std::vector<std::int64_t> num(p.size()), den(p.size());
    std::int64_t l = 1;
    for (std::size_t i = 0; i < p.size(); ++i) {
      z3::expr v = m.eval(lam[i], true);
      if (!rational(v, num[i], den[i]) || den[i] <= 0 || num[i] < 0) return std::nullopt;
      std::int64_t gcd = std::gcd(l, den[i]);
      if (!checkedMul(l / gcd, den[i], l)) return std::nullopt;
    }
    Farkas f;
    f.mu = static_cast<std::uint64_t>(l);
    for (std::size_t i = 0; i < p.size(); ++i) {
      std::int64_t li;
      if (!checkedMul(num[i], l / den[i], li)) return std::nullopt;
      f.lam.push_back(static_cast<std::uint64_t>(li));
    }
    // Re-check the integer identity (the checker will too).
    for (int part = 0; part < 2; ++part)
      for (std::size_t v = 0; v < (part == 0 ? nsv : nlv); ++v) {
        __int128 sum = 0;
        for (std::size_t i = 0; i < p.size(); ++i)
          sum += static_cast<__int128>(f.lam[i]) * at(part == 0 ? p[i].sv : p[i].lv, v);
        if (sum != static_cast<__int128>(f.mu) * at(part == 0 ? g.sv : g.lv, v)) return std::nullopt;
      }
    __int128 cq = 0;
    for (std::size_t i = 0; i < p.size(); ++i) cq += static_cast<__int128>(f.lam[i]) * p[i].c;
    if (static_cast<__int128>(f.mu) * g.c - cq > 0) return std::nullopt;
    return f;
  } catch (const z3::exception&) {
    return std::nullopt;
  }
}

std::optional<std::vector<Farkas>> farkasAll(const Assn& p, const Assn& goals) {
  std::vector<Farkas> out;
  for (const Lin& g : goals) {
    std::optional<Farkas> f = farkas(p, g);
    if (!f) return std::nullopt;
    out.push_back(*f);
  }
  return out;
}

std::optional<std::int64_t> upperBound(const Assn& p, const PExp& e) {
  try {
    z3::context ctx;
    z3::optimize o(ctx);
    z3::params prm(ctx);
    prm.set("timeout", kTimeoutMs);
    o.set(prm);
    for (const Lin& c : p) o.add(eval(ctx, c) <= 0);
    z3::expr t = linExpr(ctx, e.sv, "x") + ctx.real_val(static_cast<int64_t>(e.c));
    z3::optimize::handle h = o.maximize(t);
    if (o.check() != z3::sat) return std::nullopt;
    z3::expr v = o.upper(h);
    std::int64_t num, den;
    if (!rational(v, num, den) || den <= 0) return std::nullopt;
    std::int64_t k = num / den;
    if (num % den != 0 && num > 0) ++k;  // ceiling
    return k;
  } catch (const z3::exception&) {
    return std::nullopt;
  }
}

Assn normalize(const Assn& p) {
  Assn out;
  for (Lin e : p) {
    trim(e.sv), trim(e.lv);
    std::int64_t g = 0;
    for (std::int64_t c : e.sv) g = std::gcd(g, c < 0 ? -c : c);
    for (std::int64_t c : e.lv) g = std::gcd(g, c < 0 ? -c : c);
    if (g == 0) {
      if (e.c <= 0) continue;  // trivially true
      out = {Lin{{}, {}, 1}};  // contradiction
      return out;
    }
    // Divide by the gcd only when the constant is divisible too: integer tightening
    // would not be justified by the (rational) Farkas certificates of the checker.
    if (g > 1 && e.c % g == 0) {
      for (auto& c : e.sv) c /= g;
      for (auto& c : e.lv) c /= g;
      e.c /= g;
    }
    if (std::find(out.begin(), out.end(), e) == out.end()) out.push_back(e);
  }
  return out;
}

bool mentions(const Assn& p, std::size_t x) {
  for (const Lin& e : p)
    if (at(e.sv, x) != 0) return true;
  return false;
}

Assn eliminate(const Assn& p, std::size_t x) {
  Assn keep, pos, neg;
  for (const Lin& e : p) {
    std::int64_t c = at(e.sv, x);
    (c > 0 ? pos : c < 0 ? neg : keep).push_back(e);
  }
  // cb * a + ca * b, dropped if a product or a sum overflows (dropping only weakens).
  auto combine = [](std::int64_t ka, const Vec& va, std::int64_t kb, const Vec& vb, Vec& out) {
    out.assign(std::max(va.size(), vb.size()), 0);
    for (std::size_t i = 0; i < out.size(); ++i) {
      std::int64_t p, q;
      if (__builtin_mul_overflow(ka, at(va, i), &p) || __builtin_mul_overflow(kb, at(vb, i), &q) ||
          __builtin_add_overflow(p, q, &out[i]))
        return false;
    }
    return true;
  };
  for (const Lin& a : pos)
    for (const Lin& b : neg) {
      std::int64_t ca = at(a.sv, x), cb = -at(b.sv, x);
      Lin r;
      std::int64_t p, q;
      if (!combine(cb, a.sv, ca, b.sv, r.sv) || !combine(cb, a.lv, ca, b.lv, r.lv) ||
          __builtin_mul_overflow(cb, a.c, &p) || __builtin_mul_overflow(ca, b.c, &q) ||
          __builtin_add_overflow(p, q, &r.c))
        continue;
      if (x < r.sv.size()) r.sv[x] = 0;
      keep.push_back(r);
    }
  keep = normalize(keep);
  if (keep.size() > kMaxConstraints) keep.resize(kMaxConstraints);
  return keep;
}

// --- JSON --------------------------------------------------------------------------

namespace {

std::string vec(const Vec& v) {
  std::string s = "[";
  for (std::size_t i = 0; i < v.size(); ++i) s += (i ? "," : "") + std::to_string(v[i]);
  return s + "]";
}
std::string uvec(const std::vector<std::uint64_t>& v) {
  std::string s = "[";
  for (std::size_t i = 0; i < v.size(); ++i) s += (i ? "," : "") + std::to_string(v[i]);
  return s + "]";
}
std::string pexp(const PExp& e) { return "{\"sv\":" + vec(e.sv) + ",\"c\":" + std::to_string(e.c) + "}"; }
std::string lin(const Lin& e) {
  return "{\"sv\":" + vec(e.sv) + ",\"lv\":" + vec(e.lv) + ",\"c\":" + std::to_string(e.c) + "}";
}
std::string assn(const Assn& a) {
  std::string s = "[";
  for (std::size_t i = 0; i < a.size(); ++i) s += (i ? "," : "") + lin(a[i]);
  return s + "]";
}
std::string fk(const Farkas& f) { return "{\"mu\":" + std::to_string(f.mu) + ",\"lam\":" + uvec(f.lam) + "}"; }
std::string fks(const std::vector<Farkas>& v) {
  std::string s = "[";
  for (std::size_t i = 0; i < v.size(); ++i) s += (i ? "," : "") + fk(v[i]);
  return s + "]";
}
std::string str(const std::string& t) {
  std::string s = "\"";
  for (char c : t) {
    if (c == '"' || c == '\\') s += '\\';
    if (static_cast<unsigned char>(c) < 0x20) continue;
    s += c;
  }
  return s + "\"";
}
std::string u(std::uint64_t n) { return std::to_string(n); }
std::string sb(const SB& b) {
  if (b.constant()) return u(b.c);
  std::vector<std::uint64_t> co = b.co;
  while (!co.empty() && co.back() == 0) co.pop_back();
  return "{\"c\":" + u(b.c) + ",\"co\":" + uvec(co) + "}";
}
std::string klField(const std::vector<std::uint64_t>& kl) {
  bool any = std::any_of(kl.begin(), kl.end(), [](std::uint64_t x) { return x != 0; });
  return any ? ",\"kl\":" + uvec(kl) : "";
}

std::string node(const Node& n) {
  switch (n.kind) {
    case Node::Skip: return "{\"node\":\"skip\"}";
    case Node::Assign:
      return "{\"node\":\"assign\",\"w\":" + u(n.w) + ",\"x\":" + u(n.x) + ",\"a\":" + pexp(n.a) + "}";
    case Node::Havoc: return "{\"node\":\"havoc\",\"w\":" + u(n.w) + ",\"x\":" + u(n.x) + "}";
    case Node::HavocC: {
      std::string cs = "[";
      for (std::size_t i = 0; i < n.gs.size(); ++i) cs += (i ? "," : "") + pexp(n.gs[i]);
      return "{\"node\":\"havocC\",\"w\":" + u(n.w) + ",\"x\":" + u(n.x) + ",\"cs\":" + cs + "]}";
    }
    case Node::Seq:
      return "{\"node\":\"seq\",\"c1\":" + node(*n.c1) + ",\"mid\":" + assn(n.mid) + ",\"B1\":" +
             sb(n.b1) + ",\"B2\":" + sb(n.b2) + ",\"c2\":" + node(*n.c2) + "}";
    case Node::Ite:
      return "{\"node\":\"ite\",\"w\":" + u(n.w) + ",\"g\":" + pexp(n.a) + ",\"B1\":" + sb(n.b1) +
             ",\"B2\":" + sb(n.b2) + ",\"c1\":" + node(*n.c1) + ",\"c2\":" + node(*n.c2) + "}";
    case Node::While:
      return "{\"node\":\"while\",\"w\":" + u(n.w) + ",\"g\":" + pexp(n.a) + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"d\":" + u(n.d) + ",\"k\":" + std::to_string(n.k) +
             klField(n.kl) + ",\"j\":" + u(n.j) + ",\"posCert\":" + fk(n.posCert) + ",\"Wb\":" + sb(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    case Node::WhileAnd: {
      std::string g = "[";
      for (std::size_t i = 0; i < n.gs.size(); ++i) g += (i ? "," : "") + pexp(n.gs[i]);
      g += "]";
      return "{\"node\":\"whileAnd\",\"w\":" + u(n.w) + ",\"gs\":" + g + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"d\":" + u(n.d) + ",\"k\":" + std::to_string(n.k) +
             klField(n.kl) + ",\"j\":" + u(n.j) + ",\"posCert\":" + fk(n.posCert) + ",\"Wb\":" + sb(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    }
    case Node::WhileLog: {
      std::string g = "[";
      for (std::size_t i = 0; i < n.gs.size(); ++i) g += (i ? "," : "") + pexp(n.gs[i]);
      g += "]";
      return "{\"node\":\"whileLog\",\"w\":" + u(n.w) + ",\"gs\":" + g + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"b\":" + u(n.d) + ",\"k\":" + std::to_string(n.k) +
             ",\"j\":" + u(n.j) + ",\"posCert\":" + fk(n.posCert) + ",\"Wb\":" + sb(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    }
    case Node::WhileGrow: {
      std::string g = "[";
      for (std::size_t i = 0; i < n.gs.size(); ++i) g += (i ? "," : "") + pexp(n.gs[i]);
      g += "]";
      return "{\"node\":\"whileGrow\",\"w\":" + u(n.w) + ",\"gs\":" + g + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"b\":" + u(n.d) + ",\"K\":" + std::to_string(n.k) +
             ",\"j\":" + u(n.j) + ",\"capCert\":" + fk(n.posCert) + ",\"Wb\":" + sb(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    }
    case Node::Weaken:
      return "{\"node\":\"weaken\",\"P\":" + assn(n.pre) + ",\"preCerts\":" + fks(n.preCerts) +
             ",\"B\":" + sb(n.bound) + ",\"Q\":" + assn(n.post) + ",\"postCerts\":" + fks(n.postCerts) +
             ",\"c\":" + node(*n.c1) + "}";
    case Node::Dead: return "{\"node\":\"dead\",\"cert\":" + fk(n.deadCert) + ",\"c\":" + node(*n.c1) + "}";
    case Node::Call: {
      std::string in = "[", ub = "[";
      for (std::size_t i = 0; i < n.inst.size(); ++i) in += (i ? "," : "") + pexp(n.inst[i]);
      for (std::size_t i = 0; i < n.ubs.size(); ++i) ub += (i ? "," : "") + sb(n.ubs[i]);
      return "{\"node\":\"call\",\"w\":" + u(n.w) + ",\"f\":" + u(n.f) + ",\"inst\":" + in +
             "],\"preCerts\":" + fks(n.preCerts) + ",\"ubs\":" + ub + "],\"ubCerts\":" +
             fks(n.postCerts) + "}";
    }
  }
  return "{}";
}

}  // namespace

std::string responseJson(const std::string& task,
                         const std::vector<std::tuple<std::string, std::uint64_t, std::uint64_t>>& handlers,
                         std::uint64_t R) {
  std::string hs = "[";
  for (std::size_t i = 0; i < handlers.size(); ++i)
    hs += std::string(i ? "," : "") + "{\"function\":" + str(std::get<0>(handlers[i])) +
          ",\"min_interarrival\":" + std::to_string(std::get<1>(handlers[i])) +
          ",\"overhead\":" + std::to_string(std::get<2>(handlers[i])) + "}";
  return "{\"name\":" + str(task + " under interrupts") + ",\"task\":" + str(task) +
         ",\"handlers\":" + hs + "],\"R\":" + std::to_string(R) + "}";
}

std::optional<std::uint64_t> responseTime(std::uint64_t C,
                                          const std::vector<std::pair<std::uint64_t, std::uint64_t>>& handlers,
                                          std::uint64_t limit) {
  for (const auto& [c, T] : handlers)
    if (T == 0) return std::nullopt;
  std::uint64_t R = C;
  for (int fuel = 0; fuel < 100000; ++fuel) {
    unsigned __int128 next = C;
    for (const auto& [c, T] : handlers) next += (unsigned __int128)c * ((R + T - 1) / T);
    if (next > limit) return std::nullopt;
    if (next == R) return R;
    R = static_cast<std::uint64_t>(next);
  }
  return std::nullopt;
}

std::string programJson(const std::string& name, const std::vector<std::string>& variables,
                        const std::vector<FunJson>& functions,
                        const std::vector<std::string>& responses) {
  std::string vs = "[";
  for (std::size_t i = 0; i < variables.size(); ++i) vs += (i ? "," : "") + str(variables[i]);
  vs += "]";
  std::string fs = "[";
  for (std::size_t i = 0; i < functions.size(); ++i) {
    const FunJson& f = functions[i];
    std::vector<std::uint64_t> mods(f.mods.begin(), f.mods.end());
    fs += std::string(i ? ",\n" : "\n") + "{\"name\":" + str(f.name) + ",\"pre\":" + assn(f.pre) +
          ",\"bound\":" + sb(f.bound) + ",\"post\":" + assn(f.post) + ",\"mods\":" + uvec(mods) +
          (f.body ? ",\"body\":" + node(*f.body) : std::string(",\"contract\":true")) +
          (f.source ? ",\"jsource\":" + *f.source : std::string()) +
          (f.sourceRefused.empty() ? std::string() : ",\"source_refused\":" + str(f.sourceRefused)) + "}";
  }
  std::string rs;
  if (!responses.empty()) {
    rs = ",\"responses\":[";
    for (std::size_t i = 0; i < responses.size(); ++i) rs += (i ? "," : "") + responses[i];
    rs += "]";
  }
  return "{\"name\":" + str(name) + ",\"variables\":" + vs + ",\"functions\":" + fs + "]" + rs + "}";
}

std::string fileJson(const std::vector<std::string>& programs) {
  std::string s = "{\"format\":\"crosscheck-certificates\",\"version\":2,\"programs\":[\n";
  for (std::size_t i = 0; i < programs.size(); ++i) s += (i ? ",\n" : "") + programs[i];
  return s + "\n]}\n";
}

}  // namespace crosscheck::cert
