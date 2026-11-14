// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Cert.hpp"

#include <z3++.h>

#include <algorithm>
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

std::uint64_t whileBound(std::int64_t k, std::uint64_t d, std::uint64_t w, std::uint64_t wb) {
  // Lean: `(k / d).toNat` with Euclidean division; for d > 0 this is floor(k/d), then max 0.
  std::int64_t q = k >= 0 ? k / static_cast<std::int64_t>(d)
                          : -((-k + static_cast<std::int64_t>(d) - 1) / static_cast<std::int64_t>(d));
  std::uint64_t n = q > 0 ? static_cast<std::uint64_t>(q) : 0;
  return n * (w + wb) + w;
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

std::string node(const Node& n) {
  switch (n.kind) {
    case Node::Skip: return "{\"node\":\"skip\"}";
    case Node::Assign:
      return "{\"node\":\"assign\",\"w\":" + u(n.w) + ",\"x\":" + u(n.x) + ",\"a\":" + pexp(n.a) + "}";
    case Node::Havoc: return "{\"node\":\"havoc\",\"w\":" + u(n.w) + ",\"x\":" + u(n.x) + "}";
    case Node::Seq:
      return "{\"node\":\"seq\",\"c1\":" + node(*n.c1) + ",\"mid\":" + assn(n.mid) + ",\"B1\":" +
             u(n.b1) + ",\"B2\":" + u(n.b2) + ",\"c2\":" + node(*n.c2) + "}";
    case Node::Ite:
      return "{\"node\":\"ite\",\"w\":" + u(n.w) + ",\"g\":" + pexp(n.a) + ",\"B1\":" + u(n.b1) +
             ",\"B2\":" + u(n.b2) + ",\"c1\":" + node(*n.c1) + ",\"c2\":" + node(*n.c2) + "}";
    case Node::While:
      return "{\"node\":\"while\",\"w\":" + u(n.w) + ",\"g\":" + pexp(n.a) + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"d\":" + u(n.d) + ",\"k\":" + std::to_string(n.k) +
             ",\"j\":" + u(n.j) + ",\"posCert\":" + fk(n.posCert) + ",\"Wb\":" + u(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    case Node::WhileAnd: {
      std::string g = "[";
      for (std::size_t i = 0; i < n.gs.size(); ++i) g += (i ? "," : "") + pexp(n.gs[i]);
      g += "]";
      return "{\"node\":\"whileAnd\",\"w\":" + u(n.w) + ",\"gs\":" + g + ",\"inv\":" + assn(n.inv) +
             ",\"pot\":" + pexp(n.pot) + ",\"d\":" + u(n.d) + ",\"k\":" + std::to_string(n.k) +
             ",\"j\":" + u(n.j) + ",\"posCert\":" + fk(n.posCert) + ",\"Wb\":" + u(n.b1) +
             ",\"body\":" + node(*n.c1) + "}";
    }
    case Node::Weaken:
      return "{\"node\":\"weaken\",\"P\":" + assn(n.pre) + ",\"preCerts\":" + fks(n.preCerts) +
             ",\"B\":" + u(n.bound) + ",\"Q\":" + assn(n.post) + ",\"postCerts\":" + fks(n.postCerts) +
             ",\"c\":" + node(*n.c1) + "}";
    case Node::Dead: return "{\"node\":\"dead\",\"cert\":" + fk(n.deadCert) + ",\"c\":" + node(*n.c1) + "}";
  }
  return "{}";
}

}  // namespace

std::string toJson(const std::string& function, const std::vector<std::string>& variables,
                   const Assn& pre, std::uint64_t bound, const Assn& post, const Node& program) {
  std::string vs = "[";
  for (std::size_t i = 0; i < variables.size(); ++i) vs += (i ? "," : "") + str(variables[i]);
  vs += "]";
  return "{\"function\":" + str(function) + ",\"variables\":" + vs + ",\"pre\":" + assn(pre) +
         ",\"bound\":" + u(bound) + ",\"post\":" + assn(post) + ",\"program\":" + node(program) + "}";
}

std::string fileJson(const std::vector<std::string>& certificates) {
  std::string s = "{\"format\":\"crosscheck-certificates\",\"version\":1,\"certificates\":[\n";
  for (std::size_t i = 0; i < certificates.size(); ++i) s += (i ? ",\n" : "") + certificates[i];
  return s + "\n]}\n";
}

}  // namespace crosscheck::cert
