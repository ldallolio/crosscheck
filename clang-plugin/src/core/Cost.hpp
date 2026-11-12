// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Saturating cost arithmetic in the tropical (max,+) style used by CrossCheck:
// sequencing adds, branching takes the maximum, iteration multiplies.
#ifndef CROSSCHECK_CORE_COST_HPP
#define CROSSCHECK_CORE_COST_HPP

#include <cstdint>
#include <string>

namespace crosscheck {

/// A natural number or "too large to represent" (saturated).
struct Sat {
  std::uint64_t v = 0;
  bool inf = false;

  static Sat of(std::uint64_t x) { return Sat{x, false}; }
  static Sat infinite() { return Sat{0, true}; }

  friend Sat operator+(Sat a, Sat b) {
    Sat r;
    if (a.inf || b.inf || __builtin_add_overflow(a.v, b.v, &r.v)) return infinite();
    return r;
  }
  friend Sat operator*(Sat a, Sat b) {
    // 0 * infinity is 0: a loop that never runs costs nothing.
    if ((!a.inf && a.v == 0) || (!b.inf && b.v == 0)) return of(0);
    Sat r;
    if (a.inf || b.inf || __builtin_mul_overflow(a.v, b.v, &r.v)) return infinite();
    return r;
  }
  friend Sat max(Sat a, Sat b) {
    if (a.inf || b.inf) return infinite();
    return of(a.v > b.v ? a.v : b.v);
  }
  friend bool operator==(Sat a, Sat b) { return a.inf == b.inf && (a.inf || a.v == b.v); }
  std::string str() const { return inf ? "unbounded" : std::to_string(v); }
};

/// Number of nodes of a tree with branching factor at most `b` and depth at
/// most `d` (a single node has depth 0): `1 + b + ... + b^d`.
/// For `b >= 2` this is `(b^(d+1) - 1) / (b - 1)`; for `b = 1` it is `d + 1`.
/// Mechanised as `RTree.size_le_geom` (Lean, module `Arity`).
inline Sat treeNodes(Sat b, Sat d) {
  if (d.inf) return (!b.inf && b.v == 0) ? Sat::of(1) : Sat::infinite();
  if (!b.inf && b.v == 0) return Sat::of(1);
  if (!b.inf && b.v == 1) return d + Sat::of(1);
  Sat total = Sat::of(1), level = Sat::of(1);
  for (std::uint64_t i = 0; i < d.v; ++i) {
    level = level * b;
    total = total + level;
    if (total.inf) return total;
  }
  return total;
}

}  // namespace crosscheck

#endif
