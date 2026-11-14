// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Cost certificates in the format checked by the verified Lean checker
// (formalization/ImperativeOptimization/CheckerCore.lean, soundness theorem
// `Checker.check_sound`; format: docs/certificate-format.md).
//
// Everything is dense integer data, exactly as in Lean: a constraint `Lin` is
// `sum sv[i]*x_i + sum lv[j]*gamma_j + c <= 0` over program variables `x_i` and
// logical variables `gamma_j`. Where the checker compares lists syntactically
// (assignments, loop pre/postconditions), this file reproduces the checker's own
// vector operations (`vadd`, `vsmul`, `unit`, `Lin.subst`, `toLin`, `negLin`,
// `ghost`) so that the lists coincide element by element, trailing zeros included.
//
// Nothing here needs to be trusted: a certificate that is wrong is rejected by
// the checker. This layer is independent of Clang.
#ifndef CROSSCHECK_CORE_CERT_HPP
#define CROSSCHECK_CORE_CERT_HPP

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace crosscheck::cert {

using Vec = std::vector<std::int64_t>;

/// `sum sv[i]*x_i + c` (Lean `PExp`).
struct PExp {
  Vec sv;
  std::int64_t c = 0;
};

/// `sum sv[i]*x_i + sum lv[j]*gamma_j + c <= 0` (Lean `Lin`).
struct Lin {
  Vec sv, lv;
  std::int64_t c = 0;
  bool operator==(const Lin& o) const { return sv == o.sv && lv == o.lv && c == o.c; }
};

using Assn = std::vector<Lin>;

/// Farkas certificate `(mu, lam)` for `premises |- goal` (Lean `entails1`).
struct Farkas {
  std::uint64_t mu = 1;
  std::vector<std::uint64_t> lam;
};

// --- the checker's vector operations, reproduced exactly ---------------------
Vec vadd(const Vec& a, const Vec& b);
Vec vsmul(std::int64_t k, const Vec& a);
Vec unitVec(std::size_t i);
std::int64_t coeff(const Vec& a, std::size_t i);
Lin toLin(const PExp& g);      ///< the test `g <= 0` as a constraint
Lin negLin(const PExp& g);     ///< its negation over the integers: `1 - g <= 0`
Lin subst(const Lin& e, std::size_t x, const PExp& a);  ///< `e[a/x]`
Lin ghost(const PExp& pot, std::size_t j, std::int64_t extra);  ///< `pot - gamma_j + extra <= 0`

// --- reasoning (rational; results are checked by the Lean checker) -----------
/// Is the conjunction satisfiable over the rationals? "Unknown" counts as yes.
bool feasible(const Assn& p);
/// Integer Farkas multipliers for `p |- g`, if `g` follows rationally from `p`.
std::optional<Farkas> farkas(const Assn& p, const Lin& g);
/// One certificate per goal, or nothing if one goal does not follow.
std::optional<std::vector<Farkas>> farkasAll(const Assn& p, const Assn& goals);
/// The least integer `k` with `p |- e - k <= 0` (rational maximum, rounded up),
/// for `e` over program variables only. No value if `e` is unbounded.
std::optional<std::int64_t> upperBound(const Assn& p, const PExp& e);
/// Fourier-Motzkin elimination of the program variable `x` (exact over the
/// rationals; the result is capped in size, which only weakens it).
Assn eliminate(const Assn& p, std::size_t x);
/// Removes trivial and duplicate constraints, divides by the gcd, trims zeros.
Assn normalize(const Assn& p);
/// Is `x` mentioned (with a non-zero coefficient) by a constraint of `p`?
bool mentions(const Assn& p, std::size_t x);

// --- certificates --------------------------------------------------------------
struct Node;
using NodeP = std::shared_ptr<const Node>;

/// A node of the Lean type `ACmd`.
struct Node {
  enum Kind { Skip, Assign, Havoc, Seq, Ite, While, WhileAnd, Weaken, Dead } kind = Skip;
  std::uint64_t w = 0;          // Assign, Havoc, Ite, While
  std::size_t x = 0;            // Assign, Havoc
  PExp a;                       // Assign: expression; Ite, While: test `g <= 0`
  std::vector<PExp> gs;         // WhileAnd: the conjuncts of the test
  Assn mid;                     // Seq
  std::uint64_t b1 = 0, b2 = 0; // Seq, Ite: bounds of the parts; While: Wb in b1
  Assn inv;                     // While
  PExp pot;                     // While
  std::uint64_t d = 1;          // While
  std::int64_t k = 0;           // While
  std::size_t j = 0;            // While
  Farkas posCert;               // While
  Assn pre, post;               // Weaken: P', Q'
  std::vector<Farkas> preCerts, postCerts;  // Weaken
  std::uint64_t bound = 0;      // Weaken: B'
  Farkas deadCert;              // Dead
  NodeP c1, c2;                 // children (Seq, Ite: both; While, Weaken, Dead: c1)
};

/// The bound the checker requires of a `while` node: `floor(k/d) * (w + Wb) + w`.
std::uint64_t whileBound(std::int64_t k, std::uint64_t d, std::uint64_t w, std::uint64_t wb);

/// JSON of one certificate, in the format read by `crosscheck-check`.
std::string toJson(const std::string& function, const std::vector<std::string>& variables,
                   const Assn& pre, std::uint64_t bound, const Assn& post, const Node& program);

/// The whole file around a list of certificates produced by `toJson`.
std::string fileJson(const std::vector<std::string>& certificates);

}  // namespace crosscheck::cert

#endif
