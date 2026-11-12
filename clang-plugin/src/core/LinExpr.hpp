// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Affine expressions over symbolic integer values, and linear constraints.
// This layer is independent of Clang.
#ifndef CROSSCHECK_CORE_LINEXPR_HPP
#define CROSSCHECK_CORE_LINEXPR_HPP

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace crosscheck {

using SymId = unsigned;

/// A symbolic integer value (an unknown of the extensional layer). Symbols are
/// immutable: program variables are *mapped* to expressions over symbols.
struct Symbol {
  std::string name;
  std::optional<std::int64_t> lo;  ///< inclusive lower bound, if known
  std::optional<std::int64_t> hi;  ///< inclusive upper bound, if known
};

class SymbolTable {
 public:
  SymId fresh(std::string name, std::optional<std::int64_t> lo = std::nullopt,
              std::optional<std::int64_t> hi = std::nullopt);
  const Symbol& operator[](SymId id) const { return symbols_[id]; }
  std::size_t size() const { return symbols_.size(); }

 private:
  std::vector<Symbol> symbols_;
};

/// `sum_i coef_i * sym_i + constant` with 64-bit integer coefficients.
/// Arithmetic that overflows yields a *poisoned* expression, which every
/// consumer treats as "unknown".
class LinExpr {
 public:
  LinExpr() = default;
  static LinExpr constant(std::int64_t c);
  static LinExpr symbol(SymId s);
  static LinExpr poison();

  bool poisoned() const { return poisoned_; }
  bool isConstant() const { return !poisoned_ && terms_.empty(); }
  std::int64_t constantTerm() const { return constant_; }
  const std::map<SymId, std::int64_t>& terms() const { return terms_; }
  std::int64_t coefficient(SymId s) const;

  LinExpr operator+(const LinExpr& o) const;
  LinExpr operator-(const LinExpr& o) const;
  LinExpr operator-() const { return scaled(-1); }
  LinExpr scaled(std::int64_t k) const;
  /// Replace symbols by expressions (symbols not in the map are kept).
  LinExpr substitute(const std::map<SymId, LinExpr>& sigma) const;

  bool operator==(const LinExpr& o) const;
  bool operator!=(const LinExpr& o) const { return !(*this == o); }

  std::string str(const SymbolTable& syms) const;

 private:
  std::map<SymId, std::int64_t> terms_;  // no zero coefficients
  std::int64_t constant_ = 0;
  bool poisoned_ = false;
};

/// The linear constraint `e <= 0` over the integers.
struct Constraint {
  LinExpr e;
  bool operator==(const Constraint& o) const { return e == o.e; }
  std::string str(const SymbolTable& syms) const;
};

Constraint le(const LinExpr& a, const LinExpr& b);  ///< a <= b
Constraint lt(const LinExpr& a, const LinExpr& b);  ///< a <  b  (integers)
Constraint ge(const LinExpr& a, const LinExpr& b);  ///< a >= b
Constraint gt(const LinExpr& a, const LinExpr& b);  ///< a >  b  (integers)

}  // namespace crosscheck

#endif
