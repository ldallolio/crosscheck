// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "LinExpr.hpp"

#include <utility>

namespace crosscheck {

SymId SymbolTable::fresh(std::string name, std::optional<std::int64_t> lo,
                         std::optional<std::int64_t> hi) {
  symbols_.push_back(Symbol{std::move(name), lo, hi});
  return static_cast<SymId>(symbols_.size() - 1);
}

LinExpr LinExpr::constant(std::int64_t c) {
  LinExpr e;
  e.constant_ = c;
  return e;
}

LinExpr LinExpr::symbol(SymId s) {
  LinExpr e;
  e.terms_[s] = 1;
  return e;
}

LinExpr LinExpr::poison() {
  LinExpr e;
  e.poisoned_ = true;
  return e;
}

std::int64_t LinExpr::coefficient(SymId s) const {
  auto it = terms_.find(s);
  return it == terms_.end() ? 0 : it->second;
}

LinExpr LinExpr::operator+(const LinExpr& o) const {
  if (poisoned_ || o.poisoned_) return poison();
  LinExpr r = *this;
  if (__builtin_add_overflow(r.constant_, o.constant_, &r.constant_)) return poison();
  for (const auto& [s, c] : o.terms_) {
    std::int64_t& slot = r.terms_[s];
    if (__builtin_add_overflow(slot, c, &slot)) return poison();
    if (slot == 0) r.terms_.erase(s);
  }
  return r;
}

LinExpr LinExpr::operator-(const LinExpr& o) const { return *this + o.scaled(-1); }

LinExpr LinExpr::scaled(std::int64_t k) const {
  if (poisoned_) return poison();
  LinExpr r;
  if (k == 0) return r;
  if (__builtin_mul_overflow(constant_, k, &r.constant_)) return poison();
  for (const auto& [s, c] : terms_) {
    std::int64_t v;
    if (__builtin_mul_overflow(c, k, &v)) return poison();
    r.terms_[s] = v;
  }
  return r;
}

LinExpr LinExpr::substitute(const std::map<SymId, LinExpr>& sigma) const {
  if (poisoned_) return poison();
  LinExpr r = constant(constant_);
  for (const auto& [s, c] : terms_) {
    auto it = sigma.find(s);
    r = r + (it == sigma.end() ? symbol(s) : it->second).scaled(c);
  }
  return r;
}

bool LinExpr::operator==(const LinExpr& o) const {
  return poisoned_ == o.poisoned_ && constant_ == o.constant_ && terms_ == o.terms_;
}

std::string LinExpr::str(const SymbolTable& syms) const {
  if (poisoned_) return "<unknown>";
  std::string out;
  for (const auto& [s, c] : terms_) {
    std::int64_t a = c;
    if (out.empty()) {
      if (a < 0) out += "-";
    } else {
      out += a < 0 ? " - " : " + ";
    }
    if (a < 0) a = -a;  // INT64_MIN stays negative; harmless for printing
    if (a != 1) out += std::to_string(a) + "*";
    out += syms[s].name;
  }
  if (out.empty()) return std::to_string(constant_);
  if (constant_ > 0) out += " + " + std::to_string(constant_);
  if (constant_ < 0) out += " - " + std::to_string(-constant_);
  return out;
}

std::string Constraint::str(const SymbolTable& syms) const { return e.str(syms) + " <= 0"; }

Constraint le(const LinExpr& a, const LinExpr& b) { return Constraint{a - b}; }
Constraint lt(const LinExpr& a, const LinExpr& b) {
  return Constraint{a - b + LinExpr::constant(1)};
}
Constraint ge(const LinExpr& a, const LinExpr& b) { return le(b, a); }
Constraint gt(const LinExpr& a, const LinExpr& b) { return lt(b, a); }

}  // namespace crosscheck
