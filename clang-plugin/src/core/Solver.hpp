// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// SMT back-end (Z3): integer entailment checks and synthesis of affine ranking
// potentials through Farkas' Lemma. Independent of Clang.
#ifndef CROSSCHECK_CORE_SOLVER_HPP
#define CROSSCHECK_CORE_SOLVER_HPP

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "LinExpr.hpp"

namespace crosscheck {

/// Is the conjunction satisfiable over the integers (together with the ranges
/// of the symbols it mentions)? "Unknown" answers count as satisfiable.
bool isFeasible(const SymbolTable& syms, const std::vector<Constraint>& facts);

/// Does `facts` imply `goal` over the integers? "Unknown" counts as "no".
bool entails(const SymbolTable& syms, const std::vector<Constraint>& facts,
             const Constraint& goal);

/// The solver work of this thread so far: for every query (answered or from the cache),
/// the number of constraints it carries plus one. A deterministic measure of the
/// analysis effort, roughly proportional to its time, used for the search budget.
std::uint64_t solverCalls();

/// A closed integer interval with optional ends.
struct Interval {
  std::optional<std::int64_t> lo, hi;
  bool unconstrained() const { return !lo && !hi; }
  bool operator==(const Interval& o) const { return lo == o.lo && hi == o.hi; }
  bool operator<(const Interval& o) const { return lo != o.lo ? lo < o.lo : hi < o.hi; }
};

/// The tightest interval that `facts` (with the symbol ranges) imply for `e`
/// over the integers, as far as Z3 finds it; every returned end is re-checked
/// with `entails`, so a returned bound always holds. No value when `facts` are
/// contradictory (the state is unreachable). "Unknown" yields a missing end.
std::optional<Interval> boundsOf(const SymbolTable& syms, const std::vector<Constraint>& facts,
                                 const LinExpr& e);

struct Rational {
  std::int64_t num = 0;
  std::int64_t den = 1;
  std::string str() const;
};

/// A ranking-potential synthesis problem.
///
/// The potential is searched in the template
///   V(x) = sum_j w_j * x_j + c0
/// where `x_j` are *slots* (values of program variables at the loop head, or of
/// the parameters of a recursive function). For each step (one path through
/// guard and body, or one recursive call site) we require, under its premises,
///   descent:     V(pre) - V(post) >= 1
///   positivity:  V(pre) >= 1
/// and, under `entryFacts`, the bound `V(entry) <= K` with `K` minimal.
/// Then the number of steps is at most `floor(K)`.
///
/// Soundness: Lean theorem `ranking_bound_floor` (module `Certificate`); the
/// Farkas encoding is justified by `farkas_sound`.
struct RankingProblem {
  struct Step {
    std::vector<LinExpr> pre;         ///< slot values before the step
    std::vector<LinExpr> post;        ///< slot values after the step
    std::vector<Constraint> premises; ///< facts that hold when the step is taken
  };
  std::size_t slots = 0;
  std::vector<LinExpr> entry;          ///< slot values on entry
  std::vector<Constraint> entryFacts;  ///< facts that hold on entry
  std::vector<Step> steps;
};

struct RankingResult {
  std::vector<Rational> weights;  ///< w_j
  Rational offset;                ///< c0
  std::uint64_t bound = 0;        ///< floor(K): maximal number of steps
  /// True when no constant bounds the potential on entry (`unbounded` synthesis): the
  /// potential still decreases and is at least 1 before a step, so the number of steps is
  /// at most its value on entry, a function of the inputs; `bound` is then meaningless.
  bool symbolic = false;
};

/// Returns no value when no affine potential with a finite bound is found.
/// With `unbounded`, the potential is not required to have a constant bound on entry;
/// the sum of the absolute values of its coefficients is minimised instead.
std::optional<RankingResult> synthesizeRanking(const SymbolTable& syms,
                                               const RankingProblem& problem, bool unbounded = false);

/// A *size potential* problem for a recursive function.
///
/// Each path through the function body performs a (possibly empty) list of
/// self-calls. We search `U(x) = sum_j w_j * x_j + c0` such that on every path,
/// under its premises,
///   U(pre) >= 1 + sum_i U(call_i)
/// (for a path without calls this reads `U(pre) >= 1`). Then the number of
/// activations started by a call with parameters `x` is at most `floor(U(x))`,
/// hence at most `floor(K)` where `U(entry) <= K` under `entryFacts`.
///
/// Soundness: Lean theorem `RTree.size_le_potential` (module `Arity`).
struct SizeProblem {
  struct Path {
    std::vector<LinExpr> pre;                 ///< parameter values of the activation
    std::vector<std::vector<LinExpr>> calls;  ///< argument values of each self-call
    std::vector<Constraint> premises;
  };
  std::size_t slots = 0;
  std::vector<LinExpr> entry;
  std::vector<Constraint> entryFacts;
  std::vector<Path> paths;
};

/// Returns no value when no affine size potential with a finite bound is found.
/// On success `bound` is the maximal number of activations.
std::optional<RankingResult> synthesizeSizePotential(const SymbolTable& syms,
                                                     const SizeProblem& problem);

}  // namespace crosscheck

#endif
