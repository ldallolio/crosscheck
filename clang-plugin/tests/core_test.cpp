// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include <gtest/gtest.h>

#include "core/Cost.hpp"
#include "core/LinExpr.hpp"
#include "core/Solver.hpp"

using namespace crosscheck;

namespace {

LinExpr sym(SymId s) { return LinExpr::symbol(s); }
LinExpr num(std::int64_t c) { return LinExpr::constant(c); }

TEST(LinExpr, Arithmetic) {
  SymbolTable t;
  SymId x = t.fresh("x"), y = t.fresh("y");
  LinExpr e = sym(x).scaled(2) + sym(y) - num(3);
  EXPECT_EQ(e.coefficient(x), 2);
  EXPECT_EQ(e.coefficient(y), 1);
  EXPECT_EQ(e.constantTerm(), -3);
  EXPECT_EQ((e - e), num(0));
  EXPECT_TRUE((e - e).isConstant());
  EXPECT_EQ(e.str(t), "2*x + y - 3");
}

TEST(LinExpr, OverflowPoisons) {
  SymbolTable t;
  SymId x = t.fresh("x");
  LinExpr big = sym(x).scaled(INT64_MAX);
  EXPECT_FALSE(big.poisoned());
  EXPECT_TRUE((big + big).poisoned());
  EXPECT_TRUE((num(INT64_MAX) + num(1)).poisoned());
  EXPECT_TRUE((big + big + num(1)).poisoned());
}

TEST(LinExpr, Substitute) {
  SymbolTable t;
  SymId x = t.fresh("x"), y = t.fresh("y");
  LinExpr e = sym(x).scaled(3) + num(1);
  EXPECT_EQ(e.substitute({{x, sym(y) + num(2)}}), sym(y).scaled(3) + num(7));
}

TEST(Sat, SaturatingArithmetic) {
  EXPECT_EQ((Sat::of(3) + Sat::of(4)).v, 7u);
  EXPECT_TRUE((Sat::of(UINT64_MAX) + Sat::of(1)).inf);
  EXPECT_TRUE((Sat::of(UINT64_MAX) * Sat::of(2)).inf);
  EXPECT_EQ((Sat::of(0) * Sat::infinite()).v, 0u);
  EXPECT_FALSE((Sat::of(0) * Sat::infinite()).inf);
  EXPECT_EQ(max(Sat::of(3), Sat::of(9)).v, 9u);
}

TEST(Sat, TreeNodes) {
  EXPECT_EQ(treeNodes(Sat::of(2), Sat::of(2)).v, 7u);    // 1 + 2 + 4
  EXPECT_EQ(treeNodes(Sat::of(3), Sat::of(2)).v, 13u);   // 1 + 3 + 9
  EXPECT_EQ(treeNodes(Sat::of(1), Sat::of(19)).v, 20u);  // linear recursion
  EXPECT_EQ(treeNodes(Sat::of(0), Sat::of(5)).v, 1u);
  EXPECT_TRUE(treeNodes(Sat::of(2), Sat::of(200)).inf);
}

TEST(Solver, Entailment) {
  SymbolTable t;
  SymId x = t.fresh("x", 0, 10), y = t.fresh("y");
  EXPECT_TRUE(entails(t, {}, le(sym(x), num(10))));  // from the symbol range
  EXPECT_FALSE(entails(t, {}, le(sym(x), num(9))));
  EXPECT_TRUE(entails(t, {lt(sym(y), sym(x))}, le(sym(y), num(9))));
  // Integer reasoning: 2y <= 1 and y >= 0 gives y = 0.
  EXPECT_TRUE(entails(t, {le(sym(y).scaled(2), num(1)), ge(sym(y), num(0))}, le(sym(y), num(0))));
  EXPECT_FALSE(entails(t, {}, le(LinExpr::poison(), num(0))));
}

TEST(Solver, Feasibility) {
  SymbolTable t;
  SymId x = t.fresh("x", 0, 10);
  EXPECT_TRUE(isFeasible(t, {ge(sym(x), num(5))}));
  EXPECT_FALSE(isFeasible(t, {ge(sym(x), num(11))}));
}

// for (i = 0; i < n; i += step) with 0 <= n <= N.
RankingProblem countingLoop(SymbolTable& t, std::int64_t N, std::int64_t step) {
  SymId n = t.fresh("n", 0, N), i = t.fresh("i");
  RankingProblem p;
  p.slots = 2;
  p.entry = {num(0), sym(n)};
  RankingProblem::Step s;
  s.pre = {sym(i), sym(n)};
  s.post = {sym(i) + num(step), sym(n)};
  s.premises = {ge(sym(i), num(0)), lt(sym(i), sym(n))};
  p.steps.push_back(s);
  return p;
}

TEST(Ranking, UnitStepIsExact) {
  SymbolTable t;
  auto r = synthesizeRanking(t, countingLoop(t, 100, 1));
  ASSERT_TRUE(r.has_value());
  EXPECT_EQ(r->bound, 100u);
}

TEST(Ranking, StrideGivesCeiling) {
  SymbolTable t;
  auto r = synthesizeRanking(t, countingLoop(t, 10, 4));
  ASSERT_TRUE(r.has_value());
  EXPECT_EQ(r->bound, 3u);  // ceil(10 / 4): i = 0, 4, 8
}

TEST(Ranking, NonTerminatingLoopHasNoPotential) {
  SymbolTable t;
  SymId i = t.fresh("i");
  RankingProblem p;
  p.slots = 1;
  p.entry = {num(0)};
  p.steps.push_back({{sym(i)}, {sym(i)}, {lt(sym(i), num(1))}});  // i unchanged
  EXPECT_FALSE(synthesizeRanking(t, p).has_value());
}

TEST(Ranking, UnboundedInputHasNoFiniteBound) {
  SymbolTable t;
  SymId n = t.fresh("n"), i = t.fresh("i");  // n has no range
  RankingProblem p;
  p.slots = 2;
  p.entry = {num(0), sym(n)};
  p.steps.push_back({{sym(i), sym(n)}, {sym(i) + num(1), sym(n)}, {lt(sym(i), sym(n))}});
  EXPECT_FALSE(synthesizeRanking(t, p).has_value());
}

TEST(Ranking, DeadLoopCostsNothing) {
  SymbolTable t;
  SymId i = t.fresh("i");
  RankingProblem p;
  p.slots = 1;
  p.entry = {num(0)};
  p.steps.push_back({{sym(i)}, {sym(i)}, {Constraint{num(1)}}});  // guard is false
  auto r = synthesizeRanking(t, p);
  ASSERT_TRUE(r.has_value());
  EXPECT_EQ(r->bound, 0u);
}

TEST(Ranking, TwoPathsNeedACommonPotential) {
  // while (x > 0 && y > 0) { either x--, or y-- } with x, y in [0, 5]: V = x + y.
  SymbolTable t;
  SymId x0 = t.fresh("x0", 0, 5), y0 = t.fresh("y0", 0, 5), x = t.fresh("x"), y = t.fresh("y");
  RankingProblem p;
  p.slots = 2;
  p.entry = {sym(x0), sym(y0)};
  std::vector<Constraint> guard = {gt(sym(x), num(0)), gt(sym(y), num(0))};
  p.steps.push_back({{sym(x), sym(y)}, {sym(x) - num(1), sym(y)}, guard});
  p.steps.push_back({{sym(x), sym(y)}, {sym(x), sym(y) - num(1)}, guard});
  auto r = synthesizeRanking(t, p);
  ASSERT_TRUE(r.has_value());
  EXPECT_EQ(r->bound, 9u);  // x + y - 1 at entry
}

TEST(SizePotential, BinarySplitIsLinear) {
  // f(lo, hi) with lo < hi: leaf if hi - lo <= 1, else f(lo, m) and f(m, hi), lo < m < hi.
  SymbolTable t;
  SymId lo = t.fresh("lo", 0, 100), hi = t.fresh("hi", 0, 100), m = t.fresh("m");
  SizeProblem p;
  p.slots = 2;
  p.entry = {sym(lo), sym(hi)};
  p.entryFacts = {lt(sym(lo), sym(hi))};
  std::vector<LinExpr> pre = {sym(lo), sym(hi)};
  p.paths.push_back({pre, {}, {lt(sym(lo), sym(hi)), le(sym(hi) - sym(lo), num(1))}});
  p.paths.push_back({pre,
                     {{sym(lo), sym(m)}, {sym(m), sym(hi)}},
                     {ge(sym(hi) - sym(lo), num(2)), lt(sym(lo), sym(m)), lt(sym(m), sym(hi))}});
  auto r = synthesizeSizePotential(t, p);
  ASSERT_TRUE(r.has_value());
  EXPECT_EQ(r->bound, 199u);  // 2 * (hi - lo) - 1 with hi - lo <= 100
}

TEST(SizePotential, UnboundedRecursionFails) {
  SymbolTable t;
  SymId n = t.fresh("n", 0, 10);
  SizeProblem p;
  p.slots = 1;
  p.entry = {sym(n)};
  p.paths.push_back({{sym(n)}, {{sym(n)}}, {}});  // f(n) calls f(n)
  EXPECT_FALSE(synthesizeSizePotential(t, p).has_value());
}

}  // namespace

// --- intervals ---------------------------------------------------------------

namespace {

TEST(Bounds, IntervalImpliedByFacts) {
  SymbolTable syms;
  LinExpr x = LinExpr::symbol(syms.fresh("x")), y = LinExpr::symbol(syms.fresh("y"));
  std::vector<Constraint> facts{ge(x, LinExpr::constant(2)), le(x, LinExpr::constant(5)),
                                ge(y, x), le(y, x + LinExpr::constant(3))};
  std::optional<Interval> b = boundsOf(syms, facts, y + x);
  ASSERT_TRUE(b.has_value());
  EXPECT_EQ(b->lo, std::optional<std::int64_t>(4));
  EXPECT_EQ(b->hi, std::optional<std::int64_t>(13));
}

TEST(Bounds, MissingEndsAndDeadStates) {
  SymbolTable syms;
  LinExpr x = LinExpr::symbol(syms.fresh("x"));
  std::optional<Interval> b = boundsOf(syms, {ge(x, LinExpr::constant(0))}, x);
  ASSERT_TRUE(b.has_value());
  EXPECT_EQ(b->lo, std::optional<std::int64_t>(0));
  EXPECT_FALSE(b->hi.has_value());
  // Contradictory facts: no interval at all.
  EXPECT_FALSE(boundsOf(syms, {ge(x, LinExpr::constant(1)), le(x, LinExpr::constant(0))}, x).has_value());
}

}  // namespace
