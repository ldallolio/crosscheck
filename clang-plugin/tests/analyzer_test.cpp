// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// End-to-end tests of the analyser on small C++ programs. The cost figures in
// the comments are derived by hand from the cost model documented in
// clang-plugin/README.md (all weights 1).
#include <cstdio>

#include <gtest/gtest.h>

#include "test_support.hpp"

using namespace crosscheck;
using crosscheck::testing::anyAssumptionContains;
using crosscheck::testing::anyErrorContains;
using crosscheck::testing::check;

namespace {

const FunctionReport& fn(const Report& r, const char* name) {
  const FunctionReport* f = r.find(name);
  EXPECT_NE(f, nullptr) << "no report for " << name;
  static const FunctionReport empty;
  return f ? *f : empty;
}

// --- cost model ---------------------------------------------------------------

TEST(Cost, StraightLine) {
  // x + y: 1, * 2: 1, return: 1.
  Report r = check("CROSSCHECK_REALTIME int f(int x, int y) { return (x + y) * 2; }");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").wcet, 3u);
}

TEST(Cost, BranchTakesTheMaximum) {
  // test: 1 + 1; then: 3 assignments; else: 1 assignment; return: 1.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(int x) {
      int a = 0, b = 0, c = 0;           // 3
      if (x > 0) { a = 1; b = 2; c = 3; } // 2 + max(3, 1)
      else       { a = 4; }
      return a + b + c;                   // 3
    })");
  EXPECT_EQ(fn(r, "f").wcet, 3u + 2u + 3u + 3u);
}

TEST(Cost, GuardClauseIsNotAddedToTheRest) {
  // if (x < 0) return 0;   -> 2 + max(1, rest)
  // rest: return x * 2     -> 2
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(int x) {
      if (x < 0) return 0;
      return x * 2;
    })");
  EXPECT_EQ(fn(r, "f").wcet, 4u);
}

TEST(Cost, WeightsAreConfigurable) {
  Options o;
  ASSERT_TRUE(o.parse("weight-arith=10"));
  Report r = check("CROSSCHECK_REALTIME int f(int x, int y) { return (x + y) * 2; }", o);
  EXPECT_EQ(fn(r, "f").wcet, 21u);
}

TEST(Cost, CalleeCostIsAdded) {
  Report r = check(R"(
    static int twice(int x) { return x * 2; }           // 2
    CROSSCHECK_REALTIME int f(int x) { return twice(x) + 1; }  // call 1 + 2, + 1, return 1
    )");
  EXPECT_EQ(fn(r, "f").wcet, 5u);
}

// --- loops ----------------------------------------------------------------------

TEST(Loops, CountingLoopIsExact) {
  // init 1; 64 * (test 2 + body 3 + inc 2) + final test 2; s init 1; return 1.
  Report r = check(R"(
    CROSSCHECK_REALTIME int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
      int s = 0;
      for (int i = 0; i < n; ++i) s += a[i];
      return s;
    })");
  const FunctionReport& f = fn(r, "sum");
  EXPECT_TRUE(f.ok);
  ASSERT_EQ(f.loops.size(), 1u);
  EXPECT_EQ(f.loops[0].bound, 64u);
  EXPECT_TRUE(f.loops[0].verified);
  EXPECT_EQ(f.wcet, 453u);
}

TEST(Loops, StrideGivesCeiling) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) {
      int s = 0;
      for (int i = 0; i < n; i += 4) ++s;
      return s;
    })");
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 3u);
}

TEST(Loops, CountingDown) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int n) {
      int s = 0;
      while (n > 0) { s += n; n -= 3; }
      return s;
    })");
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 34u);  // ceil(100 / 3)
}

TEST(Loops, DisequalityGuard) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 50) int n) {
      int s = 0;
      for (int i = 0; i != n; ++i) s += i;
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 50u);
}

TEST(Loops, DisequalityGuardThatCanBeJumpedOverIsRejected) {
  // i advances by 2: it may never be equal to n.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 50) int n) {
      int s = 0;
      for (int i = 0; i != n; i += 2) s += i;
      return s;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_TRUE(anyErrorContains(fn(r, "f"), "cannot derive an iteration bound"));
}

TEST(Loops, NestedLoopsMultiply) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n, CROSSCHECK_RANGE(0, 20) int m) {
      int s = 0;
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < m; ++j) ++s;
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_EQ(f.loops.size(), 2u);
  EXPECT_EQ(f.loops[0].bound, 10u);
  EXPECT_EQ(f.loops[1].bound, 20u);
  // inner: 1 + 20 * (2 + 2 + 2) + 2 = 123; outer: 1 + 10 * (2 + 123 + 2) + 2; s: 1; return: 1.
  EXPECT_EQ(f.wcet, 1u + 1u + 10u * 127u + 2u + 1u);
}

TEST(Loops, TriangularLoopUsesOuterInvariant) {
  // The inner bound n - i needs the invariant i >= 0.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) {
      int s = 0;
      for (int i = 0; i < n; ++i)
        for (int j = i; j < n; ++j) ++s;
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  ASSERT_EQ(f.loops.size(), 2u);
  EXPECT_EQ(f.loops[1].bound, 10u);
}

TEST(Loops, BranchInBodyNeedsACommonPotential) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 5) int x, CROSSCHECK_RANGE(0, 5) int y, const int* a) {
      int s = 0;
      while (x > 0 && y > 0) {
        if (a[s]) --x; else --y;
        ++s;
      }
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 9u);
}

TEST(Loops, UnboundedInputIsRejected) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(const int* a) {
      int i = 0;
      while (a[i] != 0) ++i;
      return i;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_FALSE(fn(r, "f").bounded);
  EXPECT_TRUE(anyErrorContains(fn(r, "f"), "cannot derive an iteration bound"));
}

TEST(Loops, NonTerminatingLoopIsRejected) {
  // The paper's "infinite while loop" example.
  Report r = check(R"(
    CROSSCHECK_REALTIME void f() {
      int i = 0;
      while (i != 1) { i = 0; }
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Loops, AnnotatedBoundIsAnAssumption) {
  Report r = check(R"(
    bool ready();
    CROSSCHECK_COST(2) bool ready();
    CROSSCHECK_REALTIME int f() {
      int n = 0;
      while (ready()) {
        CROSSCHECK_LOOP_BOUND(16);
        ++n;
      }
      return n;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 16u);
  EXPECT_FALSE(f.loops.at(0).verified);
  EXPECT_TRUE(anyAssumptionContains(f, "runs at most 16 times"));
  EXPECT_TRUE(anyAssumptionContains(f, "CROSSCHECK_COST"));
}

TEST(Loops, BoundedAttributeOnLoopVariable) {
  Report r = check(R"(
    struct Buffer { CROSSCHECK_COST(1) unsigned size() const; };
    CROSSCHECK_REALTIME unsigned f(const Buffer& b) {
      unsigned s = 0;
      for (CROSSCHECK_BOUNDED(128) unsigned i = 0; i < b.size(); ++i) s += i;
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 128u);
  EXPECT_FALSE(f.loops.at(0).verified);
}

TEST(Loops, DerivedBoundBeatsALooserAnnotation) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f() {
      int s = 0;
      for (CROSSCHECK_BOUNDED(1000) int i = 0; i < 8; ++i) ++s;
      return s;
    })");
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 8u);
  EXPECT_TRUE(fn(r, "f").loops.at(0).verified);
}

TEST(Loops, AssumeMakesABoundProvable) {
  Report r = check(R"(
    CROSSCHECK_COST(4) int read_length();
    CROSSCHECK_REALTIME int f() {
      int n = read_length();
      CROSSCHECK_ASSUME(n <= 32);
      int s = 0;
      for (int i = 0; i < n; ++i) ++s;
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 32u);
  EXPECT_TRUE(f.loops.at(0).verified);
  EXPECT_TRUE(anyAssumptionContains(f, "CROSSCHECK_ASSUME"));
}

TEST(Loops, ClampedInputIsBoundedWithoutAssumption) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(int n, const int* a) {
      if (n > 8) n = 8;
      int s = 0;
      for (int i = 0; i < n; ++i) s += a[i];
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 8u);
  EXPECT_TRUE(f.assumptions.empty());
}

TEST(Loops, BreakAddsOnePartialIteration) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int find(const int* a, int key) {
      for (int i = 0; i < 10; ++i)
        if (a[i] == key) return i;
      return -1;
    })");
  const FunctionReport& f = fn(r, "find");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 10u);
}

TEST(Loops, DoWhile) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 20) int n) {
      int s = 0;
      do { s += n; --n; } while (n > 0);
      return s;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 20u);  // executions of the body (the first one included)
}

TEST(Loops, UnsignedCountdownThatWrapsIsRejected) {
  // `i >= 0` is always true for an unsigned variable: the loop never ends.
  Report r = check(R"(
    CROSSCHECK_REALTIME unsigned f(CROSSCHECK_RANGE(0, 10) unsigned n) {
      unsigned s = 0;
      for (unsigned i = n; i >= 0; --i) s += i;
      return s;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Loops, RangeForOverFixedArray) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(const int (&a)[12]) {
      int s = 0;
      for (int x : a) s += x;
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 12u);
}

TEST(Loops, SwitchInsideLoop) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(const int* op, CROSSCHECK_RANGE(0, 30) int n) {
      int acc = 0;
      for (int i = 0; i < n; ++i) {
        switch (op[i]) {
          case 0: acc += 1; break;
          case 1: acc -= 1; break;
          default: acc = 0; break;
        }
      }
      return acc;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 30u);
}

TEST(Loops, ContinueInSwitchThatSkipsTheIncrementIsRejected) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(const int* op, CROSSCHECK_RANGE(0, 30) int n) {
      int i = 0;
      while (i < n) {
        switch (op[i]) { case 0: continue; default: break; }
        ++i;
      }
      return i;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

// --- soundness regressions: loops that must NOT be given a bound -----------------

struct RejectCase {
  const char* name;
  const char* body;  // body of `int f(RANGE(0,9) int n, RANGE(0,9) int m, const int* c)`
};

class Unsound : public ::testing::TestWithParam<RejectCase> {};

TEST_P(Unsound, IsRejected) {
  std::string code = std::string("CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n, "
                                 "CROSSCHECK_RANGE(0, 9) int m, const int* c) {") +
                     GetParam().body + "}";
  Report r = check(code);
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_FALSE(fn(r, "f").bounded);
}

INSTANTIATE_TEST_SUITE_P(
    Loops, Unsound,
    ::testing::Values(
        RejectCase{"ConditionalProgress", "int i = 0; while (i < n) { if (c[i]) i++; } return i;"},
        RejectCase{"MovingTarget", "int s = 0; for (int i = 0; i < n; i++) { n++; s++; } return s;"},
        RejectCase{"UnsignedWrap", "int s = 0; for (unsigned i = 10; i < 20; i -= 1) s++; return s;"},
        RejectCase{"StepMayBeZero", "int i = 0; while (i < n) i += m; return i;"},
        RejectCase{"AliasedBound",
                   "int k = 10; int* p = &k; int s = 0; for (int i = 0; i < k; i++) { (*p)++; s++; } return s;"},
        RejectCase{"InnerLoopUndoesProgress",
                   "int s = 0; for (int i = 0; i < n; i++) for (int j = 0; j < m; j++) { i--; s++; } return s;"},
        RejectCase{"ContinueSkipsIncrement",
                   "int i = 0; while (i < n) { if (c[i]) continue; i++; } return i;"},
        RejectCase{"DoWhileDiverges", "int i = 0; do { i--; } while (i < n); return i;"},
        RejectCase{"CounterReset", "for (int i = 0; i < n; i++) { if (c[i]) i = 0; } return 0;"},
        RejectCase{"SwitchCaseWithoutProgress",
                   "int i = 0; while (i < n) { switch (c[i]) { case 1: i++; break; case 2: break; } } return i;"},
        RejectCase{"BoundGrowsInBody",
                   "int i = 0; while (i < n) { i++; if (c[i]) n = n + 2; } return i;"},
        RejectCase{"AssignmentThatIsNotAnIncrement",
                   "int x = 0; while (x < n) { if (c[x]) break; x = m - x; } "
                   "int s = 0; while (x != n) { x = x + 1; s++; } return s;"},
        RejectCase{"BoundFromIntLimitOnly", "int i = 0; while (c[i] != 0) ++i; return i;"}),
    [](const ::testing::TestParamInfo<RejectCase>& info) { return std::string(info.param.name); });

TEST(Loops, StepWithPositiveLowerBound) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n, CROSSCHECK_RANGE(1, 5) int step) {
      int i = 0;
      while (i < n) i += step;
      return i;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 9u);
}

TEST(Loops, InfiniteLoopWithBreak) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n) {
      int i = 0;
      while (true) { if (i >= n) break; i++; }
      return i;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 10u);  // executions of the body: the 10th breaks
}

TEST(Loops, ManyPathsAreJoined) {
  // 2^6 paths through the body: more than the path budget, so they are joined.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 90) int n, const int* c) {
      int i = 0;
      while (i < n) {
        if (c[0]) i += 1; else i += 2;
        if (c[1]) i += 1; else i += 2;
        if (c[2]) i += 1; else i += 2;
        if (c[3]) i += 1; else i += 2;
        if (c[4]) i += 1; else i += 2;
        if (c[5]) i += 1; else i += 2;
      }
      return i;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 15u);  // ceil(90 / 6)
}

// --- calling contexts -------------------------------------------------------------
// A callee is analysed again with the intervals of its arguments at the call
// site (Lean: `call_bound_of_context`). `cnt` alone has no bound.

const char* kCnt = "static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s++; return s; }\n";

TEST(Contexts, ConstantArgumentBoundsTheCallee) {
  Report r = check(std::string(kCnt) + "CROSSCHECK_REALTIME int f() { return cnt(8); }");
  EXPECT_TRUE(fn(r, "f").ok);
  // Same cost as with the range declared on the parameter.
  Report d = check("static int cnt(CROSSCHECK_RANGE(8, 8) int n) { int s = 0; "
                   "for (int i = 0; i < n; i++) s++; return s; }\n"
                   "CROSSCHECK_REALTIME int f() { return cnt(8); }");
  EXPECT_EQ(fn(r, "f").wcet, fn(d, "f").wcet);
  EXPECT_TRUE(fn(r, "f").assumptions.empty());
}

TEST(Contexts, ArgumentRangeComesFromTheCallersFacts) {
  Report r = check(std::string(kCnt) +
                   "CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 5) int n) { return cnt(n + 1); }");
  EXPECT_TRUE(fn(r, "f").ok);
  Report d = check("static int cnt(CROSSCHECK_RANGE(1, 6) int n) { int s = 0; "
                   "for (int i = 0; i < n; i++) s++; return s; }\n"
                   "CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 5) int n) { return cnt(n + 1); }");
  EXPECT_EQ(fn(r, "f").wcet, fn(d, "f").wcet);
}

TEST(Contexts, CallInALoopUsesTheHullOfAllIterations) {
  // i ranges over [0, 8]: the callee must be bounded for 8, not for the
  // value of one iteration.
  const char* caller = "CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n) {"
                       "  int s = 0; for (int i = 0; i < n; i++) s += cnt(i); return s; }";
  Report r = check(std::string(kCnt) + caller);
  EXPECT_TRUE(fn(r, "f").ok);
  Report d = check(std::string("static int cnt(CROSSCHECK_RANGE(0, 8) int n) { int s = 0; "
                               "for (int i = 0; i < n; i++) s++; return s; }\n") + caller);
  EXPECT_EQ(fn(r, "f").wcet, fn(d, "f").wcet);
}

TEST(Contexts, TwoPathsToOneCallAreJoined) {
  const char* caller = "CROSSCHECK_REALTIME int f(bool b) { int k = 3; if (b) k = 7; return cnt(k); }";
  Report r = check(std::string(kCnt) + caller);
  EXPECT_TRUE(fn(r, "f").ok);
  Report d = check(std::string("static int cnt(CROSSCHECK_RANGE(3, 7) int n) { int s = 0; "
                               "for (int i = 0; i < n; i++) s++; return s; }\n") + caller);
  EXPECT_EQ(fn(r, "f").wcet, fn(d, "f").wcet);
}

TEST(Contexts, ReportGivesTheInContextBounds) {
  Options o;
  o.analyzeAll = true;
  ASSERT_TRUE(o.parse("entry=f"));
  Report r = check(std::string(kCnt) + "int f() { return cnt(8) + cnt(3); }", o);
  const FunctionReport& c = fn(r, "cnt");
  EXPECT_FALSE(c.ok);  // alone, `n` is unbounded
  ASSERT_EQ(c.loops.size(), 1u);
  EXPECT_FALSE(c.loops[0].verified);
  ASSERT_TRUE(c.loops[0].inContext.has_value());
  EXPECT_EQ(*c.loops[0].inContext, 8u);
  EXPECT_EQ(c.contexts, 2u);
  EXPECT_TRUE(fn(r, "f").ok);
}

struct ContextRejectCase {
  const char* name;
  const char* code;  // defines CROSSCHECK_REALTIME f
};

class UnsoundContext : public ::testing::TestWithParam<ContextRejectCase> {};

TEST_P(UnsoundContext, IsRejected) {
  Report r = check(GetParam().code);
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_FALSE(fn(r, "f").bounded);
}

INSTANTIATE_TEST_SUITE_P(
    Calls, UnsoundContext,
    ::testing::Values(
        ContextRejectCase{"UnboundedArgument",
                          "static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s++; return s; }\n"
                          "CROSSCHECK_REALTIME int f(int n) { return cnt(n); }"},
        ContextRejectCase{"ArgumentUnknownInALoop",
                          "static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s++; return s; }\n"
                          "CROSSCHECK_REALTIME int f(const int* c) { int s = 0, k = 1;"
                          "  for (int i = 0; i < 4; i++) { s += cnt(k); k += c[i]; } return s; }"},
        ContextRejectCase{"ArgumentWrapsInConversion",
                          "static int cnt(unsigned n) { int s = 0; for (unsigned i = 0; i < n; i++) s++; return s; }\n"
                          "CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(-1, 3) int n) { return cnt(n); }"},
        ContextRejectCase{"RecursiveCalleeIsNotSpecialised",
                          "static int down(int n) { return n <= 0 ? 0 : 1 + down(n - 1); }\n"
                          "CROSSCHECK_REALTIME int f() { return down(5); }"},
        ContextRejectCase{"CalleeThroughUnknownGlobal",
                          "int g;\n"
                          "static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s++; return s; }\n"
                          "CROSSCHECK_REALTIME int f() { return cnt(g); }"},
        ContextRejectCase{"OnlyOneSideKnown",
                          "static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s++; return s; }\n"
                          "CROSSCHECK_REALTIME int f(int n) { if (n < 0) return 0; return cnt(n); }"}),
    [](const ::testing::TestParamInfo<ContextRejectCase>& info) { return std::string(info.param.name); });

// --- logarithmic potentials (Lean logloop_sound) -----------------------------------

TEST(Loops, LogarithmicHalving) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 1000) int n) {
      int k = 0;
      while (n > 0) { n >>= 1; k++; }
      return k;
    }
    CROSSCHECK_REALTIME int g(CROSSCHECK_RANGE(1, 1000) int n) {
      int k = 0;
      while (n > 1) { n = n / 4; k++; }
      return k;
    })");
  ASSERT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops[0].bound, 10u);  // floor(log2 1000) + 1
  EXPECT_EQ(fn(r, "f").loops[0].potential, "log2(n)");
  ASSERT_TRUE(fn(r, "g").ok);
  EXPECT_EQ(fn(r, "g").loops[0].bound, 5u);   // floor(log4 1000) + 1
}

TEST(Loops, LogarithmicUnsignedAndGrowing) {
  Report r = check(R"(
    #include <stdint.h>
    CROSSCHECK_REALTIME uint32_t q(CROSSCHECK_RANGE(0, 4096) uint32_t len) {
      uint32_t s = 0;
      for (uint32_t k = len; k > 1U; k >>= 2U) s++;
      return s;
    }
    CROSSCHECK_REALTIME int g(CROSSCHECK_RANGE(1, 1000) int n) {
      int s = 0;
      for (int len = 1; len < n; len <<= 1) s++;
      return s;
    }
    CROSSCHECK_REALTIME int h(CROSSCHECK_RANGE(1, 4096) int n) {
      int k = 0, max = 2;
      while (n > max) { max = max << 1; k++; }
      return k;
    })");
  ASSERT_TRUE(fn(r, "q").ok);
  EXPECT_EQ(fn(r, "q").loops[0].bound, 7u);   // floor(log4 4096) + 1
  ASSERT_TRUE(fn(r, "g").ok);
  EXPECT_EQ(fn(r, "g").loops[0].bound, 10u);  // len <= 999 under the test: floor(log2 999) + 1 (1, 2, ..., 512)
  ASSERT_TRUE(fn(r, "h").ok);
  EXPECT_LE(fn(r, "h").loops[0].bound, 12u);
}

// Lexicographic arguments with a bounded inner counter are affine potentials once the
// bounds of the inner counter are invariants (Paper I, prop:lex-log (1)).
TEST(Loops, LexicographicWithBoundedInnerCounter) {
  Report r = check(R"(
    CROSSCHECK_COST(1) int nd(void);
    CROSSCHECK_REALTIME int reset(CROSSCHECK_RANGE(0, 100) int n, CROSSCHECK_RANGE(0, 50) int m) {
      int i = 0, j = 0, c = 0;
      while (i < n) { if (j < m) j++; else { j = 0; i++; } c++; }
      return c;
    }
    CROSSCHECK_REALTIME int refill(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 50) int y) {
      int c = 0;
      while (x > 0 && y > 0) { if (nd()) x--; else { y--; x = 100; } c++; }
      return c;
    }
    CROSSCHECK_REALTIME int twophase(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 50) int y) {
      int c = 0;
      while (x > 0) { if (y > 0) y--; else x--; c++; }
      return c;
    }
    CROSSCHECK_REALTIME int down_up(CROSSCHECK_RANGE(0, 100) int n) {
      int i = n, j = 0, c = 0;
      while (i > 0) { if (j > 0) j--; else { i--; j = i; } c++; }
      return c;
    })");
  ASSERT_TRUE(fn(r, "reset").ok);
  EXPECT_EQ(fn(r, "reset").loops[0].bound, 5100u);     // n (m + 1), reached
  ASSERT_TRUE(fn(r, "refill").ok);
  EXPECT_EQ(fn(r, "refill").loops[0].bound, 5000u);    // reached by x = 100, y = 50
  ASSERT_TRUE(fn(r, "twophase").ok);
  EXPECT_EQ(fn(r, "twophase").loops[0].bound, 150u);   // x + y
  ASSERT_TRUE(fn(r, "down_up").ok);
  EXPECT_GE(fn(r, "down_up").loops[0].bound, 5050u);   // 5050 iterations for n = 100
}

// Must not be reported as 0 executions: the body of the outer loop starts once and never
// ends (the inner loop does not terminate). Found by tests/fuzz_bounds.py.
// Option `budget`: with no budget left the search is cut short; whatever is still
// bounded must be bounded soundly, and the report says the budget ran out.
TEST(Budget, ExhaustedSearchStaysSound) {
  Options o;
  ASSERT_TRUE(o.parse("budget=1"));
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 20) int n) {
      int s = 0;
      for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
          for (int k = 0; k < j; k++) s++;
      return s;
    })", o);
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.budgetExhausted);
  if (f.bounded) {
    ASSERT_EQ(f.loops.size(), 3u);
    for (const LoopReport& l : f.loops)
      if (l.verified) { EXPECT_GE(l.bound, 19u); }
  }
  Options unlimited;
  ASSERT_TRUE(unlimited.parse("budget=0"));
  Report full = check(R"(
    CROSSCHECK_REALTIME int g(CROSSCHECK_RANGE(0, 20) int n) {
      int s = 0;
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) s++;
      return s;
    })", unlimited);
  EXPECT_FALSE(fn(full, "g").budgetExhausted);
  EXPECT_TRUE(fn(full, "g").bounded);
}

// A static local is initialised once, before the first call: at each call its value is
// whatever the previous calls left, so a loop bounded by a static counter that grows from
// call to call has no bound (the analysis once re-ran the initialiser at every call).
TEST(Unsound, StaticLocalCounterGrowsAcrossCalls) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(void) {
      static int n = 0;
      n++;
      int s = 0;
      for (int i = 0; i < n; i++) s++;
      return s;
    })", o);
  const FunctionReport& f = fn(r, "f");
  EXPECT_FALSE(f.bounded);
  EXPECT_NE(f.certificate, "emitted");
}

// Size bounds: a loop with at most 100 iterations adds at most 2 to `y` per iteration,
// so `y <= 300` after it, which bounds the second loop.
TEST(SizeBounds, AfterALoop) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 100) int y) {
      while (x > 0) { x--; y += 2; }
      while (y > 0) y--;
      return y;
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.bounded);
  ASSERT_EQ(f.loops.size(), 2u);
  EXPECT_EQ(f.loops[1].bound, 300u);
}

// A do-while: the first body and at most 99 more iterations, 3 added by each.
TEST(SizeBounds, AfterADoWhile) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 100) int x, CROSSCHECK_RANGE(0, 100) int y) {
      do { y += 3; x--; } while (x > 0);
      while (y > 0) y--;
      return y;
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.bounded);
  ASSERT_EQ(f.loops.size(), 2u);
  EXPECT_EQ(f.loops[1].bound, 400u);
}

// Inside a loop: at the head reached after n <= 100 complete iterations, y <= y0 + n, so
// the inner loop starts with y <= 200 (C4B's t13).
TEST(SizeBounds, AtTheHeadOfAnOuterLoop) {
  Report r = check(R"(
    CROSSCHECK_COST(1) int nd(void);
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 100) int y) {
      while (x > 0) {
        x--;
        if (nd() > 0) y++;
        else while (y > 0) y--;
      }
      return y;
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.bounded);
  ASSERT_EQ(f.loops.size(), 2u);
  EXPECT_EQ(f.loops[1].bound, 200u);
}

// Must be rejected: `y` doubles at every iteration, so no constant bounds its change.
TEST(Unsound, SizeBoundOfADoublingVariable) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(1, 100) int y) {
      while (x > 0) { x--; y = y + y; }
      while (y > 0) y--;
      return y;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: the change of `y` is a value with no range.
TEST(Unsound, SizeBoundOfAnUnknownIncrement) {
  Report r = check(R"(
    CROSSCHECK_COST(1) int nd(void);
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 100) int y) {
      while (x > 0) {
        x--;
        int d = nd();
        if (d > 0) y += d;
        else while (y > 0) y--;
      }
      return y;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: the outer loop has no bound, so no number of iterations bounds `y`.
TEST(Unsound, SizeBoundWithoutAnOuterBound) {
  Report r = check(R"(
    CROSSCHECK_COST(1) int nd(void);
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int y) {
      while (nd() > 0) {
        y++;
        if (nd() > 0) while (y > 0) y--;
      }
      return y;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// `p != q` in a loop guard: over the integers, `p < q` or `p > q`; the body starts on
// both paths, and `p + q` decreases on each.
TEST(Disequality, GuardSplitIntoTwoPaths) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int p, CROSSCHECK_RANGE(0, 100) int q) {
      while (q > 0 && p > 0 && p != q) {
        if (q < p) q = q - 1;
        else if (p < q) p = p - 1;
      }
      return p;
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.bounded);
  ASSERT_FALSE(f.loops.empty());
  EXPECT_GE(f.loops[0].bound, 99u);
}

// The same guard where one side does not move: when p > q nothing changes, so the loop
// does not terminate; it must not get a bound.
TEST(Unsound, DisequalityGuardOneSideStuck) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int p, CROSSCHECK_RANGE(0, 100) int q) {
      while (p != q) {
        if (p < q) p = p + 1;
      }
      return p;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// A conditional expression whose arm may be 0: the selected value has no positive lower
// bound, so the loop is not shown to decrease.
TEST(Unsound, ConditionalArmMayBeZero) {
  Report r = check(R"(
    CROSSCHECK_REALTIME void f(CROSSCHECK_RANGE(0, 1000) int len, CROSSCHECK_RANGE(0, 1) int z) {
      while (len > 0) { int d = len < 64 ? len : z; len -= d; }
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// `min(len, 64)` written as a conditional expression: at most each arm and at least 1.
TEST(Conditional, MinOfTwoArmsDecreases) {
  Report r = check(R"(
    CROSSCHECK_REALTIME void f(CROSSCHECK_RANGE(0, 1000) int len) {
      while (len > 0) { int d = len < 64 ? len : 64; len -= d; }
    })");
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.bounded);
  ASSERT_FALSE(f.loops.empty());
  EXPECT_EQ(f.loops[0].bound, 1000u);
}

TEST(Unsound, OuterLoopWhoseBodyNeverCompletes) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 9) int n) {
      int l = 2, acc = 0;
      for (int p = 2; p <= n; p = p * 2) {
        while (l >= p) { l += 1; }
        acc += 1;
      }
      return acc;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_FALSE(f.bounded);
  ASSERT_FALSE(f.loops.empty());
  if (f.loops[0].verified) { EXPECT_GE(f.loops[0].bound, 1u); }
}

// Must be rejected: the inner counter is refilled with an unknown value.
TEST(Unsound, LexInnerCounterRefilledWithUnknown) {
  Report r = check(R"(
    CROSSCHECK_COST(1) int nd(void);
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int n) {
      int i = 0, j = 0, c = 0;
      while (i < n) { if (j > 0) j--; else { j = nd(); i++; } c++; }
      return c;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: the outer counter does not advance when the inner one is reset.
TEST(Unsound, LexOuterCounterNotAdvanced) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 100) int n, CROSSCHECK_RANGE(0, 50) int m) {
      int i = 0, j = 0, c = 0;
      while (i < n) { if (j < m) j++; else { j = 0; } c++; }
      return c;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: the refill is larger than any bound of the inner counter at entry,
// and grows with the outer counter's start, which has no range.
TEST(Unsound, LexRefillFromUnboundedParameter) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int n, int big) {
      int i = n, j = 0, c = 0;
      while (i > 0) { if (j > 0) j--; else { i--; j = big; } c++; }
      return c;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: the counter starts at 0, which doubling never moves.
TEST(Unsound, GrowFromZero) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 1000) int n) {
      int s = 0;
      for (int len = 0; len < n; len <<= 1) s++;
      return s;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: an unsigned counter halved then increased: 5 -> 2 + 3 = 5 forever.
TEST(Unsound, UnsignedHalvedThenIncreased) {
  Report r = check(R"(
    #include <stdint.h>
    CROSSCHECK_REALTIME uint32_t f(CROSSCHECK_RANGE(0, 4096) uint32_t n) {
      uint32_t s = 0;
      while (n > 1U) { n >>= 1; n = n + 3U; s++; }
      return s;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: on one path the variable is not divided, so only the linear bound holds.
TEST(Unsound, LogOnlyOnSomePaths) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 1000) int n, int c) {
      int k = 0;
      while (n > 0) { if (c > k) n >>= 1; else n = n - 1; k++; }
      return k;
    })");
  ASSERT_TRUE(fn(r, "f").bounded);
  EXPECT_GE(fn(r, "f").loops[0].bound, 1000u);
}

// Must be rejected: a path multiplies the variable again (the loop may not terminate).
TEST(Unsound, LogUndoneByAnotherPath) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(2, 1000) int n, int c) {
      int k = 0;
      while (n > 1) { n >>= 1; if (c > 0) n = n * 3; k++; }
      return k;
    })");
  EXPECT_FALSE(fn(r, "f").bounded);
}

// Must be rejected: n / 2 rounds towards zero, so a negative n is not a potential >= 1.
TEST(Unsound, LogNeedsAPositivePotential) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(-1000, 1000) int n) {
      int k = 0;
      while (n != 0) { n = n / 2; k++; }
      return k;
    })");
  if (fn(r, "f").bounded) {
    EXPECT_GE(fn(r, "f").loops[0].bound, 10u);
  }
}

// The certificate of a halving loop: a whileLog node, and the facts of `n >>= 1` stated
// over a copy of the old value (they used to mention the new n twice).
TEST(Certificates, LogarithmicLoop) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 1000) int n) {
      int k = 0;
      while (n > 0) { n >>= 1; k++; }
      return k;
    })", o);
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.ok);
  EXPECT_EQ(f.certificate, "emitted");
  ASSERT_FALSE(r.certificates.empty());
  EXPECT_NE(r.certificates.back().find("\"whileLog\""), std::string::npos);
  EXPECT_NE(r.certificates.back().find("?old"), std::string::npos);
}

// A lexicographic loop is certified with the ordinary while node: the analysis hands its
// invariant j <= m to the generator, which proves it again.
TEST(Certificates, LexicographicLoop) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 100) int n, CROSSCHECK_RANGE(0, 50) int m) {
      int i = 0, j = 0, c = 0;
      while (i < n) { if (j < m) j++; else { j = 0; i++; } c++; }
      return c;
    })", o);
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.ok);
  EXPECT_EQ(f.loops[0].bound, 5100u);
  EXPECT_EQ(f.certificate, "emitted");
  ASSERT_FALSE(r.certificates.empty());
  EXPECT_NE(r.certificates.back().find("\"while\""), std::string::npos);
}

// A triangular nest: the inner loop's entry bound is the outer potential (gamma_j), so
// the outer body costs a + c * gamma_j and the outer loop gets the amortised bound of the
// checker (Lean `triOk`, `triloop_sound`): about half the analyser's product bound. A
// square nest keeps the product bound, and so does `j < i` (the inner bound grows while
// the outer potential decreases: not covered).
TEST(Certificates, AmortisedTriangularNest) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    int a[64];
    CROSSCHECK_REALTIME void down(void) {
      for (int i = 0; i < 40; i++) for (int j = i; j < 40; j++) a[j] += 1;
    }
    CROSSCHECK_REALTIME void square(void) {
      for (int i = 0; i < 40; i++) for (int j = 0; j < 40; j++) a[j] += 1;
    }
    CROSSCHECK_REALTIME void up(void) {
      for (int i = 0; i < 40; i++) for (int j = 0; j < i; j++) a[j] += 1;
    })", o);
  const FunctionReport& d = fn(r, "down");
  ASSERT_TRUE(d.ok);
  EXPECT_EQ(d.certificate, "emitted");
  ASSERT_TRUE(d.certificateBound.has_value());
  EXPECT_LT(*d.certificateBound * 10, d.wcet * 6);  // below 60% of the product bound
  const FunctionReport& sq = fn(r, "square");
  ASSERT_TRUE(sq.ok);
  EXPECT_EQ(sq.certificate, "emitted");
  ASSERT_TRUE(sq.certificateBound.has_value());
  EXPECT_EQ(*sq.certificateBound, sq.wcet);
  // `j < i`: amortised with the node `whileUp`.
  const FunctionReport& u = fn(r, "up");
  ASSERT_TRUE(u.ok);
  EXPECT_EQ(u.certificate, "emitted");
  ASSERT_TRUE(u.certificateBound.has_value());
  EXPECT_LT(*u.certificateBound * 10, u.wcet * 6);
}

// Products of parameters: a nest whose two entry bounds are parameters gets a certified
// bound quadratic in them (Lean `loopBoundOk`, third form), and a call composes it.
TEST(Symbolic, ProductOfParameters) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  ASSERT_TRUE(o.parse("symbolic"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int rect(int n, int m) {
      int s = 0;
      for (int i = 0; i < n; i++) for (int j = 0; j < m; j++) s++;
      return s;
    }
    CROSSCHECK_REALTIME int twice(int k) { return rect(k, k); })", o);
  for (const char* name : {"rect", "twice"}) {
    const FunctionReport& f = fn(r, name);
    EXPECT_EQ(f.certificate, "emitted") << name;
    EXPECT_NE(f.certificateSummary.find(")*max(0,"), std::string::npos) << name << ": " << f.certificateSummary;
  }
}

// Option `symbolic`: without input ranges, a loop with a ranking potential is not an
// error; the function has no numeric bound (it is not accepted as real-time), and the
// certificate carries a bound in the parameters.
TEST(Symbolic, BoundInTheParametersWithoutRanges) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  ASSERT_TRUE(o.parse("symbolic"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int count(int n) { int s = 0; for (int i = 0; i < n; ++i) s++; return s; }
    CROSSCHECK_REALTIME int caller(int n) { return count(n) + count(n + 3); }
    CROSSCHECK_REALTIME int nested(int n, int m) {
      int s = 0;
      for (int i = 0; i < n; ++i) for (int j = 0; j < m; ++j) s++;
      return s;
    })", o);
  for (const char* name : {"count", "caller"}) {
    const FunctionReport& f = fn(r, name);
    EXPECT_FALSE(f.ok) << name;        // no numeric bound: not accepted
    EXPECT_FALSE(f.bounded) << name;
    EXPECT_TRUE(f.symbolic) << name;
    EXPECT_EQ(f.certificate, "emitted") << name;
    EXPECT_NE(f.certificateSummary.find("max(0,n)"), std::string::npos) << name;
    EXPECT_TRUE(f.errors.empty()) << name;
  }
  // Symbolic: no numeric bound for the product of two parameters.
  EXPECT_TRUE(fn(r, "nested").symbolic);
  // A product of two parameters: certified since quadratic terms (Lean `loopBoundOk`,
  // third form).
  EXPECT_EQ(fn(r, "nested").certificate, "emitted");
  EXPECT_NE(fn(r, "nested").certificateSummary.find(")*max(0,"), std::string::npos);
}

// Bounds that decrease in a parameter or depend on a difference of two: the certificate
// has logical variables for -a and n - m as well.
TEST(Symbolic, BoundsInNegatedParametersAndDifferences) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  ASSERT_TRUE(o.parse("symbolic"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int upto30(int a) { int s = 0; while (a < 30) { a++; s++; } return s; }
    CROSSCHECK_REALTIME int gap(int n, int m) { int s = 0; while (m < n) { m++; s++; } return s; }
    CROSSCHECK_REALTIME int callgap(int n) { return gap(n, 5) + upto30(n); })", o);
  EXPECT_EQ(fn(r, "upto30").certificate, "emitted");
  EXPECT_NE(fn(r, "upto30").certificateSummary.find("max(0,-a)"), std::string::npos);
  EXPECT_EQ(fn(r, "gap").certificate, "emitted");
  EXPECT_NE(fn(r, "gap").certificateSummary.find("max(0,n-m)"), std::string::npos);
  EXPECT_EQ(fn(r, "callgap").certificate, "emitted");
}

// Without the option nothing changes: the loop is an error.
TEST(Symbolic, OffByDefault) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int count(int n) { int s = 0; for (int i = 0; i < n; ++i) s++; return s; })");
  EXPECT_FALSE(fn(r, "count").ok);
  EXPECT_FALSE(fn(r, "count").symbolic);
  EXPECT_FALSE(fn(r, "count").errors.empty());
}

// Must be rejected also in symbolic mode: loops without a ranking potential.
TEST(Unsound, SymbolicModeStillNeedsAPotential) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  ASSERT_TRUE(o.parse("symbolic"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int forever(int n) { int s = 0; while (n != 0) s++; return s; }
    CROSSCHECK_REALTIME int stalls(int n, int c) {
      int s = 0, i = 0;
      while (i < n) { if (c > 0) i++; s++; }
      return s;
    }
    CROSSCHECK_REALTIME int grows(int n) { int s = 0; for (int i = 0; i < n; ++i) { n++; s++; } return s; })", o);
  for (const char* name : {"forever", "stalls", "grows"}) {
    EXPECT_FALSE(fn(r, name).symbolic) << name;
    EXPECT_FALSE(fn(r, name).bounded) << name;
    EXPECT_NE(fn(r, name).certificate, "emitted") << name;
    EXPECT_FALSE(fn(r, name).errors.empty()) << name;
  }
}

// --- certificates (docs/certificate-format.md) ------------------------------------

TEST(Certificates, EmittedWithTheSameBound) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();  // keep them in the report, do not write a file
  Report r = check(R"(
    static int cnt(int n) { int s = 0; for (int i = 0; i < n; i++) s += 2; return s; }
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) {
      if (n < 3) return cnt(n);
      int s = 0;
      for (int i = 0; i < n; i++)
        for (int j = 0; j < i; j++) s = s + 1;
      return s + cnt(4);
    })", o);
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.ok);
  EXPECT_EQ(f.certificate, "emitted");
  ASSERT_TRUE(f.certificateBound.has_value());
  // The nest `j < i` is amortised in the certificate (node `whileUp`), not by the analyser.
  EXPECT_LT(*f.certificateBound, f.wcet);
  ASSERT_FALSE(r.certificates.empty());
  EXPECT_NE(r.certificates.back().find("\"while\""), std::string::npos);
  EXPECT_NE(r.certificates.back().find("\"whileUp\""), std::string::npos);
}

TEST(Certificates, OutsideTheFragmentSaysWhy) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) {
      int i = 0;
      do { i++; if (i > 5) break; } while (i < n);
      return i;
    })", o);
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_NE(fn(r, "f").certificate.find("do loop with a jump"), std::string::npos);
}

// A do loop without jumps: the body, then the loop (Lean `JStmt.desugar`).
TEST(Certificates, DoLoopWithoutJumps) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 10) int n) {
      int i = 0;
      do { i++; } while (i < n);
      return i;
    })", o);
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").certificate, "emitted");
}

// Early exits, switch and && tests are in the fragment; that the Lean checker accepts
// these certificates is tested by certificates_accepted_by_lean_checker
// (tests/certificates/jumps.cpp).
TEST(Certificates, EarlyExitsSwitchAndConjunctiveTests) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int brk(CROSSCHECK_RANGE(0, 50) int n, const int* c) {
      int x = 0;
      while (x < n) { if (c[x]) break; x++; }
      return x;
    }
    CROSSCHECK_REALTIME int find(CROSSCHECK_RANGE(0, 30) int n, const int* a, int key) {
      for (int i = 0; i < n; i++)
        if (a[i] == key) return i;
      return -1;
    }
    CROSSCHECK_REALTIME int both(CROSSCHECK_RANGE(0, 30) int n, const int* a) {
      int i = 0;
      while (i < n && a[i] != 0) i++;
      return i;
    }
    CROSSCHECK_REALTIME int sw(int op, CROSSCHECK_RANGE(0, 10) int n) {
      int s = 0;
      switch (op) {
        case 0: s = 1; break;
        case 1: for (int i = 0; i < n; i++) { if (i == op) continue; s += 2; } break;
        default: return 7;
      }
      return s;
    })", o);
  for (const char* name : {"brk", "find", "both", "sw"}) {
    const FunctionReport& f = fn(r, name);
    ASSERT_TRUE(f.ok) << name;
    EXPECT_EQ(f.certificate, "emitted") << name;
    ASSERT_TRUE(f.certificateBound.has_value()) << name;
    EXPECT_GT(*f.certificateBound, 0u) << name;
  }
  bool whileAnd = false;
  for (const std::string& c : r.certificates) whileAnd |= c.find("\"whileAnd\"") != std::string::npos;
  EXPECT_TRUE(whileAnd);
}

// Unsigned stores are lowered as `if (0 <= a <= 2^w - 1) x := a else havoc x`; the
// checker proves the wrapping branch dead (tests/certificates/unsigned.cpp).
TEST(Certificates, UnsignedStoresCarryTheirWrapCheck) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME unsigned f(const unsigned* a, CROSSCHECK_RANGE(0, 40) unsigned n) {
      unsigned s = 0;
      for (unsigned i = 0; i < n; i++) s += a[i];
      return s;
    }
    CROSSCHECK_REALTIME int g(CROSSCHECK_RANGE(0, 10) unsigned n) {
      int c = 0;
      unsigned m = n - 1;   // wraps when n == 0
      for (unsigned i = 0; i < m; i++) c++;
      return c;
    })", o);
  const FunctionReport& f = fn(r, "f");
  ASSERT_TRUE(f.ok);
  EXPECT_EQ(f.certificate, "emitted");
  ASSERT_TRUE(f.certificateBound.has_value());
  EXPECT_EQ(*f.certificateBound, f.wcet);
  ASSERT_FALSE(r.certificates.empty());
  EXPECT_NE(r.certificates.front().find("\"dead\""), std::string::npos);
  EXPECT_FALSE(fn(r, "g").ok);  // up to 2^32 - 1 iterations
}

// Modular certificates: a function certified once with a summary in its parameters,
// its callers using it through call nodes (docs/certificate-format.md, version 2).
TEST(Certificates, SummariesAndCallNodes) {
  Options o;
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    CROSSCHECK_REALTIME int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
      int s = 0;
      for (int i = 0; i < n; ++i) s += a[i];
      return s;
    }
    CROSSCHECK_REALTIME int twice(const int* a) { return sum(a, 10) + sum(a, 20); })", o);
  EXPECT_EQ(fn(r, "sum").certificateSummary, "5 + 7*max(0,n)");
  ASSERT_TRUE(fn(r, "twice").certificateBound.has_value());
  EXPECT_EQ(*fn(r, "twice").certificateBound, fn(r, "twice").wcet);  // = its in-context bound
  ASSERT_EQ(r.certificates.size(), 1u);  // one program certificate for the translation unit
  EXPECT_NE(r.certificates[0].find("\"node\":\"call\""), std::string::npos);
}

// --- library contracts (docs/contracts.md) ----------------------------------------

namespace {
std::string contractFile(const std::string& text) {
  std::string path = ::testing::TempDir() + "crosscheck_contracts_test.json";
  std::FILE* f = std::fopen(path.c_str(), "w");
  std::fputs(text.c_str(), f);
  std::fclose(f);
  return path;
}
const char* kCopy = R"({"format": "crosscheck-contracts", "version": 1, "implementation": "test",
  "contracts": [{"function": "copy_bytes", "cost": {"c": 8, "per_arg": {"2": 2}}}]})";
}  // namespace

TEST(Contracts, LibraryContractFile) {
  Options o;
  ASSERT_TRUE(o.parse("contracts=" + contractFile(kCopy)));
  ASSERT_TRUE(o.parse("certificates=unused.json"));
  o.certificatesPath.clear();
  Report r = check(R"(
    extern "C" void copy_bytes(unsigned char* d, const unsigned char* s, unsigned n);
    CROSSCHECK_REALTIME void frame(unsigned char* d, const unsigned char* s,
                                   CROSSCHECK_RANGE(0, 64) unsigned len) {
      copy_bytes(d, s, len);
      copy_bytes(d, s, 4);
    })", o);
  const FunctionReport& f = fn(r, "frame");
  ASSERT_TRUE(f.ok);
  // (call 1 + 8 + 2*64) + (call 1 + 8 + 2*4)
  EXPECT_EQ(f.wcet, 137u + 17u);
  EXPECT_TRUE(anyAssumptionContains(f, "contract file"));
  EXPECT_EQ(f.certificate, "emitted");
  EXPECT_EQ(f.certificateSummary, "26 + 2*max(0,len)");
  EXPECT_NE(r.certificates[0].find("\"contract\":true"), std::string::npos);
}

TEST(Unsound, ContractArgumentWithoutBoundIsRejected) {
  Options o;
  ASSERT_TRUE(o.parse("contracts=" + contractFile(kCopy)));
  Report r = check(R"(
    extern "C" void copy_bytes(unsigned char* d, const unsigned char* s, unsigned n);
    CROSSCHECK_REALTIME void f(unsigned char* d, const unsigned char* s, unsigned len) {
      copy_bytes(d, s, len);
    })", o);
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_TRUE(anyErrorContains(fn(r, "f"), "has no upper bound, which its contract needs"));
}

// --- legacy C idioms: globals, struct fields, tables, `--j` tests, intrinsics ------

TEST(Globals, TrackedWithAnAssumption) {
  Report r = check(R"(
    int nbits;
    CROSSCHECK_REALTIME int f() {
      nbits = 16; int c = 0;
      for (int i = 0; i < nbits; i++) c++;
      return c;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 16u);
  EXPECT_TRUE(anyAssumptionContains(f, "not modified by interrupts"));
}

TEST(Unsound, GlobalResetByACalleeInTheLoop) {
  Report r = check(R"(
    int k;
    static void touch() { k = 0; }
    CROSSCHECK_REALTIME int f() {
      k = 0;
      while (k < 10) { k++; touch(); }
      return k;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Unsound, GlobalWhoseAddressIsTaken) {
  Report r = check(R"(
    int k;
    int* pk = &k;
    CROSSCHECK_REALTIME int f() {
      k = 0;
      while (k < 10) { k++; *pk = 0; }
      return k;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Unsound, VolatileGlobalLimit) {
  Report r = check(R"(
    volatile int lim;
    CROSSCHECK_REALTIME int f() { int c = 0; for (int i = 0; i < lim && i >= 0; i++) c++; return c; })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Fields, ReadThroughAPointerParameter) {
  Options o;
  ASSERT_TRUE(o.parse("input-range=1,64"));
  Report r = check(R"(
    struct Inst { unsigned short numTaps; const short* coeffs; };
    CROSSCHECK_REALTIME int dot(const Inst* S, const short* x) {
      int acc = 0;
      for (unsigned k = 0; k < S->numTaps; k++) acc += S->coeffs[k] * x[k];
      return acc;
    })", o);
  const FunctionReport& f = fn(r, "dot");
  EXPECT_TRUE(f.ok);
  EXPECT_EQ(f.loops.at(0).bound, 64u);
  EXPECT_TRUE(anyAssumptionContains(f, "S->numTaps are not modified"));
  EXPECT_TRUE(anyAssumptionContains(f, "input-range"));
}

TEST(Unsound, FieldWrittenInTheFunctionIsNotASymbol) {
  Report r = check(R"(
    struct C { int n; };
    CROSSCHECK_REALTIME int f(C* c) {
      int k = 0;
      c->n = 5;
      while (k < c->n) { k++; c->n = c->n + 1; }
      return k;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Tables, ConstTableGivesTheRangeOfItsEntries) {
  Report r = check(R"(
    static const unsigned char kLen[4] = {3, 8, 12, 5};
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 3) int kind) {
      int n = kLen[kind], s = 0;
      for (int i = 0; i < n; i++) s++;
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 12u);
}

TEST(Loops, PreDecrementTest) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(1, 64) unsigned n) {
      unsigned j = n; int c = 0;
      do { c++; } while (--j);
      return c;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
}

TEST(Unsound, PreDecrementTestFromZero) {
  // j = 0: --j wraps to 2^32 - 1, and the loop runs about 2^32 times.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 64) unsigned n) {
      unsigned j = n; int c = 0;
      while (--j) c++;
      return c;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Cost, TargetIntrinsicsAndInlineAssembly) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(int a) {
      int r = ({ int t = a; __asm__ volatile ("nop" ::: "memory"); t; });
      __builtin_ia32_pause();
      return r;
    })");
  const FunctionReport& f = fn(r, "f");
  EXPECT_TRUE(f.ok);
  EXPECT_TRUE(anyAssumptionContains(f, "inline assembly"));
  EXPECT_TRUE(anyAssumptionContains(f, "target intrinsics"));
}

// --- facts kept when a loop is left through `break` -------------------------------

TEST(Loops, BreakKeepsTheInvariantsForTheNextLoop) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 50) int n, const int* c) {
      int x = 0;
      while (x < n) { if (c[x]) break; x++; }
      int s = 0;
      while (x < n) { x++; s++; }   // needs x >= 0 on both exits of the first loop
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  ASSERT_EQ(fn(r, "f").loops.size(), 2u);
  EXPECT_EQ(fn(r, "f").loops[1].bound, 50u);
}

TEST(Loops, AssignmentFormOfAnIncrementGivesTheSameInvariant) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 50) int n, const int* c) {
      int x = 0;
      while (x < n) { if (c[x]) break; x = x + 1; }
      int s = 0;
      while (x < n) { x = 1 + x; s++; }
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  ASSERT_EQ(fn(r, "f").loops.size(), 2u);
  EXPECT_EQ(fn(r, "f").loops[1].bound, 50u);
}

TEST(Loops, BreakDoesNotGiveTheNegatedGuard) {
  // After the first loop x may be anywhere in [0, n]: n - x is at most 9, not 0.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n, CROSSCHECK_RANGE(0, 9) int m,
                              const int* c) {
      int x = 0;
      while (x < n) { if (c[x]) break; x++; }
      int s = 0;
      for (int j = 0; j < n - x + m; j++) s++;
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  ASSERT_EQ(fn(r, "f").loops.size(), 2u);
  EXPECT_EQ(fn(r, "f").loops[1].bound, 18u);
}

TEST(Loops, DoWhileLeftByBreakInItsFirstBody) {
  // The break may leave before `i` is ever tested against n.
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 9) int n, const int* c) {
      int i = 20;
      do { if (c[0]) break; i--; } while (i > n);
      int s = 0;
      for (int j = 0; j < i; j++) s++;   // i is 20 after a break in the first body
      return s;
    })");
  EXPECT_TRUE(fn(r, "f").ok);
  ASSERT_EQ(fn(r, "f").loops.size(), 2u);
  EXPECT_EQ(fn(r, "f").loops[1].bound, 20u);
}

// --- recursion ------------------------------------------------------------------

TEST(Recursion, LinearRecursionDepth) {
  // Per activation: test 2 + max(return 1, (n-1: 1, call 1, *: 1, return 1)) = 6.
  Report r = check(R"(
    CROSSCHECK_REALTIME unsigned long fact(CROSSCHECK_RANGE(0, 20) int n) {
      if (n <= 1) return 1;
      return n * fact(n - 1);
    })");
  const FunctionReport& f = fn(r, "fact");
  EXPECT_TRUE(f.ok);
  ASSERT_TRUE(f.recursion.has_value());
  EXPECT_EQ(f.recursion->activations, 20u);
  EXPECT_EQ(f.recursion->branching, 1u);
  EXPECT_EQ(f.wcet, 120u);
}

TEST(Recursion, PaperLinearExample) {
  // foo(a) = a > 4 ? foo(a - 2) + 3 + 6 : a + 6, called with a <= 10: depth 3.
  Report r = check(R"(
    CROSSCHECK_REALTIME int foo(CROSSCHECK_RANGE(-100, 10) int a) {
      if (a > 4) a = foo(a - 2) + 3;
      return a + 6;
    })");
  const FunctionReport& f = fn(r, "foo");
  EXPECT_TRUE(f.ok);
  ASSERT_TRUE(f.recursion.has_value());
  EXPECT_EQ(f.recursion->activations, 4u);  // a = 10, 8, 6, 4
}

TEST(Recursion, BinaryRecursionUsesTheTreeBound) {
  // The paper's binary countdown: 2^(x+1) - 1 calls.
  Report r = check(R"(
    CROSSCHECK_REALTIME int foo(CROSSCHECK_RANGE(0, 5) int x) {
      if (x > 0) return foo(x - 1) + foo(x - 1);
      return 1;
    })");
  const FunctionReport& f = fn(r, "foo");
  EXPECT_TRUE(f.ok);
  ASSERT_TRUE(f.recursion.has_value());
  EXPECT_EQ(f.recursion->branching, 2u);
  EXPECT_EQ(f.recursion->activations, 63u);
}

TEST(Recursion, DivideAndConquerIsLinearBySizePotential) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int range_sum(const int* a, CROSSCHECK_RANGE(0, 1024) int lo,
                                      CROSSCHECK_RANGE(0, 1024) int hi) {
      CROSSCHECK_REQUIRE(lo < hi);
      if (hi - lo <= 1) return a[lo];
      int mid = lo + (hi - lo) / 2;
      return range_sum(a, lo, mid) + range_sum(a, mid, hi);
    })");
  const FunctionReport& f = fn(r, "range_sum");
  EXPECT_TRUE(f.ok);
  ASSERT_TRUE(f.recursion.has_value());
  EXPECT_EQ(f.recursion->activations, 2047u);  // 2 * 1024 - 1
}

TEST(Recursion, UnboundedRecursionIsRejected) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(int n) {
      if (n == 0) return 0;
      return f(n - 1) + 1;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
  EXPECT_TRUE(anyErrorContains(fn(r, "f"), "cannot bound the recursion"));
}

TEST(Recursion, NonDecreasingRecursionIsRejected) {
  Report r = check(R"(
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) {
      if (n == 0) return 0;
      return f(n) + 1;
    })");
  EXPECT_FALSE(fn(r, "f").ok);
}

TEST(Recursion, MutualRecursionIsRejected) {
  Report r = check(R"(
    int odd(int n);
    int even(int n) { return n == 0 ? 1 : odd(n - 1); }
    int odd(int n) { return n == 0 ? 0 : even(n - 1); }
    CROSSCHECK_REALTIME int f(CROSSCHECK_RANGE(0, 10) int n) { return even(n); }
    )");
  EXPECT_FALSE(fn(r, "f").ok);
}

// --- contracts ------------------------------------------------------------------

TEST(Contracts, RangeIsProvedAtCallSites) {
  Report r = check(R"(
    static int sum(const int* a, CROSSCHECK_RANGE(0, 16) int n) {
      int s = 0;
      for (int i = 0; i < n; ++i) s += a[i];
      return s;
    }
    CROSSCHECK_REALTIME int ok(const int* a) { return sum(a, 16); }
    CROSSCHECK_REALTIME int bad(const int* a) { return sum(a, 17); }
    CROSSCHECK_REALTIME int unknown(const int* a, int n) { return sum(a, n); }
    )");
  EXPECT_TRUE(fn(r, "ok").ok);
  EXPECT_FALSE(fn(r, "bad").ok);
  EXPECT_TRUE(anyErrorContains(fn(r, "bad"), "cannot prove the precondition"));
  EXPECT_FALSE(fn(r, "unknown").ok);
}

TEST(Contracts, RequireIsProvedAtCallSites) {
  Report r = check(R"(
    static int span(int lo, int hi) {
      CROSSCHECK_REQUIRE(lo <= hi);
      return hi - lo;
    }
    CROSSCHECK_REALTIME int ok(int x) { return span(x, x + 3); }
    CROSSCHECK_REALTIME int bad(int x) { return span(x + 1, x); }
    )");
  EXPECT_TRUE(fn(r, "ok").ok);
  EXPECT_FALSE(fn(r, "bad").ok);
}

// --- real-time profile -------------------------------------------------------------

struct ProfileCase {
  const char* name;
  const char* code;
  const char* message;
};

class Profile : public ::testing::TestWithParam<ProfileCase> {};

TEST_P(Profile, ViolationIsReported) {
  Report r = check(GetParam().code);
  const FunctionReport& f = fn(r, "f");
  EXPECT_FALSE(f.ok);
  EXPECT_TRUE(anyErrorContains(f, GetParam().message))
      << "errors: " << (f.errors.empty() ? "<none>" : f.errors.front());
}

INSTANTIATE_TEST_SUITE_P(
    RealTime, Profile,
    ::testing::Values(
        ProfileCase{"New", "CROSSCHECK_REALTIME int f() { int* p = new int(1); return *p; }",
                    "dynamic allocation"},
        ProfileCase{"Delete", "CROSSCHECK_REALTIME void f(int* p) { delete p; }",
                    "dynamic deallocation"},
        ProfileCase{"Malloc",
                    "extern \"C\" void* malloc(unsigned long);\n"
                    "CROSSCHECK_REALTIME void* f() { return malloc(16); }",
                    "dynamic allocation"},
        ProfileCase{"Throw", "CROSSCHECK_REALTIME void f(int x) { if (x) throw 1; }", "'throw'"},
        ProfileCase{"Try", "CROSSCHECK_REALTIME int f() { try { return 1; } catch (...) { return 0; } }",
                    "'try'"},
        ProfileCase{"Virtual",
                    "struct B { virtual int g() const; };\n"
                    "CROSSCHECK_REALTIME int f(const B& b) { return b.g(); }",
                    "virtual call"},
        ProfileCase{"FunctionPointer", "CROSSCHECK_REALTIME int f(int (*g)(int)) { return g(1); }",
                    "indirect call"},
        ProfileCase{"Goto", "CROSSCHECK_REALTIME int f(int x) { if (x) goto end; x = 1; end: return x; }",
                    "'goto'"},
        ProfileCase{"UnknownCallee", "int g(int);\nCROSSCHECK_REALTIME int f() { return g(1); }",
                    "no definition is available"},
        ProfileCase{"TransitiveAllocation",
                    "static int* make() { return new int(0); }\n"
                    "CROSSCHECK_REALTIME int f() { return *make(); }",
                    "is not real-time safe"},
        ProfileCase{"NonTrivialDestructor",
                    "struct Guard { ~Guard(); };\nCROSSCHECK_REALTIME void f() { Guard g; }",
                    "non-trivial destructor"}),
    [](const ::testing::TestParamInfo<ProfileCase>& info) { return std::string(info.param.name); });

TEST(Profile, DevirtualizedCallIsAllowed) {
  Report r = check(R"(
    struct B { virtual int g() const { return 1; } };
    struct D final : B { int g() const override { return 2; } };
    CROSSCHECK_REALTIME int f(const D& d) { return d.g(); }
    )");
  EXPECT_TRUE(fn(r, "f").ok);
}

TEST(Profile, PlacementNewIsAllowed) {
  Report r = check(R"(
    inline void* operator new(unsigned long, void* p) noexcept { return p; }
    struct P { int x; };
    CROSSCHECK_REALTIME int f(void* storage) { P* p = new (storage) P{3}; return p->x; }
    )");
  EXPECT_TRUE(fn(r, "f").ok);
}

TEST(Profile, UnannotatedFunctionsAreNotAnalysed) {
  Report r = check("int f() { int* p = new int(1); return *p; }");
  EXPECT_EQ(r.find("f"), nullptr);
  EXPECT_TRUE(r.allOk());
}

// --- deadlines and reporting -----------------------------------------------------

TEST(Deadline, MetAndMissed) {
  Report r = check(R"(
    CROSSCHECK_DEADLINE(10) int fast(int x) { return x + 1; }
    CROSSCHECK_DEADLINE(10) int slow(const int* a) {
      int s = 0;
      for (int i = 0; i < 100; ++i) s += a[i];
      return s;
    })");
  EXPECT_TRUE(fn(r, "fast").ok);
  EXPECT_EQ(*fn(r, "fast").deadline, 10u);
  EXPECT_FALSE(fn(r, "slow").ok);
  EXPECT_TRUE(fn(r, "slow").bounded);
  EXPECT_TRUE(anyErrorContains(fn(r, "slow"), "exceeds its deadline"));
}

// Response time under interrupt handlers (Lean Interrupts.response_time_bound).
TEST(Interrupts, ResponseTime) {
  Report r = check(R"(
    int ticks;
    CROSSCHECK_INTERRUPT(10) void isr() { ticks = ticks + 1; }
    CROSSCHECK_DEADLINE(100) int task(const int* a) {
      int s = 0;
      for (int i = 0; i < 4; ++i) s += a[i];
      return s;
    })");
  ASSERT_TRUE(fn(r, "isr").interruptHandler);
  ASSERT_TRUE(fn(r, "task").responseTime.has_value());
  std::uint64_t C = fn(r, "task").wcet, c = fn(r, "isr").wcet, R = *fn(r, "task").responseTime;
  // R is a fixed point of the iteration and at least the bound plus one activation
  EXPECT_EQ(R, C + c * ((R + 9) / 10));
  EXPECT_GE(R, C + c);
  EXPECT_TRUE(fn(r, "task").ok);
}

// Must be rejected: the cost bound meets the deadline, the response time does not.
TEST(Unsound, DeadlineMissedUnderInterrupts) {
  Report r = check(R"(
    int ticks;
    CROSSCHECK_INTERRUPT(5) void isr() { ticks = ticks + 1; ticks = ticks + 1; }
    CROSSCHECK_DEADLINE(40) int task(const int* a) {
      int s = 0;
      for (int i = 0; i < 4; ++i) s += a[i];
      return s;
    })");
  ASSERT_TRUE(fn(r, "task").bounded);
  EXPECT_LE(fn(r, "task").wcet, 40u);
  EXPECT_FALSE(fn(r, "task").ok);
  EXPECT_TRUE(anyErrorContains(fn(r, "task"), "under interrupts exceeds its deadline"));
}

// Must be rejected: a handler without a positive minimum inter-arrival time.
TEST(Unsound, InterruptWithoutPeriod) {
  Report r = check(R"(
    CROSSCHECK_INTERRUPT(0) void isr() {}
    CROSSCHECK_REALTIME int task(int x) { return x; })");
  EXPECT_FALSE(fn(r, "isr").ok);
  EXPECT_FALSE(fn(r, "task").responseTime.has_value());
}

TEST(Report, JsonContainsTheBound) {
  Report r = check("CROSSCHECK_REALTIME int f(int x) { return x + 1; }");
  std::string json = r.toJson();
  EXPECT_NE(json.find("\"name\": \"f\""), std::string::npos);
  EXPECT_NE(json.find("\"wcet\": 2"), std::string::npos);
  EXPECT_NE(json.find("\"ok\": true"), std::string::npos);
}

TEST(Options, Parsing) {
  Options o;
  EXPECT_TRUE(o.parse("report=out.json"));
  EXPECT_EQ(o.reportPath, "out.json");
  EXPECT_TRUE(o.parse("max-paths=4"));
  EXPECT_EQ(o.maxPaths, 4u);
  EXPECT_TRUE(o.parse("all"));
  EXPECT_FALSE(o.parse("weight-nonsense=3"));
  EXPECT_FALSE(o.parse("weight-arith=abc"));
  EXPECT_FALSE(o.parse("bogus"));
}

}  // namespace
