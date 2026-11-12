// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// End-to-end tests of the analyser on small C++ programs. The cost figures in
// the comments are derived by hand from the cost model documented in
// clang-plugin/README.md (all weights 1).
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
  EXPECT_EQ(f.loops.at(0).bound, 19u);  // iterations after the first one
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
  EXPECT_EQ(fn(r, "f").loops.at(0).bound, 9u);
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
