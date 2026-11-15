// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// CrossCheck source annotations, for C and C++.
//
// The macros expand to `[[clang::annotate(...)]]` under Clang and to nothing
// under other compilers, so annotated code stays portable. They are read by the
// CrossCheck Clang plugin / `crosscheck-tool`; they have no run-time effect.
#ifndef CROSSCHECK_ATTRIBUTES_HPP
#define CROSSCHECK_ATTRIBUTES_HPP

#if defined(__clang__) && defined(__cplusplus)
#define CROSSCHECK_ANNOTATE(...) [[clang::annotate(__VA_ARGS__)]]
#elif defined(__clang__)
// C: the GNU spelling, accepted by Clang in every C standard mode.
#define CROSSCHECK_ANNOTATE(...) __attribute__((annotate(__VA_ARGS__)))
#else
#define CROSSCHECK_ANNOTATE(...)
#endif

/// Function: enforce the real-time profile (no dynamic allocation, no
/// exceptions, no virtual or indirect calls, every loop and recursion bounded)
/// and report a worst-case cost bound.
#define CROSSCHECK_REALTIME CROSSCHECK_ANNOTATE("crosscheck::realtime")

/// Function: real-time profile plus a deadline, in abstract cost units. The
/// function is rejected when its worst-case cost bound exceeds `units`.
#define CROSSCHECK_DEADLINE(units) CROSSCHECK_ANNOTATE("crosscheck::deadline", units)

/// Parameter: precondition `lo <= p <= hi` on an integer parameter. Assumed
/// inside the function, proved at every call site that CrossCheck analyses.
#define CROSSCHECK_RANGE(lo, hi) CROSSCHECK_ANNOTATE("crosscheck::range", lo, hi)

/// Loop variable declared in a `for` init-statement: the loop runs at most
/// `n` iterations. Trusted (reported as an assumption) unless CrossCheck can
/// derive a bound itself.
#define CROSSCHECK_BOUNDED(n) CROSSCHECK_ANNOTATE("crosscheck::bounded", n)

/// Function declaration: trusted worst-case cost of a function whose body is
/// not available or should not be analysed (reported as an assumption).
#define CROSSCHECK_COST(units) CROSSCHECK_ANNOTATE("crosscheck::cost", units)

// Markers recognised by the analyser. They are only ever named inside an
// unevaluated `sizeof`, so they are never called and need no definition.
#if defined(__cplusplus)
namespace crosscheck {
namespace detail {
int loop_bound(unsigned long long);
int require(bool);
int assume(bool);
}  // namespace detail
}  // namespace crosscheck
#define CROSSCHECK_DETAIL_(name) ::crosscheck::detail::name
#else
int crosscheck_detail_loop_bound(unsigned long long);
int crosscheck_detail_require(int);
int crosscheck_detail_assume(int);
#define CROSSCHECK_DETAIL_(name) crosscheck_detail_##name
#endif

/// First statement of a loop body: the loop runs at most `n` iterations.
/// Trusted (reported as an assumption) unless CrossCheck derives a bound.
#define CROSSCHECK_LOOP_BOUND(n) ((void)sizeof(CROSSCHECK_DETAIL_(loop_bound)(n)))

/// Leading statement of a function body: precondition over the parameters,
/// e.g. `CROSSCHECK_REQUIRE(lo < hi);`. Assumed inside the function, proved at
/// every call site that CrossCheck analyses. Only conjunctions of linear
/// integer comparisons are used; anything else is ignored (neither assumed nor
/// checked).
#define CROSSCHECK_REQUIRE(cond) ((void)sizeof(CROSSCHECK_DETAIL_(require)(cond)))

/// Statement: a fact the analyser may use from this point on, e.g. after
/// reading a device register: `CROSSCHECK_ASSUME(len <= 64);`. Trusted
/// (reported as an assumption). The condition is not evaluated at run time.
#define CROSSCHECK_ASSUME(cond) ((void)sizeof(CROSSCHECK_DETAIL_(assume)(cond)))

#endif  // CROSSCHECK_ATTRIBUTES_HPP
