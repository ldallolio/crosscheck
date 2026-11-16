/* Mini-C export (--opt=minic): functions named ok_* must be VALIDATED by the checker
   (their certificate's program is the lowering of their source); for the functions
   named no_* the exporter must not claim an exact translation (it refuses them or
   models the construct as an unknown value), so they must not be VALIDATED. */
#include <crosscheck/attributes.hpp>

int ok_sum(void) {
  int s = 0;
  for (int i = 0; i < 10; i++) s += i;
  return s;
}

int ok_nested(void) {
  int c = 0;
  for (int i = 0; i < 8; ++i)
    for (int j = i; j < 8; j++) c = c + 1;
  return c;
}

void ok_memory(int *a, int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 64);
  for (int i = 0; i < n; i++) a[i] = i * 2;
}

int ok_branches(int x) {
  CROSSCHECK_REQUIRE(x >= 0 && x <= 100);
  int k = 0;
  if (x > 3) k = 8; else k = 5;
  while (k > 0 && x >= 0) k -= 2;
  return k;
}

int ok_dead(void) {
  int i = 0;
  if (i > 5) { i = 9; while (i > 0) i--; }
  return i;
}

int ok_down(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 1000);
  int steps = 0;
  while (!(n <= 0)) { n = n - 3; steps++; }
  return steps;
}

/* unsigned counters: each store keeps its value only if it is in the variable's range
   (mini-C `assignU`); the checker proves the wrapping branches dead */
unsigned ok_unsigned(void) {
  unsigned s = 0;
  for (unsigned i = 0; i < 10u; i++) s = s + i;
  return s;
}
unsigned ok_unsigned_down(unsigned n) {
  CROSSCHECK_REQUIRE(n <= 1000u);
  unsigned k = 0;
  while (n > 0u) { n -= 1u; k++; }
  return k;
}
unsigned ok_unsigned_halve(unsigned n) {
  CROSSCHECK_REQUIRE(n <= 4096u);
  unsigned k = 0;
  while (n > 1u) { n >>= 1; k++; }
  return k;
}

/* a narrow unsigned counter is promoted to int: c + 1 is converted back, refused */
int no_unsigned_char(void) {
  int k = 0;
  for (unsigned char c = 0; c < 10; c++) k++;
  return k;
}

/* a narrow counter: c + 1 is converted back to signed char, which may wrap in general */
int no_char(void) {
  int k = 0;
  for (signed char c = 0; c < 100; c++) k++;
  return k;
}

/* the address of the counter is taken: writes through p are not seen */
int no_alias(int *out) {
  int i;
  int *p = &i;
  for (i = 0; i < 10; i++) *out = *p;
  return i;
}

/* a return inside a loop (not in the fragment of the exporter yet) */
int no_return(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 50);
  for (int i = 0; i < n; i++)
    if (i > 20) return i;
  return 0;
}

/* returns in conditionals outside loops: the rest of the body goes into the branches */
int ok_early(int x) {
  CROSSCHECK_REQUIRE(x >= 0 && x <= 100);
  int k = 0;
  if (x < 10) return 1;
  for (int i = 0; i < 5; i++) k++;
  if (x > 50) { k = k + 2; return k; }
  return k + 1;
}

/* a division stored in its operand: mini-C `div` with a scratch variable for the old value */
int ok_halve(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 1000);
  int k = 0;
  while (n > 0) { n = n / 2; k++; }
  return k;
}

/* compound forms: n /= 10 and n >>= 1 (a shift is the quotient by 2^k) */
int ok_digits(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 99999);
  int d = 0;
  while (n > 0) { n /= 10; d++; }
  return d;
}
int ok_shift(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 4096);
  int k = 0;
  while (n > 1) { n >>= 1; k++; }
  return k;
}

/* quotient, remainder and mask of another variable, as loop limits */
int ok_quarter(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 400);
  int q = n / 4, s = 0;
  for (int i = 0; i < q; i++) s++;
  return s;
}
int ok_remainder_mask(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 1000);
  int r = n % 8, m = n & 15, s = 0;
  for (int i = 0; i < r; i++) s++;
  for (int j = 0; j < m; j++) s++;
  return s;
}

/* the result of n % 8u is unsigned: storing it into an int is a conversion, refused */
int no_unsigned_remainder(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 1000);
  int r = n % 8u, s = 0;
  for (int i = 0; i < r; i++) s++;
  return s;
}

/* a counter doubled up to a limit (whileGrow); x << 1 is 2 * x in mini-C (signed) */
int ok_doubling(int n) {
  CROSSCHECK_REQUIRE(n >= 1 && n <= 1000);
  int s = 0;
  for (int len = 1; len < n; len <<= 1) s++;
  return s;
}

/* a loop test with a disequality: mini-C has no meaning for it, the exporter refuses
   (found by tests/fuzz_bounds.py: a source was written and then not validated) */
int no_loop_test_ne(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  int i = 0, k = 0;
  while (i != n && i <= n) { i++; k++; }
  return k;
}

/* calls: the arguments are stored into the callee's parameter variables, then the callee
   of the certificate file runs (mini-C `call`); the value of the call is unknown */
int ok_callee(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 100);
  int s = 0;
  for (int i = 0; i < n; i++) s++;
  return s;
}
int ok_call(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 50);
  int a = ok_callee(n);
  ok_callee(n + 1);
  a = a + ok_callee(2 * n);
  return a;
}
int ok_call_in_loop(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 10);
  int s = 0;
  for (int i = 0; i < n; i++) s += ok_callee(i);
  return s;
}
/* a call in a loop test is not in the fragment */
int no_call_in_test(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 10);
  int s = 0;
  while (ok_callee(n) > 200) s++;
  return s;
}

/* a call in the returned value */
int ok_call_in_return(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 50);
  return ok_callee(n) + 1;
}
