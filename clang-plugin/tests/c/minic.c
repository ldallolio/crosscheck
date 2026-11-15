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

/* unsigned counter: unsigned arithmetic wraps, the exporter refuses */
unsigned no_unsigned(void) {
  unsigned s = 0;
  for (unsigned i = 0; i < 10u; i++) s = s + i;
  return s;
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

/* a division: the generator describes n / 2 by facts, the exporter does not (yet) */
int no_halve(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 1000);
  int k = 0;
  while (n > 0) { n = n / 2; k++; }
  return k;
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
