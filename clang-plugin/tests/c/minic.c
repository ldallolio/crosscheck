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

/* early exits: break, continue and return inside while and for loops are written with
   the flag variables of the certificate (?break<depth>, ?continue<depth>, ?return): a
   jump stores 1 into its flag, the loop test also requires the break and return flags to
   be 0, the increment of a for loop runs only if they are, and what follows a loop that
   may return runs only if it did not */
int ok_return_in_loop(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 50);
  for (int i = 0; i < n; i++)
    if (i > 20) return i;
  return 0;
}
int ok_break(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 100);
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (i >= 40) break;
    k++;
  }
  return k;
}
int ok_break_while(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 100);
  int k = 0;
  while (n > 0) {
    n--;
    if (k >= 7) break;
    k++;
  }
  return k;
}
int ok_continue(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 30);
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (i < 3) continue;
    k++;
  }
  return k;
}
/* a break of the inner loop only, then statements of the outer body */
int ok_break_nested(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 10);
  int s = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < 8; j++) {
      if (j > i) break;
      s++;
    }
    s++;
  }
  return s;
}
/* a return in an inner loop leaves both loops; statements follow each loop */
int ok_return_nested(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 10);
  int s = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < 4; j++) {
      if (s > 20) return s;
      s++;
    }
    s++;
  }
  s = s + 1;
  return s;
}
/* two loops of the same depth, one after the other: the same flag, cleared by each */
int ok_break_twice(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  int k = 0;
  for (int i = 0; i < n; i++) { if (i == 5) break; k++; }
  for (int i = 0; i < n; i++) { if (i == 9) break; k++; }
  return k;
}
/* break, continue and return in one loop */
int ok_all_exits(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 40);
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (i == 2) continue;
    if (i == 30) break;
    if (k > 25) return -1;
    k++;
  }
  return k;
}
/* a loop without a test, left by break: not in the fragment (a certificate uses another
   kind of loop for a flag alone) */
int no_loop_without_test(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  int k = 0;
  for (int i = 0;; i++) {
    if (i >= n) break;
    k++;
  }
  return k;
}
/* do loops are not in the fragment */
int no_do_break(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  int k = 0;
  do {
    if (k >= n) break;
    k++;
  } while (k < 20);
  return k;
}
/* switch: the cost of the test, then each case group under an unknown test (the value is
   not compared with the labels); break ends its group; fall-through is the next group */
int ok_switch(int x) {
  CROSSCHECK_REQUIRE(x >= 0 && x <= 9);
  int k = 0;
  switch (x) {
    case 0: k = 1; break;
    case 1:
    case 2: k = 2;
    case 3: k = k + 3; break;
    default: k = 7;
  }
  return k;
}
/* in a loop: continue is the loop's, break the switch's; statements follow the switch */
int ok_switch_in_loop(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  int k = 0;
  for (int i = 0; i < n; i++) {
    switch (i) {
      case 1: k += 2; break;
      case 2: continue;
      default: k++;
    }
    k++;
  }
  return k;
}
/* return inside a switch, and a loop inside a case */
int ok_switch_return(int x) {
  CROSSCHECK_REQUIRE(x >= 0 && x <= 9);
  int k = 0;
  switch (x) {
    case 0: return 5;
    case 1: for (int i = 0; i < 4; i++) { if (i == x) break; k++; } break;
    default: if (x > 5) return 6; k = 3;
  }
  k = k + 1;
  return k;
}
/* a case label inside a nested statement (Duff's device): refused */
int no_switch_nested_label(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 3);
  int k = 0;
  switch (n) {
    case 0: if (k == 0) { case 1: k++; }
    default: k++;
  }
  return k;
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

/* Tracked globals: variables of the program certificate. */
int g_limit;
int ok_global(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 50);
  int s = 0;
  g_limit = n;
  for (int i = 0; i < g_limit; i++) s++;
  return s;
}
void ok_set_limit(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  g_limit = n;
}
/* A static local: its initialisation runs once, before the first call, so its
   declaration does nothing at a call and its value on entry is unknown (a global
   visible in one function). */
int ok_static_local(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  static int calls = 0;
  calls = n;
  int s = 0;
  for (int i = 0; i < calls; i++) s++;
  return s;
}
/* A static local whose address escapes is written through a pointer: not tracked, so
   the loop that it bounds has no exact translation (no bound, no certificate). */
int no_static_escaped(int n) {
  CROSSCHECK_REQUIRE(n >= 0 && n <= 20);
  static int calls = 0;
  int *p = &calls;
  *p = n;
  int s = 0;
  for (int i = 0; i < calls; i++) s++;
  return s;
}

/* do loops: the body, then the loop (Lean JStmt.doLoop, desugared). */
int ok_do(int n) {
  CROSSCHECK_REQUIRE(n >= 1 && n <= 50);
  int i = 0;
  do {
    i++;
  } while (i < n);
  return i;
}
