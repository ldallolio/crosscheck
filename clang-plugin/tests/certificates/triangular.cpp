// Triangular loop nests: an inner loop whose entry bound is the potential of the
// enclosing loop (`j` from `i` to `n`) makes the enclosing body cost `a + c * gamma_j`,
// and the enclosing loop is certified with the amortised bound (Lean `triOk`,
// `triloop_sound`) instead of the number of iterations times the largest body cost.
// Checked by the Lean checker in the ctest certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>
int a[128];
CROSSCHECK_REALTIME void suffix(void) {
  for (int i = 0; i < 100; i++)
    for (int j = i; j < 100; j++) a[j] += a[i];
}
CROSSCHECK_REALTIME void bubble(void) {
  for (int i = 0; i < 99; i++)
    for (int j = 0; j < 99 - i; j++)
      if (a[j] > a[j + 1]) { int t = a[j]; a[j] = a[j + 1]; a[j + 1] = t; }
}
CROSSCHECK_REALTIME void step2(CROSSCHECK_RANGE(0, 60) int n) {
  for (int i = 0; i < n; i += 2)
    for (int j = i; j < n; j++) a[j] -= 1;
}
CROSSCHECK_REALTIME void three(void) {
  for (int i = 0; i < 20; i++)
    for (int j = i; j < 20; j++)
      for (int k = j; k < 20; k++) a[k] += 1;
}
// An inner loop from 0 to the outer counter: its entry bound grows while the outer
// potential falls; certified with the node `whileUp` (Lean `upOk`, `uploop_sound`), in
// whose body the logical variable is what the outer potential has lost (`k - pot`).
CROSSCHECK_REALTIME void prefix(void) {
  for (int i = 0; i < 100; i++)
    for (int j = 0; j < i; j++) a[i] += a[j];
}
CROSSCHECK_REALTIME void insertion(void) {
  for (int i = 1; i < 100; i++) {
    int j = i;
    while (j > 0 && a[j - 1] > a[j]) { int t = a[j]; a[j] = a[j - 1]; a[j - 1] = t; j--; }
  }
}
CROSSCHECK_REALTIME void upto(void) {
  for (int i = 0; i < 30; i++)
    for (int j = 0; j <= i; j++) a[j] += 1;
}
