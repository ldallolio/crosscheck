// Logarithmic loops: certificates with a whileLog node (Lean logloop_sound), checked by
// the Lean checker in the ctest certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>

CROSSCHECK_REALTIME int halvings(CROSSCHECK_RANGE(0, 4096) int n) {
  int k = 0;
  while (n > 0) { n >>= 1; k++; }
  return k;
}

CROSSCHECK_REALTIME int digits(CROSSCHECK_RANGE(0, 99999) int n) {
  int d = 0;
  while (n >= 10) { n = n / 10; d++; }
  return d + 1;
}

CROSSCHECK_REALTIME int stages(void) {
  int s = 0;
  for (int len = 1024; len > 1; len >>= 2) s += len;
  return s;
}

CROSSCHECK_REALTIME int doubling(CROSSCHECK_RANGE(1, 1000) int n) {
  int s = 0;
  for (int len = 1; len < n; len <<= 1) s++;
  return s;
}
