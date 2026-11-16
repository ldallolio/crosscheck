// Option symbolic is not set by the certificate test, so these functions have ranges; they
// document the shapes whose bounds are certified in the parameters (see the unit tests
// Symbolic.* for the mode without ranges). Checked by certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>
CROSSCHECK_REALTIME int count(CROSSCHECK_RANGE(0, 1000) int n) { int s = 0; for (int i = 0; i < n; ++i) s++; return s; }
CROSSCHECK_REALTIME int upto30(CROSSCHECK_RANGE(-1000, 1000) int a) { int s = 0; while (a < 30) { a++; s++; } return s; }
CROSSCHECK_REALTIME int gap(CROSSCHECK_RANGE(0, 1000) int n, CROSSCHECK_RANGE(0, 1000) int m) { int s = 0; while (m < n) { m++; s++; } return s; }
CROSSCHECK_REALTIME int callgap(CROSSCHECK_RANGE(0, 100) int n) { return gap(n, 5) + upto30(n); }
