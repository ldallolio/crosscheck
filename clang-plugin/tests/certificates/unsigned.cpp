// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Unsigned counters: every function must get a certificate that the Lean checker
// accepts (tests/check_certificates.sh). The wrap-around branches of the stores are
// in the certificates and proved dead by the checker.
#include <cstddef>
#include <crosscheck/attributes.hpp>
static unsigned char table[36];
CROSSCHECK_REALTIME int xor_all(unsigned char mask) {
  unsigned char* p = &table[0];
  for (unsigned int i = 0; i < sizeof(table); ++i, ++p) *p ^= mask;
  return 0;
}
CROSSCHECK_REALTIME unsigned sum_u(const unsigned* a, CROSSCHECK_RANGE(0, 40) unsigned n) {
  unsigned s = 0;
  for (unsigned i = 0; i < n; i++) s += a[i];
  return s;
}
CROSSCHECK_REALTIME int count_down(CROSSCHECK_RANGE(1, 30) std::size_t n) {
  int c = 0;
  for (std::size_t i = n; i > 0; i--) c++;
  return c;
}
CROSSCHECK_REALTIME int bytes(CROSSCHECK_RANGE(0, 200) unsigned char n) {
  int c = 0;
  for (unsigned char k = 0; k < n; k++) c += 2;
  return c;
}
// The store `m = n - 1` wraps when n == 0: its havoc branch is live, and `m` is not
// needed for the bound.
CROSSCHECK_REALTIME int may_wrap(CROSSCHECK_RANGE(0, 10) unsigned n) {
  int c = 0;
  unsigned m = n - 1;
  for (unsigned i = 0; i < n; i++) c++;
  if (m < 5) c++;
  return c;
}
