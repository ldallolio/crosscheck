/* Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
 *
 * The annotations in C (crosscheck/attributes.hpp without C++): ranges, requirements,
 * trusted costs and loop bounds, globals, fields, tables and `while (--j)`.
 * Checked by tests/check_c.sh: each function's verdict must match its name (ok_ / bad_). */
#include <stdint.h>
#include <crosscheck/attributes.hpp>

CROSSCHECK_COST(5) int hal_ready(void);
static const uint8_t kLen[3] = {2, 9, 4};
int nbits;
typedef struct { uint16_t n; } inst_t;

CROSSCHECK_REALTIME int ok_range(const int* a, CROSSCHECK_RANGE(0, 16) int n) {
  CROSSCHECK_REQUIRE(n >= 0);
  int s = 0;
  for (int i = 0; i < n; i++) s += a[i];
  return s;
}
CROSSCHECK_REALTIME int ok_loop_bound(void) {
  int k = 0;
  while (hal_ready()) { CROSSCHECK_LOOP_BOUND(3); k++; }
  return k;
}
CROSSCHECK_REALTIME int ok_predecrement(CROSSCHECK_RANGE(1, 32) uint32_t n) {
  uint32_t j = n; int c = 0;
  do { c++; } while (--j);
  return c;
}
CROSSCHECK_REALTIME int ok_table(CROSSCHECK_RANGE(0, 2) int k) {
  int c = 0;
  for (int i = 0; i < kLen[k]; i++) c++;
  return c;
}
CROSSCHECK_REALTIME int ok_global(void) {
  int c = 0;
  nbits = 8;
  for (int i = 0; i < nbits; i++) c++;
  return c;
}
CROSSCHECK_REALTIME int bad_predecrement(CROSSCHECK_RANGE(0, 32) uint32_t n) {
  uint32_t j = n; int c = 0;
  while (--j) c++;
  return c;
}
