// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// Lexicographic arguments with a bounded inner counter: the combined potential
// V1 (K2 + 1) + V2 is affine, so the certificates use the ordinary while node; the
// invariants bounding the inner counter come from the analysis as candidates and are
// re-proved by the generator. Checked by the Lean checker in the ctest
// certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>
CROSSCHECK_COST(1) int nd(void);
CROSSCHECK_REALTIME int reset(CROSSCHECK_RANGE(0,100) int n, CROSSCHECK_RANGE(0,50) int m) {
  int i = 0, j = 0, c = 0;
  while (i < n) { if (j < m) j++; else { j = 0; i++; } c++; }
  return c;
}
CROSSCHECK_REALTIME int reset_const(CROSSCHECK_RANGE(0,100) int n) {
  int i = 0, j = 0, c = 0;
  while (i < n) { if (j < 50) j++; else { j = 0; i++; } c++; }
  return c;
}
CROSSCHECK_REALTIME int refill(CROSSCHECK_RANGE(0,100) int x, CROSSCHECK_RANGE(0,50) int y) {
  int c = 0;
  while (x > 0 && y > 0) { if (nd()) x--; else { y--; x = 100; } c++; }
  return c;
}
CROSSCHECK_REALTIME int twophase(CROSSCHECK_RANGE(0,100) int x, CROSSCHECK_RANGE(0,50) int y) {
  int c = 0;
  while (x > 0) { if (y > 0) y--; else x--; c++; }
  return c;
}
CROSSCHECK_REALTIME int down_up(CROSSCHECK_RANGE(0,100) int n) {
  int i = n, j = 0, c = 0;
  while (i > 0) { if (j > 0) j--; else { i--; j = i; } c++; }
  return c;
}
