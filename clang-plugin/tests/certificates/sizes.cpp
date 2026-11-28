// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// Size facts (Lean `whileSz`, `sizeloop_sound`; Paper I `prop:size-facts`): a loop of at
// most N iterations in which a variable grows by at most h per iteration leaves it at most
// h*N above its value on entry, and at most h*(N-1) above at the start of every iteration.
// `after`: the second loop is bounded by the value of `y` that the first leaves (at most
// 300). `nested`: the inner loop is bounded by `x`, which the outer loop increases by 2
// per iteration (at most 100). Checked by the Lean checker in the ctest
// certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>
CROSSCHECK_REALTIME int after(CROSSCHECK_RANGE(0, 100) int x, CROSSCHECK_RANGE(0, 100) int y) {
  while (x > 0) { x--; y += 2; }
  while (y > 0) y--;
  return y;
}
CROSSCHECK_REALTIME int nested(CROSSCHECK_RANGE(0, 50) int n) {
  int x = 0, c = 0;
  for (int i = 0; i < n; i++) {
    x += 2;
    int y = 0;
    while (y < x) { y++; c++; }
  }
  return c;
}
