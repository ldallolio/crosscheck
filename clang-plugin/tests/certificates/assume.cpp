// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// A trusted assumption (CROSSCHECK_ASSUME, listed in the report's assumptions) becomes the
// certificate node `assume`: the state is kept and the executions in which the assumption
// fails are blocked (Lean `check`, case `assume`; example `assumeCert_exec`). The bound
// holds for the executions that satisfy the assumption. Checked by the Lean checker in the
// ctest certificates_accepted_by_lean_checker.
#include <crosscheck/attributes.hpp>
CROSSCHECK_COST(1) int read_input(void);
CROSSCHECK_REALTIME int count_input(void) {
  int n = read_input();
  CROSSCHECK_ASSUME(0 <= n && n <= 100);
  int c = 0;
  while (n > 0) { n--; c++; }
  return c;
}
