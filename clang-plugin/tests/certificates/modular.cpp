// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Modular certificates: `sum` is certified once with a summary in its parameter `n`;
// its callers use it through call nodes, with bounds equal to the plugin's in-context
// bounds; `hal_read` (CROSSCHECK_COST) is an assumed contract.
#include <crosscheck/attributes.hpp>
CROSSCHECK_REALTIME int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += a[i];
  return s;
}
CROSSCHECK_REALTIME int twice(const int* a) {
  return sum(a, 10) + sum(a, 20);
}
CROSSCHECK_REALTIME int scaled(const int* a, CROSSCHECK_RANGE(0, 32) int m) {
  return sum(a, m);
}
CROSSCHECK_COST(25) int hal_read(int ch);
CROSSCHECK_REALTIME int poll_all(CROSSCHECK_RANGE(0, 4) int k) {
  int s = 0;
  for (int c = 0; c < k; c++) s += hal_read(c);
  return s;
}
