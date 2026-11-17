/* See time_budget_lib.c: ok_* must meet their budget, no_* must not (Cortex-M0, 48 MHz). */
#include <crosscheck/attributes.hpp>
int sum_row(int i);
CROSSCHECK_DEADLINE_US(500) int ok_frame(void) {
  int s = 0;
  for (int i = 0; i < 16; i++) s += sum_row(i);
  return s;
}
CROSSCHECK_DEADLINE_CYCLES(100) int no_frame_fast(void) {
  int s = 0;
  for (int i = 0; i < 16; i++) s += sum_row(i);
  return s;
}
