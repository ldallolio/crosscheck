/* Time budgets checked after compilation (scripts/crosscheck_link.py): functions named
   ok_* must meet their budget on a Cortex-M0, those named no_* must not. */
#include <crosscheck/attributes.hpp>
int buf[64];
CROSSCHECK_DEADLINE_CYCLES(5000) int ok_sum(void) {
  int s = 0;
  for (int i = 0; i < 64; i++) s += buf[i];
  return s;
}
CROSSCHECK_DEADLINE_US(100) int ok_sum_us(void) {
  int s = 0;
  for (int i = 0; i < 64; i++) s += buf[i];
  return s;
}
CROSSCHECK_DEADLINE_US(1) int no_too_slow(void) {
  int s = 0;
  for (int i = 0; i < 64; i++) s += buf[i];
  return s;
}
