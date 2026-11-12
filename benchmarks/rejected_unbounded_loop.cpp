// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// REJECTED: waiting for a peripheral with a busy loop. Nothing in the code
// bounds the number of polls (the device may never become ready), so no
// worst-case cost exists. The fix is a timeout counter, as in `wait_ready_ok`.
#include <crosscheck/attributes.hpp>

namespace hal {
CROSSCHECK_COST(3) bool adc_ready();
}

namespace adc {

CROSSCHECK_REALTIME
void wait_ready() {
  while (!hal::adc_ready()) {
    // spin
  }
}

/// The accepted variant: gives up after a fixed number of polls.
CROSSCHECK_REALTIME
bool wait_ready_ok() {
  for (int polls = 0; polls < 100; ++polls)
    if (hal::adc_ready()) return true;
  return false;
}

}  // namespace adc
