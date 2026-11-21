// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// A control step preempted by two interrupt handlers: the report gives its response time
// under their interference, and the certificate file a response-time claim that the
// checker verifies from the certified bounds (Lean Interrupts.rtaHolds_sound).
#include <crosscheck/attributes.hpp>

int samples[16];
int ticks;

CROSSCHECK_INTERRUPT(500)
void timer_isr() {
  ticks = ticks + 1;
}

CROSSCHECK_INTERRUPT(2000)
void adc_isr() {
  for (int i = 0; i < 16; i++) samples[i] = 0;
}

CROSSCHECK_DEADLINE(3000)
int control_step() {
  int acc = 0;
  for (int i = 0; i < 16; i++) acc += samples[i];
  for (int k = 0; k < 100; k++) acc = acc - 1;
  return acc;
}
