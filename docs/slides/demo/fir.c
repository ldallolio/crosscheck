/* Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
   Released under the MIT license as described in the file LICENSE.

   The running example of the slides (docs/slides): an 8-tap FIR filter over a block of
   samples whose length is a parameter in [1, 56], with a time budget at 48 MHz. */
#include <crosscheck/attributes.hpp>

#define TAPS 8
int coeff[TAPS];
int window[64];

__attribute__((noinline)) int dot(int start) {
  int acc = 0;
  for (int k = 0; k < TAPS; k++)
    acc += coeff[k] * window[start + k];
  return acc;
}

CROSSCHECK_DEADLINE_US(500)
int fir_peak(CROSSCHECK_RANGE(1, 56) int n) {
  int peak = 0;
  for (int i = 0; i < n; i++) {
    int y = dot(i);
    if (y > peak) peak = y;
  }
  return peak;
}
