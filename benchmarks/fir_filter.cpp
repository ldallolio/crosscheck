// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Fixed-point FIR low-pass filter, as run in an audio or sensor-acquisition
// interrupt: each call filters one block of samples through a 16-tap filter
// with a circular delay line. No allocation, no floating point.
//
// What CrossCheck proves: the block loop runs at most 64 times, the tap loop
// exactly 16 times, and the whole call stays within the stated cost budget.
#include <array>
#include <cstdint>

#include <crosscheck/attributes.hpp>

namespace dsp {

constexpr int kTaps = 16;
constexpr int kMaxBlock = 64;

struct Fir {
  std::array<std::int16_t, kTaps> coeff{};  // Q15 coefficients
  std::array<std::int16_t, kTaps> delay{};  // circular delay line
  int head = 0;                             // index of the newest sample
};

/// Filters one sample (Q15 arithmetic with saturation).
CROSSCHECK_REALTIME
std::int16_t fir_step(Fir& f, std::int16_t x) {
  f.head = (f.head + 1) & (kTaps - 1);
  f.delay[f.head] = x;

  std::int32_t acc = 0;
  int idx = f.head;
  for (int k = 0; k < kTaps; ++k) {
    acc += static_cast<std::int32_t>(f.coeff[k]) * f.delay[idx];
    idx = (idx - 1) & (kTaps - 1);
  }
  acc >>= 15;
  if (acc > INT16_MAX) acc = INT16_MAX;
  if (acc < INT16_MIN) acc = INT16_MIN;
  return static_cast<std::int16_t>(acc);
}

/// Filters a block of `n` samples in place; called once per audio period.
CROSSCHECK_DEADLINE(22000)
void fir_block(Fir& f, std::int16_t* samples, CROSSCHECK_RANGE(0, kMaxBlock) int n) {
  for (int i = 0; i < n; ++i) samples[i] = fir_step(f, samples[i]);
}

}  // namespace dsp
