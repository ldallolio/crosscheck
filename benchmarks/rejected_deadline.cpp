// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// REJECTED: the code is bounded, but the bound does not fit the budget. A
// naive O(n^2) moving-average over a 256-sample window is placed in a handler
// with a budget of 20000 cost units; CrossCheck computes the product bound of
// the two loops and reports that the deadline is exceeded.
#include <crosscheck/attributes.hpp>

namespace filter {

constexpr int kWindow = 256;
constexpr int kWidth = 16;

CROSSCHECK_DEADLINE(20000)
void moving_average(const int* in, int* out) {
  for (int i = 0; i < kWindow; ++i) {
    int acc = 0;
    for (int k = 0; k < kWidth; ++k) {
      const int j = i - k;
      if (j >= 0) acc += in[j];
    }
    out[i] = acc / kWidth;
  }
}

}  // namespace filter
