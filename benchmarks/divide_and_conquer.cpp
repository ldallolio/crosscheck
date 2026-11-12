// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Recursive algorithms on a bounded buffer, as found in on-board data
// reduction (peak detection, lookup in calibration tables, sorting a window of
// measurements). Recursion is usually banned in real-time code because its
// depth and work are hard to bound by review; here the bounds are derived.
//
// What CrossCheck proves:
//  * range_max: at most 2*(hi - lo) - 1 activations (a size potential), so the
//    cost is linear in the window although the recursion branches;
//  * table_lookup: linear recursion, depth bounded by the table size;
//  * merge_sort: the same size potential, with the merge loop bounded by the
//    window size.
#include <crosscheck/attributes.hpp>

namespace reduce {

constexpr int kWindow = 256;

/// Maximum of samples[lo, hi) by halving the range.
CROSSCHECK_REALTIME
int range_max(const int* samples, CROSSCHECK_RANGE(0, kWindow) int lo,
              CROSSCHECK_RANGE(0, kWindow) int hi) {
  CROSSCHECK_REQUIRE(lo < hi);
  if (hi - lo <= 1) return samples[lo];
  const int mid = lo + (hi - lo) / 2;
  const int left = range_max(samples, lo, mid);
  const int right = range_max(samples, mid, hi);
  return left > right ? left : right;
}

/// Index of the first calibration point not below `key`, in table[lo, hi).
CROSSCHECK_REALTIME
int table_lookup(const int* table, int key, CROSSCHECK_RANGE(0, kWindow) int lo,
                 CROSSCHECK_RANGE(0, kWindow) int hi) {
  CROSSCHECK_REQUIRE(lo <= hi);
  if (lo == hi) return lo;
  const int mid = lo + (hi - lo) / 2;
  if (table[mid] < key) return table_lookup(table, key, mid + 1, hi);
  return table_lookup(table, key, lo, mid);
}

/// Sorts data[lo, hi) using `scratch` as a work buffer of the same size.
CROSSCHECK_REALTIME
void merge_sort(int* data, int* scratch, CROSSCHECK_RANGE(0, kWindow) int lo,
                CROSSCHECK_RANGE(0, kWindow) int hi) {
  CROSSCHECK_REQUIRE(lo < hi);
  if (hi - lo <= 1) return;
  const int mid = lo + (hi - lo) / 2;
  merge_sort(data, scratch, lo, mid);
  merge_sort(data, scratch, mid, hi);

  int i = lo, j = mid;
  for (int k = lo; k < hi; ++k) {
    if (i < mid && (j >= hi || data[i] <= data[j]))
      scratch[k] = data[i++];
    else
      scratch[k] = data[j++];
  }
  for (int k = lo; k < hi; ++k) data[k] = scratch[k];
}

}  // namespace reduce
