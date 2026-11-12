// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// REJECTED: a logging helper that looks harmless but allocates. The call to
// std::vector::push_back may reallocate, which takes an unbounded time in the
// allocator; CrossCheck follows the call into the standard library and
// reports the allocation, although no `new` appears in this file.
#include <vector>

#include <crosscheck/attributes.hpp>

namespace logging {

CROSSCHECK_REALTIME
void record_sample(std::vector<int>& history, int sample) {
  history.push_back(sample);  // may call operator new
}

}  // namespace logging
