// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Stepper-motor motion planning: a trapezoidal speed ramp is pre-computed in a
// fixed table before the move starts, inside the real-time task that accepts
// motion commands. The number of ramp steps depends on the requested speed
// and on the acceleration, both of which are command parameters.
//
// What CrossCheck proves: with a target speed in [0, 4000] steps/s and an
// acceleration of at least 50 steps/s per table entry, the ramp loop runs at
// most 80 times. The synthesised potential is (target - speed) / 50: each
// iteration adds `accel >= 50` to the speed, so the potential drops by at
// least 1. Without the lower bound on `accel` the loop would be rejected.
#include <crosscheck/attributes.hpp>

namespace motion {

constexpr int kMaxSpeed = 4000;  // steps per second
constexpr int kMinAccel = 50;    // steps per second, per ramp entry
constexpr int kRampSize = 96;

struct Ramp {
  int speed[kRampSize];
  int length = 0;
};

enum class Phase { Idle, Accelerating, Cruising, Decelerating };

CROSSCHECK_DEADLINE(1500)
void plan_ramp(Ramp& ramp, CROSSCHECK_RANGE(0, kMaxSpeed) int target,
               CROSSCHECK_RANGE(kMinAccel, 1000) int accel) {
  int speed = 0;
  int n = 0;
  while (speed + accel < target) {  // full acceleration steps
    speed += accel;
    if (n < kRampSize) ramp.speed[n] = speed;
    ++n;
  }
  if (n < kRampSize) ramp.speed[n] = target;  // last, partial step
  ++n;
  ramp.length = n < kRampSize ? n : kRampSize;
}

/// Phase transition executed at every step interrupt.
CROSSCHECK_DEADLINE(30)
Phase next_phase(Phase phase, int position, CROSSCHECK_RANGE(0, kRampSize) int ramp_length,
                 int total_steps) {
  switch (phase) {
    case Phase::Idle:
      return total_steps > 0 ? Phase::Accelerating : Phase::Idle;
    case Phase::Accelerating:
      if (position >= ramp_length) return Phase::Cruising;
      return phase;
    case Phase::Cruising:
      if (position >= total_steps - ramp_length) return Phase::Decelerating;
      return phase;
    case Phase::Decelerating:
      return position >= total_steps ? Phase::Idle : phase;
  }
  return Phase::Idle;
}

}  // namespace motion
