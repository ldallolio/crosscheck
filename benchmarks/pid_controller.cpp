// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// PID controller with output clamping and anti-windup, and a four-axis
// attitude loop that runs one PID per axis at a fixed rate (e.g. 1 kHz on a
// flight controller). The control law must finish within its period.
//
// What CrossCheck proves: straight-line cost of one PID step (the worst branch
// of every clamp is taken into account), and the bound of the axis loop from
// the fixed array extent.
#include <array>

#include <crosscheck/attributes.hpp>

namespace control {

struct Pid {
  float kp = 0, ki = 0, kd = 0;
  float integral = 0;
  float previous_error = 0;
  float out_min = -1, out_max = 1;
};

CROSSCHECK_REALTIME
float pid_step(Pid& c, float setpoint, float measured, float dt) {
  const float error = setpoint - measured;
  const float derivative = (error - c.previous_error) / dt;
  float integral = c.integral + error * dt;

  float out = c.kp * error + c.ki * integral + c.kd * derivative;
  if (out > c.out_max) {
    out = c.out_max;
    integral = c.integral;  // anti-windup: do not integrate while saturated
  } else if (out < c.out_min) {
    out = c.out_min;
    integral = c.integral;
  }
  c.integral = integral;
  c.previous_error = error;
  return out;
}

constexpr int kAxes = 4;  // roll, pitch, yaw, thrust

struct Attitude {
  std::array<Pid, kAxes> pid{};
  std::array<float, kAxes> setpoint{};
  std::array<float, kAxes> command{};
};

/// One control period: read the measurements, update every axis.
CROSSCHECK_DEADLINE(250)
void attitude_update(Attitude& a, const std::array<float, kAxes>& measured, float dt) {
  for (int axis = 0; axis < kAxes; ++axis)
    a.command[axis] = pid_step(a.pid[axis], a.setpoint[axis], measured[axis], dt);
}

}  // namespace control
