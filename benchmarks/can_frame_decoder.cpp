// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Decoding of CAN bus frames in an automotive ECU receive interrupt. The data
// length code (DLC) comes from the bus, so it is untrusted input: the decoder
// clamps it before using it as a loop bound.
//
// What CrossCheck proves: because of the clamp, the payload loop runs at most
// 8 times whatever the frame contains; the dispatch `switch` costs at most the
// sum of its cases; the handler meets its budget.
#include <cstdint>

#include <crosscheck/attributes.hpp>

namespace can {

struct Frame {
  std::uint32_t id;
  std::uint8_t dlc;      // 0..15 on the wire; only 0..8 are valid payload sizes
  std::uint8_t data[8];
};

struct VehicleState {
  std::uint16_t engine_rpm = 0;
  std::uint16_t wheel_speed[4] = {0, 0, 0, 0};
  std::uint8_t checksum_errors = 0;
};

/// XOR checksum over the payload (last byte excluded).
CROSSCHECK_REALTIME
std::uint8_t payload_checksum(const Frame& f) {
  int len = f.dlc & 0x0F;
  if (len > 8) len = 8;  // clamp untrusted input
  std::uint8_t sum = 0;
  for (int i = 0; i + 1 < len; ++i) sum ^= f.data[i];
  return sum;
}

CROSSCHECK_DEADLINE(150)
void on_frame(VehicleState& v, const Frame& f) {
  if ((f.dlc & 0x0F) == 0) return;
  if (payload_checksum(f) != f.data[(f.dlc & 0x07) == 0 ? 7 : (f.dlc & 0x07) - 1]) {
    ++v.checksum_errors;
    return;
  }
  switch (f.id) {
    case 0x0C0:  // engine speed, big endian
      v.engine_rpm = static_cast<std::uint16_t>((f.data[0] << 8) | f.data[1]);
      break;
    case 0x1A0:  // four wheel speeds, one byte each
      for (int w = 0; w < 4; ++w) v.wheel_speed[w] = f.data[w];
      break;
    default:
      break;  // unknown identifiers are ignored
  }
}

}  // namespace can
