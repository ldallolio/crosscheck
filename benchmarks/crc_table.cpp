// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// CRC-32 of a telemetry packet, bit by bit (no lookup table, as on small
// microcontrollers where 1 KiB of table is too much). Two nested loops: bytes
// of the packet, then the 8 bits of each byte.
//
// What CrossCheck proves: the outer loop is bounded by the maximal packet
// length, the inner loop by 8, and the cost is their product; the data-
// dependent branch in the inner loop is charged at its most expensive side.
#include <cstddef>
#include <cstdint>

#include <crosscheck/attributes.hpp>

namespace telemetry {

constexpr std::size_t kMaxPacket = 128;

CROSSCHECK_DEADLINE(11000)
std::uint32_t crc32(const std::uint8_t* packet, CROSSCHECK_RANGE(0, kMaxPacket) std::size_t length) {
  std::uint32_t crc = 0xFFFFFFFFu;
  for (std::size_t i = 0; i < length; ++i) {
    crc ^= packet[i];
    for (int bit = 0; bit < 8; ++bit) {
      if (crc & 1u)
        crc = (crc >> 1) ^ 0xEDB88320u;
      else
        crc >>= 1;
    }
  }
  return ~crc;
}

}  // namespace telemetry
