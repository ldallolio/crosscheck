// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// UART receive interrupt that drains a hardware FIFO into a ring buffer. The
// loop condition reads a device register, so no bound can be derived from the
// code: the bound comes from the hardware (FIFO depth), and is written down as
// an explicit, reviewable assumption. The register accessors are declared
// with their cost because their bodies live in a vendor library.
//
// What CrossCheck proves: under the two stated assumptions the handler costs
// at most the reported bound. The assumptions are listed in the report, so a
// reviewer sees exactly what was trusted.
#include <cstdint>

#include <crosscheck/attributes.hpp>

namespace hal {
CROSSCHECK_COST(3) bool uart_rx_ready();        // reads the status register
CROSSCHECK_COST(3) std::uint8_t uart_rx_read(); // reads the data register
}  // namespace hal

namespace serial {

constexpr int kFifoDepth = 16;     // hardware receive FIFO
constexpr unsigned kCapacity = 64; // ring buffer, power of two

struct Ring {
  std::uint8_t data[kCapacity];
  unsigned head = 0;  // next write position
  unsigned tail = 0;  // next read position
  unsigned overruns = 0;
};

CROSSCHECK_DEADLINE(450)
void uart_rx_isr(Ring& r) {
  while (hal::uart_rx_ready()) {
    CROSSCHECK_LOOP_BOUND(kFifoDepth);  // at most one FIFO per interrupt
    const std::uint8_t byte = hal::uart_rx_read();
    const unsigned next = (r.head + 1) & (kCapacity - 1);
    if (next == r.tail) {
      ++r.overruns;  // buffer full: drop the byte
    } else {
      r.data[r.head] = byte;
      r.head = next;
    }
  }
}

/// Copies up to `max` received bytes to `out`; returns the number copied.
CROSSCHECK_REALTIME
unsigned ring_read(Ring& r, std::uint8_t* out, CROSSCHECK_RANGE(0, 64) unsigned max) {
  unsigned n = 0;
  while (n < max && r.tail != r.head) {
    out[n] = r.data[r.tail];
    r.tail = (r.tail + 1) & (kCapacity - 1);
    ++n;
  }
  return n;
}

}  // namespace serial
