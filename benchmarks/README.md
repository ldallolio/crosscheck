# CrossCheck examples

Small, self-contained pieces of real-time code of the kind found in embedded
firmware, each annotated for the [CrossCheck plugin](../clang-plugin/README.md).
The header comment of every file says what the code does and what the analysis
establishes. They are checked by the plugin's test suite (`ctest`).

Run one yourself:

```bash
../clang-plugin/build/crosscheck-tool --summary fir_filter.cpp -- -std=c++20 -I../clang-plugin/include
```

## Accepted

Bounds are in abstract cost units with all weights equal to 1.

| File | Scenario | Function | Bound | How the bound is obtained |
|---|---|---|---:|---|
| `fir_filter.cpp` | 16-tap fixed-point FIR filter on a block of samples (audio / sensor ISR) | `dsp::fir_step` | 331 | tap loop: 16 iterations, derived |
| | | `dsp::fir_block` | 21 699 | block loop: 64 iterations from `CROSSCHECK_RANGE` |
| `pid_controller.cpp` | PID with clamping and anti-windup; four-axis attitude loop | `control::pid_step` | 19 | straight-line; worst branch of each clamp |
| | | `control::attitude_update` | 167 | axis loop: 4 iterations, derived |
| `divide_and_conquer.cpp` | recursive peak search, table lookup and merge sort on a 256-sample window | `reduce::range_max` | 7 154 | size potential `2·(hi−lo)−1`: 511 activations |
| | | `reduce::table_lookup` | 6 144 | linear recursion; depth bounded linearly (true depth is logarithmic) |
| | | `reduce::merge_sort` | 3 148 271 | 511 activations × worst-case merge (no amortisation: pessimistic) |
| `can_frame_decoder.cpp` | CAN frame decoding in an ECU receive interrupt | `can::payload_checksum` | 67 | 7 iterations, derived from the clamp of the untrusted length |
| | | `can::on_frame` | 119 | `switch` charged as the sum of its cases |
| `ring_buffer_isr.cpp` | UART receive ISR draining a hardware FIFO into a ring buffer | `serial::uart_rx_isr` | 309 | **assumed**: FIFO depth 16, cost of two register accessors |
| | | `serial::ring_read` | 838 | 64 iterations, derived from `n < max` |
| `crc_table.cpp` | bitwise CRC-32 of a telemetry packet | `telemetry::crc32` | 10 502 | nested loops 128 × 8, derived |
| `motor_ramp.cpp` | trapezoidal speed ramp of a stepper motor | `motion::plan_ramp` | 883 | 79 iterations: potential `(target − speed − accel)/50`, needs `accel ≥ 50` |
| | | `motion::next_phase` | 15 | `switch` state machine |

## Rejected (each file must fail to compile with the plugin)

| File | Why it is rejected |
|---|---|
| `rejected_allocation.cpp` | `std::vector::push_back` reaches `operator new`; reported once, at the call site |
| `rejected_unbounded_loop.cpp` | busy-wait on a device flag has no bound; the variant with a poll counter is accepted (1 010 units) |
| `rejected_deadline.cpp` | bounded (47 875 units) but over its deadline of 20 000 |

## Reading the results

- A bound is an upper bound on a count of abstract operations, not a time. It
  becomes a timing argument only with per-operation worst-case durations for a
  given target, which this project does not provide.
- "Derived" means a ranking potential was found and checked; "assumed" means the
  bound rests on an annotation that the tool cannot check. Assumptions are
  listed in the JSON report (`--report=out.json`).
- Several bounds are deliberately pessimistic (see `merge_sort`); the
  [limitations](../clang-plugin/README.md#limitations) explain why.
