// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// The example programs of benchmarks/ must be accepted (or rejected) for the
// reasons their header comments state.
#include <gtest/gtest.h>

#include <fstream>
#include <sstream>

#include "test_support.hpp"

using namespace crosscheck;
using crosscheck::testing::anyAssumptionContains;
using crosscheck::testing::anyErrorContains;

namespace {

Report benchmark(const std::string& name) {
  std::ifstream in(std::string(CROSSCHECK_BENCHMARK_DIR) + "/" + name);
  EXPECT_TRUE(in.good()) << "cannot read benchmark " << name;
  std::stringstream text;
  text << in.rdbuf();
  return crosscheck::testing::analyze(text.str(), {}, name);
}

const FunctionReport& fn(const Report& r, const char* name) {
  const FunctionReport* f = r.find(name);
  EXPECT_NE(f, nullptr) << "no report for " << name;
  static const FunctionReport empty;
  return f ? *f : empty;
}

TEST(Benchmarks, FirFilter) {
  Report r = benchmark("fir_filter.cpp");
  EXPECT_TRUE(r.allOk());
  EXPECT_EQ(fn(r, "dsp::fir_step").loops.at(0).bound, 16u);
  EXPECT_EQ(fn(r, "dsp::fir_block").loops.at(0).bound, 64u);
  EXPECT_LE(fn(r, "dsp::fir_block").wcet, *fn(r, "dsp::fir_block").deadline);
  // The block costs 64 filter steps plus loop overhead.
  EXPECT_GE(fn(r, "dsp::fir_block").wcet, 64 * fn(r, "dsp::fir_step").wcet);
}

TEST(Benchmarks, PidController) {
  Report r = benchmark("pid_controller.cpp");
  EXPECT_TRUE(r.allOk());
  EXPECT_TRUE(fn(r, "control::pid_step").loops.empty());
  EXPECT_EQ(fn(r, "control::pid_step").wcet, 19u);
  EXPECT_EQ(fn(r, "control::attitude_update").loops.at(0).bound, 4u);
  EXPECT_TRUE(fn(r, "control::attitude_update").assumptions.empty());
}

TEST(Benchmarks, DivideAndConquer) {
  Report r = benchmark("divide_and_conquer.cpp");
  EXPECT_TRUE(r.allOk());
  const FunctionReport& rm = fn(r, "reduce::range_max");
  ASSERT_TRUE(rm.recursion.has_value());
  EXPECT_EQ(rm.recursion->activations, 511u);  // 2 * 256 - 1: linear, not exponential
  const FunctionReport& tl = fn(r, "reduce::table_lookup");
  ASSERT_TRUE(tl.recursion.has_value());
  EXPECT_EQ(tl.recursion->branching, 1u);
  const FunctionReport& ms = fn(r, "reduce::merge_sort");
  ASSERT_TRUE(ms.recursion.has_value());
  EXPECT_EQ(ms.recursion->activations, 511u);
  EXPECT_EQ(ms.loops.size(), 2u);
}

TEST(Benchmarks, CanFrameDecoder) {
  Report r = benchmark("can_frame_decoder.cpp");
  EXPECT_TRUE(r.allOk());
  const FunctionReport& cs = fn(r, "can::payload_checksum");
  EXPECT_EQ(cs.loops.at(0).bound, 7u);  // from the clamp, not from an assumption
  EXPECT_TRUE(cs.loops.at(0).verified);
  EXPECT_TRUE(cs.assumptions.empty());
}

TEST(Benchmarks, RingBufferIsr) {
  Report r = benchmark("ring_buffer_isr.cpp");
  EXPECT_TRUE(r.allOk());
  const FunctionReport& isr = fn(r, "serial::uart_rx_isr");
  EXPECT_FALSE(isr.loops.at(0).verified);
  EXPECT_TRUE(anyAssumptionContains(isr, "runs at most 16 times"));
  EXPECT_TRUE(anyAssumptionContains(isr, "uart_rx_ready"));
  EXPECT_EQ(fn(r, "serial::ring_read").loops.at(0).bound, 64u);
  EXPECT_TRUE(fn(r, "serial::ring_read").loops.at(0).verified);
}

TEST(Benchmarks, Crc) {
  Report r = benchmark("crc_table.cpp");
  EXPECT_TRUE(r.allOk());
  const FunctionReport& crc = fn(r, "telemetry::crc32");
  ASSERT_EQ(crc.loops.size(), 2u);
  EXPECT_EQ(crc.loops[0].bound, 128u);
  EXPECT_EQ(crc.loops[1].bound, 8u);
}

TEST(Benchmarks, MotorRamp) {
  Report r = benchmark("motor_ramp.cpp");
  EXPECT_TRUE(r.allOk());
  EXPECT_EQ(fn(r, "motion::plan_ramp").loops.at(0).bound, 79u);
  EXPECT_TRUE(fn(r, "motion::next_phase").loops.empty());
}

TEST(Benchmarks, AllocationIsRejected) {
  Report r = benchmark("rejected_allocation.cpp");
  const FunctionReport& f = fn(r, "logging::record_sample");
  EXPECT_FALSE(f.ok);
  EXPECT_EQ(f.errors.size(), 1u);  // one message at the call site, not a cascade
  EXPECT_TRUE(anyErrorContains(f, "push_back"));
  EXPECT_TRUE(anyErrorContains(f, "dynamic allocation"));
}

TEST(Benchmarks, UnboundedLoopIsRejected) {
  Report r = benchmark("rejected_unbounded_loop.cpp");
  EXPECT_FALSE(fn(r, "adc::wait_ready").ok);
  EXPECT_TRUE(fn(r, "adc::wait_ready_ok").ok);
  EXPECT_EQ(fn(r, "adc::wait_ready_ok").loops.at(0).bound, 100u);
}

TEST(Benchmarks, DeadlineIsRejected) {
  Report r = benchmark("rejected_deadline.cpp");
  const FunctionReport& f = fn(r, "filter::moving_average");
  EXPECT_FALSE(f.ok);
  EXPECT_TRUE(f.bounded);
  EXPECT_GT(f.wcet, *f.deadline);
}

}  // namespace
