// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// The limits of every Z3 query (core/Solver.cpp, core/Cert.cpp).
//
// A query is limited by Z3's resource counter (`rlimit`, per query), so that its answer is
// the same on every machine and under any load. On TACLeBench (kernels and larger programs,
// 2026-11-27, Z3 5.1.0) the largest of about 416,000 queries used 187k units (0.06 s); the
// limit leaves a factor of about 270. With the limit alone, the analysis of `cosf` did not
// finish in 30 minutes with Ubuntu 24.04's Z3 4.8.12 (CI; it does with the timeouts), so the
// wall-clock timeout of 10 s stays as a backstop: a query stopped by it is counted (`solverTimeouts`, the report's `solver_timeouts`), since its answer may
// depend on the machine. An exhausted query answers "unknown", which every caller treats as
// "not proved". The queries that reached the backstop with 4.8.12 on TACLeBench were
// optimisations of an objective with a variable that no premise mentions, now answered without
// the optimiser (`boundsOf`); after that change no query of the kernels reaches it with either
// version. `CROSSCHECK_Z3_DUMP=DIR` writes each query it stops to DIR (SMT-LIB).
#pragma once
#include <unistd.h>
#include <z3++.h>

#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <string>

namespace crosscheck::z3limits {

constexpr unsigned kRlimit = 50000000;
constexpr unsigned kBackstopMs = 10000;

inline std::uint64_t& timeouts() {
  static thread_local std::uint64_t n = 0;
  return n;
}

inline void apply(z3::params& p) {
  p.set("rlimit", kRlimit);
  p.set("timeout", kBackstopMs);
}

inline std::string reasonUnknown(z3::solver& s) { return s.reason_unknown(); }
inline std::string reasonUnknown(z3::optimize& o) {
  return Z3_optimize_get_reason_unknown(o.ctx(), o);  // no member in z3++
}

inline std::string text(z3::solver& s) { return s.to_smt2(); }
inline std::string text(z3::optimize& o) { return Z3_optimize_to_string(o.ctx(), o); }

/// With `CROSSCHECK_Z3_DUMP=DIR`, each query stopped by the backstop is written to
/// DIR/query-<pid>-<n>.smt2 (diagnosis of slow queries; nothing else changes).
template <class S>
void dump(S& s) {
  static const char* dir = std::getenv("CROSSCHECK_Z3_DUMP");
  if (!dir) return;
  static thread_local unsigned n = 0;
  std::ofstream(std::string(dir) + "/query-" + std::to_string(::getpid()) + "-" + std::to_string(n++) + ".smt2")
      << text(s);
}

/// `s.check()`, counting a query that the backstop stopped.
template <class S>
z3::check_result check(S& s) {
  z3::check_result r = s.check();
  if (r == z3::unknown) {
    std::string why = reasonUnknown(s);
    if (why.find("timeout") != std::string::npos || why.find("canceled") != std::string::npos) {
      ++timeouts();
      dump(s);
    }
  }
  return r;
}

}  // namespace crosscheck::z3limits
