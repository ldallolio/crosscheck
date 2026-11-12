// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_ANALYSIS_REPORT_HPP
#define CROSSCHECK_ANALYSIS_REPORT_HPP

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace crosscheck {

struct LoopReport {
  unsigned line = 0;
  std::uint64_t bound = 0;  ///< maximal number of iterations
  /// True when the bound was derived from a synthesised ranking potential;
  /// false when it comes from a user annotation (an assumption).
  bool verified = false;
  std::string potential;    ///< the ranking potential, when synthesised
};

struct RecursionReport {
  std::uint64_t activations = 0;  ///< bound on the number of activations
  std::uint64_t branching = 0;    ///< maximal number of self-calls per activation
  std::optional<std::uint64_t> depth;  ///< bound on the recursion depth, if derived
  std::string potential;          ///< the potential the bound comes from
};

struct FunctionReport {
  std::string name;
  std::string file;
  unsigned line = 0;
  bool ok = false;          ///< profile respected, bound derived, deadline met
  bool bounded = false;     ///< a finite cost bound was derived
  std::uint64_t wcet = 0;   ///< worst-case cost bound in abstract units (if bounded)
  std::optional<std::uint64_t> deadline;
  std::vector<LoopReport> loops;
  std::optional<RecursionReport> recursion;
  std::vector<std::string> assumptions;  ///< everything trusted, not proved
  std::vector<std::string> errors;
};

struct Report {
  std::vector<FunctionReport> functions;

  const FunctionReport* find(const std::string& name) const {
    for (const FunctionReport& f : functions)
      if (f.name == name) return &f;
    return nullptr;
  }
  bool allOk() const {
    for (const FunctionReport& f : functions)
      if (!f.ok) return false;
    return true;
  }
  std::string toJson() const;
};

}  // namespace crosscheck

#endif
