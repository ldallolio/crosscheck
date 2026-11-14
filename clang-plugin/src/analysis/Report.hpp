// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_ANALYSIS_REPORT_HPP
#define CROSSCHECK_ANALYSIS_REPORT_HPP

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace crosscheck {

struct LoopReport {
  std::string file;         ///< source file of the loop keyword (as the compiler names it)
  unsigned line = 0;
  unsigned column = 0;
  std::uint64_t bound = 0;  ///< maximal number of iterations
  /// True when the bound was derived from a synthesised ranking potential;
  /// false when it comes from a user annotation (an assumption).
  bool verified = false;
  std::string potential;    ///< the ranking potential, when synthesised
  /// Largest bound over the calling contexts in which the program uses the
  /// function, when the loop is bounded in all of them (see FunctionReport).
  std::optional<std::uint64_t> inContext;
};

struct RecursionReport {
  std::uint64_t activations = 0;  ///< bound on the number of activations
  std::uint64_t branching = 0;    ///< maximal number of self-calls per activation
  std::optional<std::uint64_t> depth;  ///< bound on the recursion depth, if derived
  std::string potential;          ///< the potential the bound comes from
};

/// A diagnostic with its location, for machine-readable outputs (SARIF).
struct Site {
  std::string rule;  ///< "rejected" (profile or bound) or "deadline"
  std::string file;
  unsigned line = 0, column = 0;
  std::string message;
};

struct FunctionReport {
  std::string name;
  std::string symbol;       ///< linker (mangled) name
  std::string file;
  unsigned line = 0;
  bool ok = false;          ///< profile respected, bound derived, deadline met
  bool bounded = false;     ///< a finite cost bound was derived
  std::uint64_t wcet = 0;   ///< worst-case cost bound in abstract units (if bounded)
  std::optional<std::uint64_t> deadline;
  std::vector<LoopReport> loops;
  std::optional<RecursionReport> recursion;
  /// "In context": the function analysed with the argument intervals of the
  /// call sites through which the entry functions reach it. `wcet`, `bounded`
  /// and the loops' `bound` hold for every call that meets the preconditions;
  /// the in-context values only for the program as analysed.
  bool reachable = false;
  unsigned contexts = 0;  ///< number of analyses (contexts) that reach it
  std::optional<std::uint64_t> wcetInContext;
  /// Certificate: "emitted", or why none was produced (empty: not requested).
  std::string certificate;
  std::optional<std::uint64_t> certificateBound;  ///< the bound the certificate proves
  std::vector<std::string> assumptions;  ///< everything trusted, not proved
  std::vector<std::string> errors;
  std::vector<Site> errorSites;  ///< the errors with their locations
};

struct Report {
  std::vector<FunctionReport> functions;
  /// Certificates in the JSON format of `cert::toJson` (one per emitted function).
  std::vector<std::string> certificates;

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

/// `s` as a JSON string literal (with quotes).
std::string jsonQuote(const std::string& s);

}  // namespace crosscheck

#endif
