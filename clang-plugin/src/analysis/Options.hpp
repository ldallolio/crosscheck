// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_ANALYSIS_OPTIONS_HPP
#define CROSSCHECK_ANALYSIS_OPTIONS_HPP

#include <cstdint>
#include <string>

namespace crosscheck {

/// Weights of the abstract instruction classes (the cost norm of the paper:
/// a weighted trace length, Lean `wcost`). All default to 1.
struct CostModel {
  std::uint64_t arith = 1;    ///< arithmetic, logic, comparison operators
  std::uint64_t assign = 1;   ///< assignments, increments (stores)
  std::uint64_t memory = 1;   ///< array subscripts, pointer dereferences, `->`
  std::uint64_t call = 1;     ///< call overhead (callee cost is added)
  std::uint64_t branch = 1;   ///< every evaluated branch / loop test
  std::uint64_t ret = 1;      ///< return statements
  std::uint64_t convert = 1;  ///< int <-> floating-point conversions

  /// Sets a weight by class name; returns false for an unknown name.
  bool set(const std::string& name, std::uint64_t value) {
    if (name == "arith") arith = value;
    else if (name == "assign") assign = value;
    else if (name == "memory") memory = value;
    else if (name == "call") call = value;
    else if (name == "branch") branch = value;
    else if (name == "ret") ret = value;
    else if (name == "convert") convert = value;
    else return false;
    return true;
  }
};

struct Options {
  CostModel weights;
  /// Maximal number of symbolic paths kept through a loop body or function
  /// before they are joined.
  unsigned maxPaths = 16;
  /// When non-empty, a JSON report is written to this file.
  std::string reportPath;
  /// Analyse every function defined in the main file, not only annotated ones.
  bool analyzeAll = false;
  /// Entry function for the "in context" results of the report (qualified
  /// name). Empty: every analysed function that no analysed function calls.
  std::string entry;
  /// Emit a cost certificate for every analysed function that the certificate
  /// fragment covers (see docs/certificate-format.md); written by the tool and
  /// the plugin to `certificatesPath` when it is not empty.
  bool certificates = false;
  std::string certificatesPath;
  /// Loop bounds as flow facts for WCET tools (src/analysis/Export.hpp), written to
  /// `flowFactsPath` in `flowFactsFormat` ("ffx": OTAWA; "ais": aiT, AIS;
  /// "ais2": aiT, AIS2), with the bounds valid for every call or, with
  /// `flowFactsContext == "program"`, in the calling contexts of the program.
  std::string flowFactsPath;
  std::string flowFactsFormat;   ///< empty: from the file extension (.ais: ais2, else ffx)
  std::string flowFactsContext = "every-call";
  /// SARIF 2.1.0 log of the results (src/analysis/Export.hpp); file paths that start
  /// with `sarifBase` are written relative to it (uriBaseId %SRCROOT%).
  std::string sarifPath;
  std::string sarifBase;

  /// Parses one `name=value` option (`weight-arith=3`, `max-paths=8`,
  /// `report=out.json`, `all`). Returns false if it is not understood.
  bool parse(const std::string& arg) {
    if (arg == "all") { analyzeAll = true; return true; }
    auto eq = arg.find('=');
    if (eq == std::string::npos) return false;
    std::string key = arg.substr(0, eq), value = arg.substr(eq + 1);
    if (key == "report") { reportPath = value; return !value.empty(); }
    if (key == "entry") { entry = value; return !value.empty(); }
    if (key == "flowfacts") { flowFactsPath = value; return !value.empty(); }
    if (key == "flowfacts-format") {
      flowFactsFormat = value;
      return value == "ffx" || value == "ais" || value == "ais2";
    }
    if (key == "flowfacts-context") {
      flowFactsContext = value;
      return value == "every-call" || value == "program";
    }
    if (key == "sarif") { sarifPath = value; return !value.empty(); }
    if (key == "sarif-base") { sarifBase = value; return !value.empty(); }
    if (key == "certificates") {
      certificates = true;
      certificatesPath = value;
      return !value.empty();
    }
    if (value.empty() || value.find_first_not_of("0123456789") != std::string::npos ||
        value.size() > 18)
      return false;
    std::uint64_t n = std::stoull(value);
    if (key == "max-paths") { maxPaths = n == 0 ? 1 : static_cast<unsigned>(n); return true; }
    if (key.rfind("weight-", 0) == 0) return weights.set(key.substr(7), n);
    return false;
  }
};

}  // namespace crosscheck

#endif
