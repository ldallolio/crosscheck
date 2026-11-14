// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Outputs for other tools, computed from a Report (no Clang dependency):
//
// - flow facts for WCET analysers: the loop bounds the analysis derived, as
//   * FFX, the XML flow-fact format read by OTAWA and written by oRange
//     (Bonenfant et al., RTNS 2012): `<loop source=... line=... maxcount=.../>`
//     at top level of `<flowfacts>`, i.e. for every context of the loop;
//   * AIS / AIS2, the annotation languages of AbsInt's aiT
//     (`loop "f" + 1 loops max 10;` resp. `loop "f.L1" { bound: 0 .. 10; }`).
//     aiT numbers loops in the executable; we number them in source order, which
//     agrees only if the compiler keeps the loops of a function in that order and
//     does not inline or unroll them. The file says so; it was not validated with aiT.
//   The bound is the maximal number of executions of the loop body per entry of
//   the loop (the convention of the report, of the TACLeBench flow facts and of
//   oRange's FFX output). Bounds stated by annotations (CROSSCHECK_LOOP_BOUND) are
//   assumptions and are not exported.
// - SARIF 2.1.0, for code-scanning interfaces: rejections and missed deadlines as
//   errors, cost bounds and assumptions as notes.
#ifndef CROSSCHECK_ANALYSIS_EXPORT_HPP
#define CROSSCHECK_ANALYSIS_EXPORT_HPP

#include <string>

#include "Options.hpp"
#include "Report.hpp"

namespace crosscheck {

/// The format of `opts.flowFactsFormat`, or the one implied by the extension of
/// `opts.flowFactsPath` (".ais": ais2; otherwise ffx).
std::string flowFactsFormat(const Options& opts);

/// Flow facts in that format.
std::string toFlowFacts(const Report& report, const Options& opts);

/// SARIF 2.1.0 log.
std::string toSarif(const Report& report, const Options& opts);

}  // namespace crosscheck

#endif
