// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_ANALYSIS_ANALYZER_HPP
#define CROSSCHECK_ANALYSIS_ANALYZER_HPP

#include "Options.hpp"
#include "Report.hpp"

namespace clang {
class ASTContext;
}

namespace crosscheck {

/// Analyses every annotated function of the translation unit, emits Clang
/// diagnostics (errors for violations, remarks for derived bounds) and returns
/// the structured report.
Report analyzeTranslationUnit(clang::ASTContext& context, const Options& options);

}  // namespace crosscheck

#endif
