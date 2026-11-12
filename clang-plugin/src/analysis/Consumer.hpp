// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_ANALYSIS_CONSUMER_HPP
#define CROSSCHECK_ANALYSIS_CONSUMER_HPP

#include <memory>

#include "Options.hpp"
#include "Report.hpp"

namespace clang {
class ASTConsumer;
}

namespace crosscheck {

/// An AST consumer that runs the analysis at the end of the translation unit,
/// writes the JSON report if requested and, when `out` is non-null, stores the
/// structured report there.
std::unique_ptr<clang::ASTConsumer> makeConsumer(const Options& options, Report* out = nullptr);

}  // namespace crosscheck

#endif
