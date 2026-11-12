// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Consumer.hpp"

#include <fstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/Diagnostic.h"

#include "Analyzer.hpp"

namespace crosscheck {

namespace {

class Consumer : public clang::ASTConsumer {
 public:
  Consumer(const Options& options, Report* out) : options_(options), out_(out) {}

  void HandleTranslationUnit(clang::ASTContext& context) override {
    clang::DiagnosticsEngine& diags = context.getDiagnostics();
    if (diags.hasErrorOccurred()) return;  // do not analyse ill-formed code
    Report report = analyzeTranslationUnit(context, options_);
    if (!options_.reportPath.empty()) {
      std::ofstream file(options_.reportPath);
      file << report.toJson();
      if (!file) {
        unsigned id = diags.getCustomDiagID(clang::DiagnosticsEngine::Error,
                                            "crosscheck: cannot write report '%0'");
        diags.Report(id) << options_.reportPath;
      }
    }
    if (out_) *out_ = std::move(report);
  }

 private:
  Options options_;
  Report* out_;
};

}  // namespace

std::unique_ptr<clang::ASTConsumer> makeConsumer(const Options& options, Report* out) {
  return std::make_unique<Consumer>(options, out);
}

}  // namespace crosscheck
