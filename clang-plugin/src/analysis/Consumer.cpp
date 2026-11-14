// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Consumer.hpp"
#include "../core/Cert.hpp"
#include "Export.hpp"

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
    if (!options_.certificatesPath.empty() && !out_) {
      // Plugin: one file per translation unit (the tool combines its inputs itself).
      std::ofstream file(options_.certificatesPath);
      file << cert::fileJson(report.certificates);
      if (!file) {
        unsigned id = diags.getCustomDiagID(clang::DiagnosticsEngine::Error,
                                            "crosscheck: cannot write certificates '%0'");
        diags.Report(id) << options_.certificatesPath;
      }
    }
    if (!out_) {
      // Plugin: one file per translation unit (the tool combines its inputs itself).
      auto write = [&](const std::string& path, const std::string& text, const char* what) {
        if (path.empty()) return;
        std::ofstream file(path);
        file << text;
        if (!file) {
          unsigned id = diags.getCustomDiagID(clang::DiagnosticsEngine::Error, "crosscheck: cannot write %0 '%1'");
          diags.Report(id) << what << path;
        }
      };
      write(options_.flowFactsPath, toFlowFacts(report, options_), "flow facts");
      write(options_.sarifPath, toSarif(report, options_), "SARIF log");
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
