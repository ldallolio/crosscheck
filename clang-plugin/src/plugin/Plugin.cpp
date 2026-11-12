// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Clang plugin entry point.
//
//   clang++ -fplugin=libCrossCheckPlugin.so file.cpp
//   clang++ -fplugin=libCrossCheckPlugin.so
//           -fplugin-arg-crosscheck-report=out.json
//           -fplugin-arg-crosscheck-weight-memory=3 file.cpp
//
// The analysis runs before code generation; a violation is a compile error.
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"

#include "../analysis/Consumer.hpp"

namespace {

class CrossCheckAction : public clang::PluginASTAction {
 protected:
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance&,
                                                        llvm::StringRef) override {
    return crosscheck::makeConsumer(options_);
  }

  bool ParseArgs(const clang::CompilerInstance& ci, const std::vector<std::string>& args) override {
    for (const std::string& arg : args) {
      if (options_.parse(arg)) continue;
      clang::DiagnosticsEngine& diags = ci.getDiagnostics();
      unsigned id = diags.getCustomDiagID(clang::DiagnosticsEngine::Error,
                                          "crosscheck: unknown plugin argument '%0'");
      diags.Report(id) << arg;
      return false;
    }
    return true;
  }

  ActionType getActionType() override { return AddBeforeMainAction; }

 private:
  crosscheck::Options options_;
};

}  // namespace

static clang::FrontendPluginRegistry::Add<CrossCheckAction> registration(
    "crosscheck", "CrossCheck: real-time profile and worst-case cost bounds");
