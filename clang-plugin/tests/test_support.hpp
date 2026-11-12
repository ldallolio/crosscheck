// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#ifndef CROSSCHECK_TESTS_SUPPORT_HPP
#define CROSSCHECK_TESTS_SUPPORT_HPP

#include <sstream>
#include <string>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

#include "analysis/Consumer.hpp"

namespace crosscheck::testing {

/// Runs the analyser on a piece of C++ source and returns its report.
inline Report analyze(const std::string& code, const Options& options = {},
                      const std::string& fileName = "input.cpp") {
  class Action : public clang::ASTFrontendAction {
   public:
    Action(const Options& o, Report* r) : options_(o), report_(r) {}
    std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance&,
                                                          llvm::StringRef) override {
      return makeConsumer(options_, report_);
    }

   private:
    Options options_;
    Report* report_;
  };

  std::vector<std::string> args = {"-std=c++20", "-I" CROSSCHECK_INCLUDE_DIR,
                                   "-resource-dir=" CROSSCHECK_RESOURCE_DIR};
  std::istringstream extra(CROSSCHECK_CLANG_EXTRA_FLAGS);
  for (std::string flag; extra >> flag;) args.push_back(flag);

  Report report;
  clang::tooling::runToolOnCodeWithArgs(std::make_unique<Action>(options, &report), code, args,
                                        fileName);
  return report;
}

/// Same, with the annotation header already included.
inline Report check(const std::string& code, const Options& options = {}) {
  return analyze("#include <crosscheck/attributes.hpp>\n" + code, options);
}

inline bool anyErrorContains(const FunctionReport& f, const std::string& text) {
  for (const std::string& e : f.errors)
    if (e.find(text) != std::string::npos) return true;
  return false;
}

inline bool anyAssumptionContains(const FunctionReport& f, const std::string& text) {
  for (const std::string& a : f.assumptions)
    if (a.find(text) != std::string::npos) return true;
  return false;
}

}  // namespace crosscheck::testing

#endif
