// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Standalone driver:
//
//   crosscheck-tool [--report=out.json] [--all] [--opt=weight-memory=3] file.cpp -- -std=c++20 -Iinclude
//
// Exit status 0 when every analysed function is accepted, 1 otherwise.
#include "../core/Cert.hpp"
#include <iostream>

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

#include "../analysis/Consumer.hpp"
#include "../analysis/Export.hpp"

namespace {

llvm::cl::OptionCategory category("crosscheck options");
llvm::cl::opt<std::string> reportPath("report", llvm::cl::desc("write a JSON report to this file"),
                                      llvm::cl::cat(category));
llvm::cl::opt<bool> analyzeAll("all", llvm::cl::desc("analyse every function of the main file"),
                               llvm::cl::cat(category));
llvm::cl::opt<bool> summary("summary", llvm::cl::desc("print a one-line summary per function"),
                            llvm::cl::cat(category));
llvm::cl::list<std::string> extra("opt", llvm::cl::desc("analysis option, e.g. weight-memory=3"),
                                  llvm::cl::cat(category));

crosscheck::Options options;
crosscheck::Report combined;

class Action : public clang::ASTFrontendAction {
 public:
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance&,
                                                        llvm::StringRef) override {
    return crosscheck::makeConsumer(options, &last_);
  }
  void EndSourceFileAction() override {
    for (auto& f : last_.functions) combined.functions.push_back(std::move(f));
    for (auto& c : last_.certificates) combined.certificates.push_back(std::move(c));
    last_.functions.clear();
    last_.certificates.clear();
  }

 private:
  crosscheck::Report last_;
};

}  // namespace

int main(int argc, const char** argv) {
  auto parser = clang::tooling::CommonOptionsParser::create(argc, argv, category);
  if (!parser) {
    llvm::errs() << llvm::toString(parser.takeError()) << "\n";
    return 2;
  }
  options.analyzeAll = analyzeAll;
  for (const std::string& o : extra)
    if (!options.parse(o)) {
      llvm::errs() << "crosscheck-tool: unknown option '" << o << "'\n";
      return 2;
    }

  clang::tooling::ClangTool tool(parser->getCompilations(), parser->getSourcePathList());
  tool.appendArgumentsAdjuster(clang::tooling::getInsertArgumentAdjuster(
      "-resource-dir=" CROSSCHECK_RESOURCE_DIR, clang::tooling::ArgumentInsertPosition::BEGIN));
  int status = tool.run(clang::tooling::newFrontendActionFactory<Action>().get());

  if (!reportPath.empty()) {
    std::error_code ec;
    llvm::raw_fd_ostream out(reportPath, ec);
    if (ec) {
      llvm::errs() << "crosscheck-tool: cannot write '" << reportPath << "'\n";
      return 2;
    }
    out << combined.toJson();
  }
  if (!options.certificatesPath.empty()) {
    std::error_code ec;
    llvm::raw_fd_ostream out(options.certificatesPath, ec);
    if (ec) {
      llvm::errs() << "crosscheck-tool: cannot write '" << options.certificatesPath << "'\n";
      return 2;
    }
    out << crosscheck::cert::fileJson(combined.certificates);
  }
  auto write = [](const std::string& path, const std::string& text) {
    if (path.empty()) return true;
    std::error_code ec;
    llvm::raw_fd_ostream out(path, ec);
    if (ec) {
      llvm::errs() << "crosscheck-tool: cannot write '" << path << "'\n";
      return false;
    }
    out << text;
    return true;
  };
  if (!options.flowFactsPath.empty() && !write(options.flowFactsPath, crosscheck::toFlowFacts(combined, options)))
    return 2;
  if (!options.sarifPath.empty() && !write(options.sarifPath, crosscheck::toSarif(combined, options))) return 2;
  if (summary)
    for (const auto& f : combined.functions)
      llvm::outs() << (f.ok ? "OK   " : "FAIL ") << f.name << ": "
                   << (f.bounded ? std::to_string(f.wcet) + " units" : std::string("no bound"))
                   << (f.responseTime ? ", response time " + std::to_string(*f.responseTime) +
                                            " under interrupts"
                                      : std::string())
                   << (f.interruptHandler ? " (interrupt handler)" : "") << "\n";
  return (status == 0 && combined.allOk()) ? 0 : 1;
}
