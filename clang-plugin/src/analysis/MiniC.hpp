// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
#pragma once

#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Expr.h>
#include <clang/AST/Stmt.h>

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace crosscheck::minic {

/// Where a function is in the certificate file: its number, and the variables of its
/// tracked integer parameters (the others are not listed). `plain` is false when its
/// certificate has logical variables other than those of its parameters (option
/// `symbolic`), which a mini-C call does not describe.
struct CalleeInfo {
  std::size_t index = 0;
  std::vector<std::pair<const clang::ParmVarDecl*, std::size_t>> params;
  bool plain = true;
};

/// What the exporter needs from the analysis: the variable numbering of the program
/// certificate (any injective numbering of non-aliased integer locals and parameters),
/// and the cost model. Neither the generator of certificates nor any analysis result is
/// used: the exporter reads the C syntax only.
struct Inputs {
  const std::map<const clang::VarDecl*, std::size_t>* vars = nullptr;
  std::function<std::uint64_t(const clang::Expr*)> costOf;  ///< the cost model
  std::uint64_t assign = 1, branch = 1, ret = 1;            ///< weights of the cost model
  /// Scratch variables of the certificate for this function: for a statement of the form
  /// `x = x / c`, keyed by its operand expression, the variable that receives the old
  /// value of `x`. The exporter uses an index only after checking that it is not a
  /// variable of `vars`: nothing else about them is trusted, and a wrong choice makes
  /// validation fail.
  std::map<const clang::Expr*, std::size_t> scratch;
  /// Ghost variables of the certificate for the jumps of this function, by name:
  /// `?break<d>` and `?continue<d>` for a loop at nesting depth `d` (0 for a loop that is
  /// in no other loop), `?case<s>` for a `switch` at `switch` nesting depth `s`,
  /// `?return` for a `return` inside a loop or `switch`. As for `scratch`, only the index
  /// is used, after checking that it is not a variable of `vars`; the checker refuses
  /// ghost variables that are named by the source or not fresh along a nesting path.
  std::function<std::optional<std::size_t>(const std::string&)> flag;
  /// The layout of the certificate file for a called function (none: it has no entry of
  /// its own, the exporter refuses the call). Only this layout is used; whether the
  /// certificate's program really calls it there is what validation checks.
  std::function<std::optional<CalleeInfo>(const clang::FunctionDecl*)> callee;
  /// `CROSSCHECK_REQUIRE(...)` markers (no code; their content is the precondition).
  std::function<bool(const clang::Stmt*)> isRequire;
};

/// The mini-C program of `def` (JSON `{"ret": r, "body": ...}`: the fragment `MiniC.JStmt`
/// of the Lean formalization, statements with `break`, `continue`, `return` and `switch`,
/// whose jump-free parts are `MiniC.MStmt`, and the return flag `r`), or the reason why
/// `def` is outside the fragment.
///
/// The translation is the trusted part of a validated certificate (theorem
/// `MiniC.validated_sound`), so it is meant to be read: it is syntactic, and every
/// construct it does not model exactly is either an unknown value (`other`: reads of
/// memory and of untracked variables, non-affine or possibly-wrapping arithmetic,
/// narrowing conversions), a statement that only costs (stores to memory or to untracked
/// variables), or a refusal (indirect calls, `goto`, `do` loops, aliased tracked
/// variables, ...). `break`, `continue`, `return` and `switch` are written as in C; their
/// meaning (`MiniC.JExec`) and their elimination with flag variables (`MiniC.elim`) are
/// in Lean, and the elimination is proved (`MiniC.validatedJ_sound`).
/// Signed arithmetic is exact: signed overflow is undefined behaviour, assumed absent.
struct Result {
  std::optional<std::string> json;
  std::string reason;
};
Result exportFunction(const clang::FunctionDecl* def, clang::ASTContext& ctx, const Inputs& in);

}  // namespace crosscheck::minic
