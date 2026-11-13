// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// The CrossCheck analyser: a symbolic walk over the Clang AST of annotated
// functions that
//   * enforces the real-time profile,
//   * computes a worst-case cost envelope with the tropical (max,+) rules
//     (sequence = sum, branch = max, loop = bound * body),
//   * bounds loops and recursion with affine ranking potentials synthesised by
//     Z3 through Farkas' Lemma.
//
// Extensional layer: program variables are mapped to affine expressions over
// immutable symbols (`State::val`), and path conditions are linear facts over
// those symbols (`State::facts`). A fact, once established on a path, stays
// true on that path because symbols never change.
#include "Analyzer.hpp"

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"

#include "../core/Cost.hpp"
#include "../core/LinExpr.hpp"
#include "../core/Solver.hpp"

using namespace clang;

namespace crosscheck {

namespace {

// ---------------------------------------------------------------------------
// Cost: abstract units plus the number of self-calls, for the worst path that
// falls through to the next statement and for the worst path that leaves the
// function with `return`. Keeping the two apart makes guard clauses precise:
//   if (c) return a;  rest      costs   cond + max(a, rest),   not  cond + a + rest.
// ---------------------------------------------------------------------------

struct Cost {
  Sat units;             ///< worst fall-through path
  Sat rec;
  bool live = true;      ///< can control fall through?
  Sat retUnits;          ///< worst returning path (if `returns`)
  Sat retRec;
  bool returns = false;
};

/// Forgets the distinction: an upper bound for every path, falling through.
Cost flat(Cost a) {
  Cost r;
  r.units = a.live ? a.units : Sat::of(0);
  r.rec = a.live ? a.rec : Sat::of(0);
  if (a.returns) {
    r.units = max(r.units, a.retUnits);
    r.rec = max(r.rec, a.retRec);
  }
  return r;
}

Cost seq(Cost a, Cost b) {
  if (!a.live) return a;  // `b` is unreachable
  Cost r;
  r.units = a.units + b.units;
  r.rec = a.rec + b.rec;
  r.live = b.live;
  r.returns = a.returns || b.returns;
  if (a.returns) {
    r.retUnits = a.retUnits;
    r.retRec = a.retRec;
  }
  if (b.returns) {
    r.retUnits = max(r.retUnits, a.units + b.retUnits);
    r.retRec = max(r.retRec, a.rec + b.retRec);
  }
  return r;
}

Cost alt(Cost a, Cost b) {
  Cost r;
  r.live = a.live || b.live;
  if (a.live) { r.units = a.units; r.rec = a.rec; }
  if (b.live) { r.units = max(r.units, b.units); r.rec = max(r.rec, b.rec); }
  r.returns = a.returns || b.returns;
  if (a.returns) { r.retUnits = a.retUnits; r.retRec = a.retRec; }
  if (b.returns) { r.retUnits = max(r.retUnits, b.retUnits); r.retRec = max(r.retRec, b.retRec); }
  return r;
}

Cost times(Sat k, Cost a) {
  a = flat(a);
  Cost r;
  r.units = k * a.units;
  r.rec = k * a.rec;
  return r;
}

Cost unit(std::uint64_t w) {
  Cost r;
  r.units = Sat::of(w);
  return r;
}

Cost returning(Cost a) {
  a = flat(a);
  Cost r;
  r.live = false;
  r.returns = true;
  r.retUnits = a.units;
  r.retRec = a.rec;
  return r;
}

// ---------------------------------------------------------------------------
// Symbolic states.
// ---------------------------------------------------------------------------

enum class Flow { Normal, Break, Continue, Return };

struct State {
  std::map<const VarDecl*, LinExpr> val;
  std::vector<Constraint> facts;
  /// Argument values of the self-calls performed so far on this path.
  std::vector<std::vector<LinExpr>> selfCalls;
  Flow flow = Flow::Normal;
};

struct CondResult {
  std::vector<Constraint> ifTrue;   ///< implied by the condition being true
  std::vector<Constraint> ifFalse;  ///< implied by the condition being false
  std::vector<std::pair<LinExpr, LinExpr>> neqTrue;   ///< a != b when true
  std::vector<std::pair<LinExpr, LinExpr>> neqFalse;  ///< a != b when false
};

Constraint contradiction() { return Constraint{LinExpr::constant(1)}; }

// ---------------------------------------------------------------------------
// Helpers on declarations.
// ---------------------------------------------------------------------------

const AnnotateAttr* findAnnotation(const Decl* d, llvm::StringRef name) {
  if (!d) return nullptr;
  for (const Decl* r : d->redecls())
    for (const auto* a : r->specific_attrs<AnnotateAttr>())
      if (a->getAnnotation() == name) return a;
  return nullptr;
}

std::optional<std::int64_t> toInt64(const llvm::APSInt& v) {
  if (v.isSigned()) {
    if (v.getSignificantBits() > 64) return std::nullopt;
    return v.getSExtValue();
  }
  if (v.getActiveBits() > 63) return std::nullopt;
  return static_cast<std::int64_t>(v.getZExtValue());
}

std::optional<std::int64_t> annotationArg(const AnnotateAttr* a, unsigned i, ASTContext& ctx) {
  if (!a || i >= a->args_size()) return std::nullopt;
  const Expr* e = *(a->args_begin() + i);
  Expr::EvalResult r;
  if (!e || e->isValueDependent() || !e->EvaluateAsInt(r, ctx)) return std::nullopt;
  return toInt64(r.Val.getInt());
}

bool isIntType(QualType t) {
  return !t.isNull() && t->isIntegralOrEnumerationType();
}

/// Inclusive range of an integer type, as far as it fits in int64.
std::pair<std::optional<std::int64_t>, std::optional<std::int64_t>> typeRange(QualType t,
                                                                              ASTContext& ctx) {
  if (t->isBooleanType()) return {0, 1};
  unsigned width = ctx.getIntWidth(t);
  bool isUnsigned = t->isUnsignedIntegerOrEnumerationType();
  if (isUnsigned) {
    if (width >= 64) return {0, std::nullopt};
    return {0, (std::int64_t{1} << width) - 1};
  }
  if (width >= 64) return {INT64_MIN, INT64_MAX};
  return {-(std::int64_t{1} << (width - 1)), (std::int64_t{1} << (width - 1)) - 1};
}

/// Range assumed for a *symbol* of an integer type. Deliberately weaker than
/// `typeRange` for 32-bit and wider types: the limits of `int` or `size_t`
/// are never used as loop or recursion bounds (a bound of 2^31 iterations
/// "because the counter cannot overflow" is not a real-time guarantee).
std::pair<std::optional<std::int64_t>, std::optional<std::int64_t>> symbolRange(QualType t,
                                                                                ASTContext& ctx) {
  if (t->isBooleanType() || ctx.getIntWidth(t) < 32) return typeRange(t, ctx);
  if (t->isUnsignedIntegerOrEnumerationType()) return {0, std::nullopt};
  return {std::nullopt, std::nullopt};
}

/// Marker calls `(void)sizeof(crosscheck::detail::NAME(arg))`.
const CallExpr* asMarker(const Stmt* s, llvm::StringRef name) {
  const auto* e = dyn_cast_or_null<Expr>(s);
  if (!e) return nullptr;
  e = e->IgnoreParenCasts();
  const auto* so = dyn_cast<UnaryExprOrTypeTraitExpr>(e);
  if (!so || so->getKind() != UETT_SizeOf || so->isArgumentType()) return nullptr;
  const auto* call = dyn_cast<CallExpr>(so->getArgumentExpr()->IgnoreParenCasts());
  if (!call) return nullptr;
  const FunctionDecl* fd = call->getDirectCallee();
  if (!fd || fd->getQualifiedNameAsString() != ("crosscheck::detail::" + name.str()))
    return nullptr;
  return call->getNumArgs() == 1 ? call : nullptr;
}

// ---------------------------------------------------------------------------
// Pre-pass: which local variables can be tracked symbolically?
// A variable is tracked when it is a local integer whose every use is a plain
// read, an assignment target or an increment/decrement operand (its address is
// never taken, it is never bound to a reference or captured).
// ---------------------------------------------------------------------------

class TrackScan : public RecursiveASTVisitor<TrackScan> {
 public:
  std::map<const VarDecl*, int> total, benign;
  std::set<const VarDecl*> escaped;

  static const VarDecl* varOf(const Expr* e) {
    const auto* dre = dyn_cast<DeclRefExpr>(e->IgnoreParens());
    return dre ? dyn_cast<VarDecl>(dre->getDecl()) : nullptr;
  }
  bool VisitDeclRefExpr(DeclRefExpr* e) {
    if (const auto* v = dyn_cast<VarDecl>(e->getDecl())) ++total[v];
    return true;
  }
  bool VisitImplicitCastExpr(ImplicitCastExpr* e) {
    if (e->getCastKind() == CK_LValueToRValue)
      if (const VarDecl* v = varOf(e->getSubExpr())) ++benign[v];
    return true;
  }
  bool VisitBinaryOperator(BinaryOperator* e) {
    if (e->isAssignmentOp())
      if (const VarDecl* v = varOf(e->getLHS())) ++benign[v];
    return true;
  }
  bool VisitUnaryOperator(UnaryOperator* e) {
    if (e->isIncrementDecrementOp())
      if (const VarDecl* v = varOf(e->getSubExpr())) ++benign[v];
    return true;
  }
  bool TraverseLambdaExpr(LambdaExpr* e) {
    for (const LambdaCapture& c : e->captures())
      if (c.capturesVariable())
        if (const auto* v = dyn_cast<VarDecl>(c.getCapturedVar())) escaped.insert(v);
    return true;  // the body is not executed here
  }
};

/// How a loop (or switch) modifies tracked variables.
struct ModInfo {
  bool nonNegative = true;  ///< every modification adds a constant >= 0
  bool nonPositive = true;  ///< every modification adds a constant <= 0
  bool declaredInside = false;
};

class ModScan : public RecursiveASTVisitor<ModScan> {
 public:
  ModScan(ASTContext& ctx) : ctx_(ctx) {}
  std::map<const VarDecl*, ModInfo> mods;
  std::set<const VarDecl*> refs;
  bool hasCaseLabel = false;

  bool VisitDeclRefExpr(DeclRefExpr* e) {
    if (const auto* v = dyn_cast<VarDecl>(e->getDecl())) refs.insert(v);
    return true;
  }
  bool VisitVarDecl(VarDecl* v) {
    ModInfo& m = mods[v];
    m.declaredInside = true;
    m.nonNegative = m.nonPositive = false;
    return true;
  }
  bool VisitBinaryOperator(BinaryOperator* e) {
    if (!e->isAssignmentOp()) return true;
    const VarDecl* v = TrackScan::varOf(e->getLHS());
    if (!v) return true;
    std::optional<std::int64_t> delta;
    if (e->getOpcode() == BO_AddAssign || e->getOpcode() == BO_SubAssign) {
      Expr::EvalResult r;
      if (!e->getRHS()->isValueDependent() && isIntType(e->getRHS()->getType()) &&
          e->getRHS()->EvaluateAsInt(r, ctx_)) {
        delta = toInt64(r.Val.getInt());
        if (delta && e->getOpcode() == BO_SubAssign)
          delta = *delta == INT64_MIN ? std::nullopt : std::optional<std::int64_t>(-*delta);
      }
    } else if (e->getOpcode() == BO_Assign) {
      // `v = v + c`, `v = c + v`, `v = v - c` with a constant c.
      if (const auto* rhs = dyn_cast<BinaryOperator>(e->getRHS()->IgnoreParenImpCasts());
          rhs && (rhs->getOpcode() == BO_Add || rhs->getOpcode() == BO_Sub)) {
        const Expr* l = rhs->getLHS()->IgnoreParenImpCasts();
        const Expr* r = rhs->getRHS()->IgnoreParenImpCasts();
        const Expr* other = nullptr;
        if (TrackScan::varOf(l) == v) other = r;
        else if (rhs->getOpcode() == BO_Add && TrackScan::varOf(r) == v) other = l;
        Expr::EvalResult c;
        if (other && !other->isValueDependent() && isIntType(other->getType()) &&
            !other->HasSideEffects(ctx_) && other->EvaluateAsInt(c, ctx_)) {
          delta = toInt64(c.Val.getInt());
          if (delta && rhs->getOpcode() == BO_Sub)
            delta = *delta == INT64_MIN ? std::nullopt : std::optional<std::int64_t>(-*delta);
        }
      }
    }
    note(v, delta);
    return true;
  }
  bool VisitUnaryOperator(UnaryOperator* e) {
    if (!e->isIncrementDecrementOp()) return true;
    if (const VarDecl* v = TrackScan::varOf(e->getSubExpr())) note(v, e->isIncrementOp() ? 1 : -1);
    return true;
  }
  bool VisitSwitchCase(SwitchCase*) {
    hasCaseLabel = true;
    return true;
  }
  bool TraverseLambdaExpr(LambdaExpr*) { return true; }

 private:
  void note(const VarDecl* v, std::optional<std::int64_t> delta) {
    ModInfo& m = mods[v];
    if (!delta || *delta < 0) m.nonNegative = false;
    if (!delta || *delta > 0) m.nonPositive = false;
  }
  ASTContext& ctx_;
};

// ---------------------------------------------------------------------------
// The analyser.
// ---------------------------------------------------------------------------

/// A calling context: for each parameter, the interval in which its argument
/// is known to lie at the call sites the analysis is used for. Empty: no
/// context (the analysis holds for every call that meets the preconditions).
using Context = std::vector<Interval>;
using SummaryKey = std::pair<const FunctionDecl*, Context>;

/// Declared preconditions of a function, over its own parameter symbols.
struct Contract {
  std::vector<std::optional<SymId>> paramSyms;
  std::vector<Constraint> requires_;
};

struct CallRecord {
  const FunctionDecl* callee = nullptr;  ///< canonical declaration
  Context hull;                          ///< join of the argument intervals seen
  bool any = false;
};

struct Summary {
  bool ok = true;
  /// Analyses of callees this analysis relies on.
  std::set<SummaryKey> callees;
  Sat wcet;
  std::vector<std::string> assumptions;
  /// Symbols standing for the integer parameters (by parameter index).
  std::vector<std::optional<SymId>> paramSyms;
  /// Preconditions over `paramSyms` (CROSSCHECK_RANGE, CROSSCHECK_REQUIRE).
  std::vector<Constraint> requires_;
  /// Why the function is rejected (first violation found), if it is.
  std::string reason;
  FunctionReport report;
};

struct RecSite {
  std::vector<Constraint> premises;
  std::vector<LinExpr> args;  ///< one entry per recursion slot
};

struct FnCtx {
  const FunctionDecl* fn = nullptr;
  std::set<const VarDecl*> tracked;
  Summary summary;
  std::vector<SymId> slotSyms;        ///< recursion slots: integer parameters
  std::vector<unsigned> slotParams;   ///< their parameter indices
  std::vector<RecSite> recSites;
  bool recImprecise = false;          ///< self-call lists are not path-exact
  unsigned speculative = 0;
  unsigned loopDepth = 0;
  std::map<const Stmt*, LoopReport> loops;
  std::set<std::pair<unsigned, std::string>> emitted;
  /// Argument intervals of the calls evaluated so far (non-speculatively).
  std::map<const CallExpr*, CallRecord> calls;
  /// Innermost enclosing switch: the havoc state valid at every case label.
  /// An empty entry marks a loop boundary (case labels across it are rejected).
  std::vector<std::optional<State>> switchStack;
};

class Analyzer {
 public:
  Analyzer(ASTContext& ctx, const Options& opts) : ctx_(ctx), opts_(opts), w_(opts.weights) {
    DiagnosticsEngine& d = ctx_.getDiagnostics();
    errorId_ = d.getCustomDiagID(DiagnosticsEngine::Error, "crosscheck: %0");
    remarkId_ = d.getCustomDiagID(DiagnosticsEngine::Remark, "crosscheck: %0");
  }

  Report run();

 private:
  // -- diagnostics ----------------------------------------------------------
  FnCtx& cur() { return *stack_.back(); }

  /// Reports a violation. `root` is the underlying reason when `msg` only
  /// relays a violation found in a callee. Violations located in system
  /// headers are not printed there: they surface at the call site in user code.
  void error(SourceLocation loc, const std::string& msg, const std::string& root = "") {
    FnCtx& c = cur();
    if (c.speculative) return;
    c.summary.ok = false;
    if (c.summary.reason.empty()) c.summary.reason = root.empty() ? msg : root;
    if (!c.emitted.insert({loc.getRawEncoding(), msg}).second) return;
    const SourceManager& sm = ctx_.getSourceManager();
    if (loc.isValid() && sm.isInSystemHeader(sm.getExpansionLoc(loc))) return;
    c.summary.report.errors.push_back(describe(loc) + msg);
    // The same function may be analysed in several calling contexts.
    if (!printed_.insert({loc.getRawEncoding(), msg}).second) return;
    ctx_.getDiagnostics().Report(loc, errorId_) << msg;
  }

  void assume(const std::string& msg) {
    FnCtx& c = cur();
    if (c.speculative) return;
    auto& a = c.summary.assumptions;
    if (std::find(a.begin(), a.end(), msg) == a.end()) a.push_back(msg);
  }

  std::string describe(SourceLocation loc) {
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    if (p.isInvalid()) return "";
    return "line " + std::to_string(p.getLine()) + ": ";
  }

  unsigned lineOf(SourceLocation loc) {
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    return p.isInvalid() ? 0 : p.getLine();
  }

  // -- symbols and values ---------------------------------------------------
  bool tracked(const VarDecl* v) { return v && cur().tracked.count(v); }

  LinExpr freshInt(QualType t, const std::string& name) {
    auto [lo, hi] = symbolRange(t, ctx_);
    return LinExpr::symbol(syms_.fresh(name, lo, hi));
  }

  /// A value about which nothing is known beyond its type.
  LinExpr unknown(QualType t, const char* name = "tmp") {
    if (!isIntType(t)) return LinExpr::poison();
    return freshInt(t, name);
  }

  /// Adds to `s` what a disequality `a != b` gives once the order of `a` and
  /// `b` is known: with `a <= b` it is `a < b`, with `a >= b` it is `a > b`.
  void addDisequalities(State& s, const std::vector<std::pair<LinExpr, LinExpr>>& neq) {
    for (const auto& [a, b] : neq) {
      if (a.poisoned() || b.poisoned()) continue;
      if (entails(syms_, s.facts, le(a, b)))
        s.facts.push_back(lt(a, b));
      else if (entails(syms_, s.facts, ge(a, b)))
        s.facts.push_back(gt(a, b));
    }
  }

  /// Extends `s` with everything known when the condition is true / false.
  void assumeCond(State& s, const CondResult& r, bool value) {
    const auto& facts = value ? r.ifTrue : r.ifFalse;
    s.facts.insert(s.facts.end(), facts.begin(), facts.end());
    addDisequalities(s, value ? r.neqTrue : r.neqFalse);
  }

  LinExpr lookup(const VarDecl* v, State& s) {
    auto it = s.val.find(v);
    if (it != s.val.end() && !it->second.poisoned()) return it->second;
    LinExpr e = freshInt(v->getType(), v->getNameAsString());
    s.val[v] = e;
    return e;
  }

  /// `v` if it provably lies in the range of `t`, an unknown of type `t`
  /// otherwise (this is where wrap-around and truncation are accounted for).
  LinExpr fit(const LinExpr& v, QualType t, State& s) {
    if (!isIntType(t)) return LinExpr::poison();
    if (v.poisoned()) return unknown(t);
    auto [lo, hi] = typeRange(t, ctx_);
    if (v.isConstant()) {
      std::int64_t c = v.constantTerm();
      return ((!lo || c >= *lo) && (!hi || c <= *hi)) ? v : unknown(t);
    }
    if (lo && *lo != INT64_MIN && !entails(syms_, s.facts, ge(v, LinExpr::constant(*lo))))
      return unknown(t);
    if (hi && *hi != INT64_MAX && !entails(syms_, s.facts, le(v, LinExpr::constant(*hi))))
      return unknown(t);
    return v;
  }

  /// Result of arithmetic in type `t`: unsigned arithmetic wraps, so the value
  /// must be proved in range; signed overflow is undefined behaviour and is
  /// assumed not to happen.
  LinExpr arithResult(const LinExpr& v, QualType t, State& s) {
    if (!isIntType(t)) return LinExpr::poison();
    if (v.poisoned()) return unknown(t);
    if (t->isUnsignedIntegerOrEnumerationType() || t->isBooleanType()) return fit(v, t, s);
    return v;
  }

  /// Does every value of `from` fit in `to`?
  bool widens(QualType from, QualType to) {
    if (!isIntType(from) || !isIntType(to)) return false;
    auto [flo, fhi] = typeRange(from, ctx_);
    auto [tlo, thi] = typeRange(to, ctx_);
    bool loOk = !tlo || (flo && *flo >= *tlo);
    bool hiOk = !thi || (fhi && *fhi <= *thi);
    return loOk && hiOk;
  }

  std::optional<std::int64_t> constantValue(const Expr* e) {
    if (!e || e->isValueDependent() || !isIntType(e->getType()) || e->isGLValue()) return std::nullopt;
    if (e->HasSideEffects(ctx_)) return std::nullopt;
    Expr::EvalResult r;
    if (!e->EvaluateAsInt(r, ctx_)) return std::nullopt;
    return toInt64(r.Val.getInt());
  }

  // -- expression evaluation (extensional layer) ----------------------------
  LinExpr eval(const Expr* e, State& s);
  void evalChildren(const Expr* e, State& s);
  LinExpr evalCall(const CallExpr* call, State& s);
  LinExpr evalBinary(const BinaryOperator* bo, State& s);
  LinExpr arith(BinaryOperatorKind op, const LinExpr& a, const LinExpr& b, QualType t, State& s);
  CondResult evalCond(const Expr* e, State& s);
  void assignVar(const VarDecl* v, const LinExpr& value, State& s);
  void checkContract(const FunctionDecl* callee, const std::vector<LinExpr>& args,
                     const std::vector<const Expr*>& argExprs, SourceLocation loc, State& s);

  // -- cost (intensional layer) ---------------------------------------------
  Cost exprCost(const Expr* e);
  Cost childrenCost(const Expr* e);
  Cost calleeCost(const CallExpr* call);
  Cost functionCost(const FunctionDecl* fd, SourceLocation loc, const CallExpr* call = nullptr);

  // -- statements -----------------------------------------------------------
  Cost exec(const Stmt* s, std::vector<State>& states);
  Cost execDecl(const DeclStmt* ds, std::vector<State>& states);
  Cost execIf(const IfStmt* is, std::vector<State>& states);
  Cost execSwitch(const SwitchStmt* ss, std::vector<State>& states);
  Cost execRangeFor(const CXXForRangeStmt* fs, std::vector<State>& states);
  Cost execLoop(const Stmt* loop, const Expr* cond, const Stmt* body, const Expr* inc, bool isDo,
                std::optional<std::uint64_t> annotated, std::vector<State>& states);

  State mergeStates(const std::vector<State>& in);
  void limitStates(std::vector<State>& states);
  State havoc(const State& s, const std::map<const VarDecl*, ModInfo>& mods,
              std::map<const VarDecl*, SymId>* fresh = nullptr);
  std::optional<std::uint64_t> loopBoundMarker(const Stmt* body);
  std::string potentialString(const RankingResult& r, const std::vector<std::string>& names);

  // -- functions ------------------------------------------------------------
  const Summary& analyzeFunction(const FunctionDecl* def, const Context& context = {});
  State enterFunction(const FunctionDecl* def, FnCtx& fc);
  const Contract& contractOf(const FunctionDecl* def);
  bool callsItself(const FunctionDecl* def);
  void recordCall(const CallExpr* call, const FunctionDecl* fd, const std::vector<LinExpr>& args,
                  const std::vector<const Expr*>& argExprs, State& s);
  Context contextFor(const CallExpr* call, const FunctionDecl* def);
  void fillInContext(Report& report, const std::vector<const FunctionDecl*>& roots);
  bool onStack(const FunctionDecl* fd) {
    for (const auto& c : stack_)
      if (c->fn->getCanonicalDecl() == fd->getCanonicalDecl()) return true;
    return false;
  }

  ASTContext& ctx_;
  const Options& opts_;
  CostModel w_;
  SymbolTable syms_;
  unsigned errorId_ = 0, remarkId_ = 0;
  std::vector<std::unique_ptr<FnCtx>> stack_;
  std::map<SummaryKey, Summary> cache_;
  std::map<const FunctionDecl*, Contract> contracts_;
  std::map<const FunctionDecl*, bool> selfRecursive_;
  std::map<const FunctionDecl*, unsigned> specialisations_;
  std::set<std::pair<unsigned, std::string>> printed_;
};

// ===========================================================================
// Expression evaluation.
// ===========================================================================

void Analyzer::assignVar(const VarDecl* v, const LinExpr& value, State& s) {
  if (value.poisoned())
    s.val.erase(v);
  else
    s.val[v] = value;
}

void Analyzer::evalChildren(const Expr* e, State& s) {
  for (const Stmt* c : e->children())
    if (const auto* ce = dyn_cast_or_null<Expr>(c)) eval(ce, s);
}

LinExpr Analyzer::arith(BinaryOperatorKind op, const LinExpr& a, const LinExpr& b, QualType t,
                        State& s) {
  if (a.poisoned() || b.poisoned()) return unknown(t);
  auto nonNegative = [&](const LinExpr& x) {
    if (x.isConstant()) return x.constantTerm() >= 0;
    return entails(syms_, s.facts, ge(x, LinExpr::constant(0)));
  };
  auto divide = [&](std::int64_t c) -> LinExpr {
    if (c <= 0) return unknown(t);
    if (a.isConstant()) return LinExpr::constant(a.constantTerm() / c);
    if (c == 1) return a;
    if (!nonNegative(a)) return unknown(t);
    // q = a / c with a >= 0:  c*q <= a <= c*q + c - 1.
    LinExpr q = unknown(t, "quot");
    s.facts.push_back(le(q.scaled(c), a));
    s.facts.push_back(le(a, q.scaled(c) + LinExpr::constant(c - 1)));
    s.facts.push_back(ge(q, LinExpr::constant(0)));
    return q;
  };
  switch (op) {
    case BO_Add: return a + b;
    case BO_Sub: return a - b;
    case BO_Mul:
      if (a.isConstant()) return b.scaled(a.constantTerm());
      if (b.isConstant()) return a.scaled(b.constantTerm());
      return unknown(t);
    case BO_Div:
      return b.isConstant() ? divide(b.constantTerm()) : unknown(t);
    case BO_Rem: {
      if (!b.isConstant() || b.constantTerm() <= 0) return unknown(t);
      std::int64_t c = b.constantTerm();
      if (a.isConstant()) return LinExpr::constant(a.constantTerm() % c);
      LinExpr r = unknown(t, "rem");
      if (nonNegative(a)) {
        s.facts.push_back(ge(r, LinExpr::constant(0)));
        s.facts.push_back(le(r, a));
      } else {
        s.facts.push_back(ge(r, LinExpr::constant(-(c - 1))));
      }
      s.facts.push_back(le(r, LinExpr::constant(c - 1)));
      return r;
    }
    case BO_Shl:
      if (b.isConstant() && b.constantTerm() >= 0 && b.constantTerm() < 62)
        return a.scaled(std::int64_t{1} << b.constantTerm());
      return unknown(t);
    case BO_Shr:
      if (b.isConstant() && b.constantTerm() >= 0 && b.constantTerm() < 62)
        return divide(std::int64_t{1} << b.constantTerm());
      return unknown(t);
    case BO_And: {
      // x & m with a constant m >= 0 lies in [0, m].
      const LinExpr* mask = a.isConstant() ? &a : b.isConstant() ? &b : nullptr;
      if (!mask || mask->constantTerm() < 0) return unknown(t);
      if (a.isConstant() && b.isConstant())
        return LinExpr::constant(a.constantTerm() & b.constantTerm());
      LinExpr r = unknown(t, "masked");
      s.facts.push_back(ge(r, LinExpr::constant(0)));
      s.facts.push_back(le(r, *mask));
      return r;
    }
    default:
      return unknown(t);
  }
}

LinExpr Analyzer::evalBinary(const BinaryOperator* bo, State& s) {
  QualType t = bo->getType();
  BinaryOperatorKind op = bo->getOpcode();

  if (op == BO_Comma) {
    eval(bo->getLHS(), s);
    return eval(bo->getRHS(), s);
  }
  if (op == BO_Assign) {
    LinExpr v = eval(bo->getRHS(), s);
    const VarDecl* var = TrackScan::varOf(bo->getLHS());
    if (tracked(var)) {
      assignVar(var, v, s);
      return v;
    }
    eval(bo->getLHS(), s);
    return unknown(t);
  }
  if (bo->isCompoundAssignmentOp()) {
    const VarDecl* var = TrackScan::varOf(bo->getLHS());
    LinExpr rhs = eval(bo->getRHS(), s);
    if (!tracked(var)) {
      eval(bo->getLHS(), s);
      return unknown(t);
    }
    const auto* cao = cast<CompoundAssignOperator>(bo);
    QualType compTy = cao->getComputationResultType();
    LinExpr curVal = lookup(var, s);
    if (!widens(var->getType(), cao->getComputationLHSType())) curVal = fit(curVal, cao->getComputationLHSType(), s);
    LinExpr v = arith(BinaryOperator::getOpForCompoundAssignment(op), curVal, rhs, compTy, s);
    v = arithResult(v, compTy, s);
    if (!v.poisoned() && !(compTy->isSignedIntegerOrEnumerationType() &&
                           ctx_.hasSameUnqualifiedType(compTy, var->getType())))
      v = fit(v, var->getType(), s);
    assignVar(var, v, s);
    return v;
  }
  if (bo->isComparisonOp() || bo->isLogicalOp()) {
    evalCond(bo, s);
    return unknown(t, "flag");
  }
  LinExpr a = eval(bo->getLHS(), s);
  LinExpr b = eval(bo->getRHS(), s);
  if (!isIntType(t)) return LinExpr::poison();
  return arithResult(arith(op, a, b, t, s), t, s);
}

void Analyzer::checkContract(const FunctionDecl* callee, const std::vector<LinExpr>& args,
                             const std::vector<const Expr*>& argExprs, SourceLocation loc,
                             State& s) {
  const std::vector<std::optional<SymId>>* paramSyms = nullptr;
  const std::vector<Constraint>* requires_ = nullptr;
  bool self = !stack_.empty() && callee->getCanonicalDecl() == cur().fn->getCanonicalDecl();
  if (self) {
    paramSyms = &cur().summary.paramSyms;
    requires_ = &cur().summary.requires_;
  } else {
    if (cur().speculative) return;  // nothing is reported or recorded there
    const FunctionDecl* def = nullptr;
    if (!callee->hasBody(def) || !def->getBody() || def->isDependentContext()) return;
    const Contract& ct = contractOf(def);
    paramSyms = &ct.paramSyms;
    requires_ = &ct.requires_;
  }
  if (!requires_->empty()) {
    std::map<SymId, LinExpr> sigma;
    for (std::size_t i = 0; i < paramSyms->size() && i < args.size(); ++i) {
      if (!(*paramSyms)[i]) continue;
      LinExpr a = args[i];
      if (a.poisoned()) a = unknown(argExprs[i]->getType(), "arg");
      if (a.poisoned()) a = freshInt(ctx_.LongLongTy, "arg");
      sigma[*(*paramSyms)[i]] = a;
    }
    for (const Constraint& c : *requires_) {
      Constraint inst{c.e.substitute(sigma)};
      if (!entails(syms_, s.facts, inst)) {
        error(loc, "cannot prove the precondition of '" + callee->getNameAsString() +
                       "' at this call (CROSSCHECK_RANGE / CROSSCHECK_REQUIRE)");
        break;
      }
    }
  }
  if (self && !cur().speculative) {
    FnCtx& c = cur();
    RecSite site;
    site.premises = s.facts;
    for (unsigned p : c.slotParams) {
      LinExpr a = p < args.size() ? args[p] : LinExpr::poison();
      if (a.poisoned()) a = freshInt(callee->getParamDecl(p)->getType(), "arg");
      site.args.push_back(a);
    }
    c.recSites.push_back(site);
    s.selfCalls.push_back(site.args);
    if (c.loopDepth > 0) c.recImprecise = true;
  }
}

LinExpr Analyzer::evalCall(const CallExpr* call, State& s) {
  eval(call->getCallee(), s);
  std::vector<LinExpr> args;
  std::vector<const Expr*> argExprs;
  for (const Expr* a : call->arguments()) {
    args.push_back(eval(a, s));
    argExprs.push_back(a);
  }
  const FunctionDecl* fd = call->getDirectCallee();
  if (fd) {
    // For `a.operator+(b)` written as `a + b`, the object is argument 0.
    if (isa<CXXOperatorCallExpr>(call))
      if (const auto* md = dyn_cast<CXXMethodDecl>(fd); md && md->isInstance() && !args.empty()) {
        args.erase(args.begin());
        argExprs.erase(argExprs.begin());
      }
    checkContract(fd, args, argExprs, call->getExprLoc(), s);
    recordCall(call, fd, args, argExprs, s);
  }
  return unknown(call->getType(), "result");
}

LinExpr Analyzer::eval(const Expr* e, State& s) {
  if (!e) return LinExpr::poison();
  e = e->IgnoreParens();
  QualType t = e->getType();

  if (auto c = constantValue(e)) return LinExpr::constant(*c);

  if (const auto* ce = dyn_cast<CastExpr>(e)) {
    const Expr* sub = ce->getSubExpr();
    switch (ce->getCastKind()) {
      case CK_LValueToRValue: {
        const VarDecl* v = TrackScan::varOf(sub);
        if (tracked(v)) return lookup(v, s);
        eval(sub, s);
        return unknown(t);
      }
      case CK_NoOp:
        return eval(sub, s);
      case CK_IntegralCast: {
        LinExpr v = eval(sub, s);
        if (!isIntType(t)) return LinExpr::poison();
        if (v.poisoned()) return unknown(t);
        if (widens(sub->getType(), t)) return v;
        return fit(v, t, s);
      }
      default:
        eval(sub, s);
        return unknown(t);
    }
  }
  if (const auto* uo = dyn_cast<UnaryOperator>(e)) {
    if (uo->isIncrementDecrementOp()) {
      const VarDecl* v = TrackScan::varOf(uo->getSubExpr());
      if (!tracked(v)) {
        eval(uo->getSubExpr(), s);
        return unknown(t);
      }
      LinExpr old = lookup(v, s);
      LinExpr nw = old + LinExpr::constant(uo->isIncrementOp() ? 1 : -1);
      QualType vt = v->getType();
      // Types narrower than int are promoted, then converted back.
      bool narrow = ctx_.getIntWidth(vt) < ctx_.getIntWidth(ctx_.IntTy);
      nw = (narrow || vt->isUnsignedIntegerOrEnumerationType() || vt->isBooleanType())
               ? fit(nw, vt, s)
               : nw;
      assignVar(v, nw, s);
      return uo->isPrefix() ? nw : old;
    }
    if (uo->getOpcode() == UO_Minus) return arithResult(-eval(uo->getSubExpr(), s), t, s);
    if (uo->getOpcode() == UO_Plus || uo->getOpcode() == UO_Extension)
      return eval(uo->getSubExpr(), s);
    eval(uo->getSubExpr(), s);
    return unknown(t);
  }
  if (const auto* bo = dyn_cast<BinaryOperator>(e)) return evalBinary(bo, s);
  if (const auto* co = dyn_cast<ConditionalOperator>(e)) {
    CondResult r = evalCond(co->getCond(), s);
    State s1 = s, s2 = s;
    assumeCond(s1, r, true);
    assumeCond(s2, r, false);
    LinExpr v1 = eval(co->getTrueExpr(), s1);
    LinExpr v2 = eval(co->getFalseExpr(), s2);
    std::size_t keep = s.facts.size();
    s = mergeStates({s1, s2});
    if (!isIntType(t)) return LinExpr::poison();
    if (!v1.poisoned() && v1 == v2) return v1;
    // Join of the two arms: when they differ by a constant, keep the hull.
    LinExpr m = unknown(t, "sel");
    LinExpr d = v2 - v1;
    if (!v1.poisoned() && !v2.poisoned() && d.isConstant() && s.facts.size() >= keep) {
      std::int64_t c = d.constantTerm();
      s.facts.push_back(ge(m, v1 + LinExpr::constant(std::min<std::int64_t>(c, 0))));
      s.facts.push_back(le(m, v1 + LinExpr::constant(std::max<std::int64_t>(c, 0))));
    }
    return m;
  }
  if (const auto* call = dyn_cast<CallExpr>(e)) return evalCall(call, s);
  if (const auto* da = dyn_cast<CXXDefaultArgExpr>(e)) return eval(da->getExpr(), s);
  if (const auto* di = dyn_cast<CXXDefaultInitExpr>(e)) return eval(di->getExpr(), s);
  if (const auto* ec = dyn_cast<FullExpr>(e)) return eval(ec->getSubExpr(), s);
  if (const auto* mt = dyn_cast<MaterializeTemporaryExpr>(e)) return eval(mt->getSubExpr(), s);
  if (isa<UnaryExprOrTypeTraitExpr>(e) || isa<CXXNoexceptExpr>(e) || isa<TypeTraitExpr>(e))
    return unknown(t);
  if (const auto* le_ = dyn_cast<LambdaExpr>(e)) {
    for (const Expr* init : le_->capture_inits()) eval(init, s);
    return LinExpr::poison();
  }
  evalChildren(e, s);
  return unknown(t);
}

CondResult Analyzer::evalCond(const Expr* e, State& s) {
  CondResult r;
  if (!e) {  // `for (;;)`: always true
    r.ifFalse.push_back(contradiction());
    return r;
  }
  e = e->IgnoreParens();
  if (const auto* fe = dyn_cast<FullExpr>(e)) return evalCond(fe->getSubExpr(), s);

  if (!e->isValueDependent() && !e->HasSideEffects(ctx_)) {
    bool value = false;
    if (e->EvaluateAsBooleanCondition(value, ctx_)) {
      (value ? r.ifFalse : r.ifTrue).push_back(contradiction());
      return r;
    }
  }
  if (const auto* uo = dyn_cast<UnaryOperator>(e); uo && uo->getOpcode() == UO_LNot) {
    CondResult inner = evalCond(uo->getSubExpr(), s);
    r.ifTrue = inner.ifFalse;
    r.ifFalse = inner.ifTrue;
    r.neqTrue = inner.neqFalse;
    r.neqFalse = inner.neqTrue;
    return r;
  }
  if (const auto* ce = dyn_cast<ImplicitCastExpr>(e)) {
    if (ce->getCastKind() == CK_IntegralToBoolean) {
      LinExpr v = eval(ce->getSubExpr(), s);
      if (!v.poisoned()) {
        LinExpr zero = LinExpr::constant(0);
        r.neqTrue.push_back({v, zero});
        r.ifFalse.push_back(le(v, zero));
        r.ifFalse.push_back(ge(v, zero));
      }
      return r;
    }
    if (ce->getCastKind() == CK_NoOp) return evalCond(ce->getSubExpr(), s);
  }
  if (const auto* bo = dyn_cast<BinaryOperator>(e)) {
    BinaryOperatorKind op = bo->getOpcode();
    if (op == BO_LAnd || op == BO_LOr) {
      CondResult l = evalCond(bo->getLHS(), s);
      // The right operand is evaluated only when the left one does not decide.
      State s1 = s;
      const auto& gate = op == BO_LAnd ? l.ifTrue : l.ifFalse;
      s1.facts.insert(s1.facts.end(), gate.begin(), gate.end());
      CondResult rr = evalCond(bo->getRHS(), s1);
      if (s1.val != s.val || s1.selfCalls.size() != s.selfCalls.size()) {
        State skipped = s;
        s = mergeStates({skipped, s1});
      }
      if (op == BO_LAnd) {
        r.ifTrue = l.ifTrue;
        r.ifTrue.insert(r.ifTrue.end(), rr.ifTrue.begin(), rr.ifTrue.end());
        r.neqTrue = l.neqTrue;
        r.neqTrue.insert(r.neqTrue.end(), rr.neqTrue.begin(), rr.neqTrue.end());
      } else {
        r.ifFalse = l.ifFalse;
        r.ifFalse.insert(r.ifFalse.end(), rr.ifFalse.begin(), rr.ifFalse.end());
        r.neqFalse = l.neqFalse;
        r.neqFalse.insert(r.neqFalse.end(), rr.neqFalse.begin(), rr.neqFalse.end());
      }
      return r;
    }
    if (bo->isComparisonOp() && op != BO_Cmp && isIntType(bo->getLHS()->getType()) &&
        isIntType(bo->getRHS()->getType())) {
      LinExpr a = eval(bo->getLHS(), s);
      LinExpr b = eval(bo->getRHS(), s);
      if (a.poisoned() || b.poisoned()) return r;
      switch (op) {
        case BO_LT: r.ifTrue.push_back(lt(a, b)); r.ifFalse.push_back(ge(a, b)); break;
        case BO_LE: r.ifTrue.push_back(le(a, b)); r.ifFalse.push_back(gt(a, b)); break;
        case BO_GT: r.ifTrue.push_back(gt(a, b)); r.ifFalse.push_back(le(a, b)); break;
        case BO_GE: r.ifTrue.push_back(ge(a, b)); r.ifFalse.push_back(lt(a, b)); break;
        case BO_EQ:
          r.ifTrue.push_back(le(a, b));
          r.ifTrue.push_back(ge(a, b));
          r.neqFalse.push_back({a, b});
          break;
        case BO_NE:
          r.ifFalse.push_back(le(a, b));
          r.ifFalse.push_back(ge(a, b));
          r.neqTrue.push_back({a, b});
          break;
        default: break;
      }
      return r;
    }
    if (bo->isComparisonOp() || bo->isLogicalOp()) {
      // Not an integer comparison (floating point, pointers, ...): no facts.
      evalChildren(bo, s);
      return r;
    }
  }
  eval(e, s);
  return r;
}

// ===========================================================================
// Cost of expressions and calls.
// ===========================================================================

Cost Analyzer::childrenCost(const Expr* e) {
  Cost c{};
  for (const Stmt* ch : e->children())
    if (const auto* ce = dyn_cast_or_null<Expr>(ch)) c = seq(c, exprCost(ce));
  return c;
}

Cost Analyzer::exprCost(const Expr* e) {
  if (!e) return Cost{};
  e = e->IgnoreParens();

  if (isa<ConstantExpr>(e) || isa<UnaryExprOrTypeTraitExpr>(e) || isa<CXXNoexceptExpr>(e) ||
      isa<TypeTraitExpr>(e))
    return Cost{};

  if (const auto* bo = dyn_cast<BinaryOperator>(e)) {
    Cost c = childrenCost(e);
    if (bo->isLogicalOp()) return seq(c, unit(w_.branch));
    if (bo->getOpcode() == BO_Comma) return c;
    if (bo->getOpcode() == BO_Assign) return seq(c, unit(w_.assign));
    if (bo->isCompoundAssignmentOp()) return seq(c, unit(w_.arith + w_.assign));
    return seq(c, unit(w_.arith));
  }
  if (const auto* uo = dyn_cast<UnaryOperator>(e)) {
    Cost c = childrenCost(e);
    switch (uo->getOpcode()) {
      case UO_Plus: case UO_AddrOf: case UO_Extension: return c;
      case UO_Deref: return seq(c, unit(w_.memory));
      case UO_PreInc: case UO_PreDec: case UO_PostInc: case UO_PostDec:
        return seq(c, unit(w_.arith + w_.assign));
      default: return seq(c, unit(w_.arith));
    }
  }
  if (const auto* co = dyn_cast<ConditionalOperator>(e))
    return seq(seq(exprCost(co->getCond()), unit(w_.branch)),
               alt(exprCost(co->getTrueExpr()), exprCost(co->getFalseExpr())));
  if (isa<BinaryConditionalOperator>(e)) return seq(childrenCost(e), unit(w_.branch));
  if (isa<ArraySubscriptExpr>(e)) return seq(childrenCost(e), unit(w_.memory));
  if (const auto* me = dyn_cast<MemberExpr>(e))
    return seq(childrenCost(e), unit(me->isArrow() ? w_.memory : 0));
  if (isa<CXXDynamicCastExpr>(e)) {
    error(e->getExprLoc(), "dynamic_cast is not allowed in a real-time function");
    return childrenCost(e);
  }
  if (const auto* ce = dyn_cast<CastExpr>(e)) {
    Cost c = childrenCost(e);
    CastKind k = ce->getCastKind();
    if (k == CK_IntegralToFloating || k == CK_FloatingToIntegral) return seq(c, unit(w_.convert));
    return c;
  }
  if (const auto* ne = dyn_cast<CXXNewExpr>(e)) {
    const FunctionDecl* op = ne->getOperatorNew();
    if (!(op && op->isReservedGlobalPlacementOperator()))
      error(e->getExprLoc(), "dynamic allocation ('new') is not allowed in a real-time function");
    return childrenCost(e);
  }
  if (isa<CXXDeleteExpr>(e)) {
    error(e->getExprLoc(), "dynamic deallocation ('delete') is not allowed in a real-time function");
    return childrenCost(e);
  }
  if (isa<CXXThrowExpr>(e)) {
    error(e->getExprLoc(), "'throw' is not allowed in a real-time function");
    return childrenCost(e);
  }
  if (isa<CXXBindTemporaryExpr>(e)) {
    error(e->getExprLoc(),
          "temporary with a non-trivial destructor (hidden cost) in a real-time function");
    return childrenCost(e);
  }
  if (isa<StmtExpr>(e) || isa<CoroutineSuspendExpr>(e)) {
    error(e->getExprLoc(), "unsupported expression in a real-time function");
    return Cost{};
  }
  if (const auto* ctor = dyn_cast<CXXConstructExpr>(e)) {
    Cost c = childrenCost(e);
    const CXXConstructorDecl* cd = ctor->getConstructor();
    if (cd && !cd->isTrivial()) c = seq(c, functionCost(cd, e->getExprLoc()));
    return c;
  }
  if (const auto* call = dyn_cast<CallExpr>(e)) return seq(childrenCost(e), calleeCost(call));
  if (const auto* da = dyn_cast<CXXDefaultArgExpr>(e)) return exprCost(da->getExpr());
  if (const auto* di = dyn_cast<CXXDefaultInitExpr>(e)) return exprCost(di->getExpr());
  if (const auto* le_ = dyn_cast<LambdaExpr>(e)) {
    Cost c{};
    for (const Expr* init : le_->capture_inits()) c = seq(c, exprCost(init));
    return c;
  }
  return childrenCost(e);
}

Cost Analyzer::calleeCost(const CallExpr* call) {
  const FunctionDecl* fd = call->getDirectCallee();
  if (!fd) {
    if (isa<CXXPseudoDestructorExpr>(call->getCallee()->IgnoreParens())) return Cost{};
    error(call->getExprLoc(),
          "indirect call (function pointer or pointer to member): the callee is unknown");
    return unit(w_.call);
  }
  if (const auto* mc = dyn_cast<CXXMemberCallExpr>(call)) {
    const auto* md = dyn_cast<CXXMethodDecl>(fd);
    const auto* me = dyn_cast<MemberExpr>(call->getCallee()->IgnoreParens());
    if (md && md->isVirtual() && !(me && me->hasQualifier())) {
      const CXXMethodDecl* devirt =
          md->getDevirtualizedMethod(mc->getImplicitObjectArgument(), /*IsAppleKext=*/false);
      if (!devirt) {
        error(call->getExprLoc(), "virtual call to '" + md->getQualifiedNameAsString() +
                                      "' is not allowed in a real-time function");
        return unit(w_.call);
      }
      fd = devirt;
    }
  }
  return functionCost(fd, call->getExprLoc(), call);
}

Cost Analyzer::functionCost(const FunctionDecl* fd, SourceLocation loc, const CallExpr* call) {
  static const std::set<std::string> banned = {"malloc", "calloc", "realloc", "free",
                                               "aligned_alloc", "posix_memalign", "strdup",
                                               "alloca", "operator_new", "operator_delete"};
  static const std::set<std::string> constantCost = {
      "sqrt", "sqrtf", "sqrtl", "fabs", "fabsf", "fabsl", "abs", "labs", "llabs",
      "sin", "sinf", "cos", "cosf", "tan", "tanf", "atan", "atanf", "atan2", "atan2f",
      "exp", "expf", "log", "logf", "pow", "powf", "floor", "floorf", "ceil", "ceilf",
      "round", "roundf", "trunc", "truncf", "fmin", "fminf", "fmax", "fmaxf", "fma", "fmaf",
      "hypot", "hypotf", "copysign", "copysignf", "isnan", "isinf", "isfinite",
      "expect", "expect_with_probability", "unreachable", "assume_aligned",
      "is_constant_evaluated", "addressof", "launder", "clz", "clzl", "clzll", "ctz", "ctzl",
      "ctzll", "popcount", "popcountl", "popcountll", "bswap16", "bswap32", "bswap64",
      "nan", "nanf", "inf", "inff", "huge_val", "huge_valf", "signbit", "trap",
      "forward", "move", "move_if_noexcept", "as_const", "forward_like", "constant_p",
      "add_overflow", "sub_overflow", "mul_overflow", "assume", "prefetch"};

  OverloadedOperatorKind ook = fd->getDeclName().getCXXOverloadedOperator();
  if ((ook == OO_New || ook == OO_Array_New || ook == OO_Delete || ook == OO_Array_Delete) &&
      !fd->isReservedGlobalPlacementOperator()) {
    error(loc, "dynamic allocation ('" + fd->getNameAsString() +
                   "') is not allowed in a real-time function");
    return unit(w_.call);
  }
  std::string name = fd->getIdentifier() ? fd->getName().str() : std::string();
  std::string base = name;
  if (base.rfind("__builtin_", 0) == 0) base = base.substr(10);
  bool cLike = fd->getBuiltinID() != 0 || fd->isExternC() ||
               fd->getDeclContext()->getRedeclContext()->isTranslationUnit() ||
               fd->isInStdNamespace();
  if (cLike && banned.count(base)) {
    error(loc, "dynamic allocation ('" + name + "') is not allowed in a real-time function");
    return unit(w_.call);
  }
  if (const AnnotateAttr* a = findAnnotation(fd, "crosscheck::cost")) {
    if (auto n = annotationArg(a, 0, ctx_); n && *n >= 0) {
      assume("cost of '" + fd->getQualifiedNameAsString() + "' is at most " + std::to_string(*n) +
             " (CROSSCHECK_COST)");
      return seq(unit(w_.call), unit(static_cast<std::uint64_t>(*n)));
    }
    error(loc, "CROSSCHECK_COST needs a non-negative constant");
    return unit(w_.call);
  }
  if (!stack_.empty() && fd->getCanonicalDecl() == cur().fn->getCanonicalDecl())
  {
    Cost self = unit(w_.call);
    self.rec = Sat::of(1);
    return self;
  }
  if (onStack(fd)) {
    error(loc, "mutual recursion through '" + fd->getQualifiedNameAsString() +
                   "' is not supported");
    return unit(w_.call);
  }
  if (const auto* md = dyn_cast<CXXMethodDecl>(fd); md && md->isTrivial() && !md->hasBody())
    return unit(w_.assign);
  if (const auto* cd = dyn_cast<CXXConstructorDecl>(fd); cd && cd->isTrivial()) return Cost{};

  const FunctionDecl* def = nullptr;
  if (fd->hasBody(def) && def->getBody() && !def->isDependentContext()) {
    // Costs computed while candidate invariants are being tested are discarded.
    if (!stack_.empty() && cur().speculative) return unit(w_.call);
    Context context = call ? contextFor(call, def) : Context{};
    if (!stack_.empty()) cur().summary.callees.insert({def->getCanonicalDecl(), context});
    // Copy what is needed: analysing callees may rehash the cache.
    const Summary& sm = analyzeFunction(def, context);
    bool ok = sm.ok;
    Sat wcet = sm.wcet;
    std::string reason = sm.reason;
    std::vector<std::string> assumptions = sm.assumptions;
    for (const std::string& a : assumptions) assume(a);
    if (!ok)
      error(loc, "call to '" + fd->getQualifiedNameAsString() + "' is not real-time safe: " +
                     (reason.empty() ? std::string("no cost bound") : reason),
            reason);
    Cost callee;
    callee.units = wcet;
    return seq(unit(w_.call), callee);
  }
  if (cLike && constantCost.count(base)) {
    if (fd->getBuiltinID() == 0 || base == name)
      assume("library function '" + name + "' is assumed to cost one call unit");
    return unit(w_.call);
  }
  if (fd->isNoReturn()) return unit(w_.call);  // the path ends here
  error(loc, "no definition is available for '" + fd->getQualifiedNameAsString() +
                 "'; declare its cost with CROSSCHECK_COST(n)");
  return unit(w_.call);
}

// ===========================================================================
// States.
// ===========================================================================

State Analyzer::mergeStates(const std::vector<State>& in) {
  if (in.size() == 1) return in.front();
  State out;
  out.flow = in.front().flow;
  // Facts: the common prefix (facts added on only some of the paths are dropped).
  std::size_t common = in.front().facts.size();
  for (const State& s : in) {
    std::size_t k = 0;
    while (k < common && k < s.facts.size() && s.facts[k] == in.front().facts[k]) ++k;
    common = k;
  }
  out.facts.assign(in.front().facts.begin(), in.front().facts.begin() + common);
  // Self-calls: exact only when all paths agree.
  out.selfCalls = in.front().selfCalls;
  for (const State& s : in)
    if (s.selfCalls != in.front().selfCalls) {
      if (!stack_.empty()) cur().recImprecise = true;
      if (s.selfCalls.size() > out.selfCalls.size()) out.selfCalls = s.selfCalls;
    }
  // Values: keep what agrees; otherwise a fresh symbol, with the interval hull
  // when the values differ by constants.
  for (const auto& [var, first] : in.front().val) {
    bool everywhere = true, same = true, constDiff = !first.poisoned();
    std::int64_t lo = 0, hi = 0;
    for (const State& s : in) {
      auto it = s.val.find(var);
      if (it == s.val.end()) { everywhere = false; break; }
      if (it->second != first) same = false;
      LinExpr d = it->second - first;
      if (d.isConstant()) {
        lo = std::min(lo, d.constantTerm());
        hi = std::max(hi, d.constantTerm());
      } else {
        constDiff = false;
      }
    }
    if (!everywhere) continue;
    if (same) {
      out.val[var] = first;
      continue;
    }
    LinExpr m = freshInt(var->getType(), var->getNameAsString());
    if (constDiff) {
      out.facts.push_back(ge(m, first + LinExpr::constant(lo)));
      out.facts.push_back(le(m, first + LinExpr::constant(hi)));
    } else if (in.size() <= 4) {
      // Keep `m <= v` (resp. `m >= v`) for each incoming value `v` that bounds
      // the value of the variable on every merged path. This retains clamps
      // such as `if (len > 8) len = 8;`.
      for (const State& cand : in) {
        const LinExpr& v = cand.val.at(var);
        if (v.poisoned()) continue;
        bool upper = true, lower = true;
        for (const State& s : in) {
          const LinExpr& w = s.val.at(var);
          if (upper && !(w == v) && !entails(syms_, s.facts, le(w, v))) upper = false;
          if (lower && !(w == v) && !entails(syms_, s.facts, ge(w, v))) lower = false;
          if (!upper && !lower) break;
        }
        if (upper) out.facts.push_back(le(m, v));
        if (lower) out.facts.push_back(ge(m, v));
      }
      // Interval join: a constant bound that holds on every merged path.
      Interval hull;
      bool first_ = true, live = false;
      for (const State& st : in) {
        std::optional<Interval> b = boundsOf(syms_, st.facts, st.val.at(var));
        if (!b) continue;  // unreachable path
        live = true;
        if (first_) { hull = *b; first_ = false; continue; }
        hull.lo = (hull.lo && b->lo) ? std::optional<std::int64_t>(std::min(*hull.lo, *b->lo)) : std::nullopt;
        hull.hi = (hull.hi && b->hi) ? std::optional<std::int64_t>(std::max(*hull.hi, *b->hi)) : std::nullopt;
      }
      if (live && hull.lo) out.facts.push_back(ge(m, LinExpr::constant(*hull.lo)));
      if (live && hull.hi) out.facts.push_back(le(m, LinExpr::constant(*hull.hi)));
    }
    out.val[var] = m;
  }
  return out;
}

void Analyzer::limitStates(std::vector<State>& states) {
  for (Flow f : {Flow::Normal, Flow::Return, Flow::Break, Flow::Continue}) {
    std::vector<State> same, rest;
    for (State& s : states) (s.flow == f ? same : rest).push_back(std::move(s));
    if (same.size() > opts_.maxPaths) {
      State m = mergeStates(same);
      m.flow = f;
      same.clear();
      same.push_back(std::move(m));
    }
    states = std::move(rest);
    for (State& s : same) states.push_back(std::move(s));
  }
}

State Analyzer::havoc(const State& s, const std::map<const VarDecl*, ModInfo>& mods,
                      std::map<const VarDecl*, SymId>* fresh) {
  State out = s;
  for (const auto& [var, info] : mods) {
    if (!tracked(var)) continue;
    if (info.declaredInside) {
      out.val.erase(var);
      continue;
    }
    auto [lo, hi] = symbolRange(var->getType(), ctx_);
    SymId id = syms_.fresh(var->getNameAsString(), lo, hi);
    out.val[var] = LinExpr::symbol(id);
    if (fresh) (*fresh)[var] = id;
  }
  return out;
}

std::optional<std::uint64_t> Analyzer::loopBoundMarker(const Stmt* body) {
  auto read = [&](const Stmt* s) -> std::optional<std::uint64_t> {
    const CallExpr* m = asMarker(s, "loop_bound");
    if (!m) return std::nullopt;
    Expr::EvalResult r;
    if (m->getArg(0)->isValueDependent() || !m->getArg(0)->EvaluateAsInt(r, ctx_)) {
      error(m->getExprLoc(), "CROSSCHECK_LOOP_BOUND needs a constant");
      return std::nullopt;
    }
    if (auto v = toInt64(r.Val.getInt()); v && *v >= 0) return static_cast<std::uint64_t>(*v);
    return std::nullopt;
  };
  if (!body) return std::nullopt;
  if (const auto* cs = dyn_cast<CompoundStmt>(body)) {
    for (const Stmt* s : cs->body())
      if (auto v = read(s)) return v;
    return std::nullopt;
  }
  return read(body);
}

std::string Analyzer::potentialString(const RankingResult& r,
                                      const std::vector<std::string>& names) {
  std::string out;
  auto term = [&](Rational q, const std::string& name) {
    if (q.num == 0) return;
    bool neg = q.num < 0;
    Rational a{neg ? -q.num : q.num, q.den};
    out += out.empty() ? (neg ? "-" : "") : (neg ? " - " : " + ");
    if (name.empty())
      out += a.str();
    else if (a.num == 1 && a.den == 1)
      out += name;
    else
      out += a.str() + "*" + name;
  };
  for (std::size_t j = 0; j < names.size() && j < r.weights.size(); ++j) term(r.weights[j], names[j]);
  term(r.offset, "");
  return out.empty() ? "0" : out;
}

// ===========================================================================
// Statements.
// ===========================================================================

Cost Analyzer::execDecl(const DeclStmt* ds, std::vector<State>& states) {
  Cost c{};
  for (const Decl* d : ds->decls()) {
    const auto* vd = dyn_cast<VarDecl>(d);
    if (!vd) continue;
    if (vd->getType()->isVariablyModifiedType())
      error(vd->getLocation(), "variable-length array (unbounded stack use) in a real-time function");
    if (vd->hasLocalStorage() && vd->needsDestruction(ctx_) != QualType::DK_none)
      error(vd->getLocation(), "local variable '" + vd->getNameAsString() +
                                   "' has a non-trivial destructor (hidden cost)");
    const Expr* init = vd->getInit();
    for (State& s : states) {
      if (s.flow != Flow::Normal) continue;
      LinExpr v = init ? eval(init, s) : LinExpr::poison();
      if (tracked(vd)) assignVar(vd, v, s);
    }
    // Costed after evaluation: the cost of a call uses the argument intervals
    // recorded while evaluating it (as everywhere below).
    if (init) c = seq(c, seq(exprCost(init), unit(isIntType(vd->getType()) ? w_.assign : 0)));
  }
  return c;
}

Cost Analyzer::execIf(const IfStmt* is, std::vector<State>& states) {
  if (is->isConsteval()) {
    error(is->getIfLoc(), "'if consteval' is not supported");
    return Cost{};
  }
  Cost c = exec(is->getInit(), states);
  if (const DeclStmt* cv = is->getConditionVariableDeclStmt()) c = seq(c, execDecl(cv, states));
  if (auto taken = is->getNondiscardedCase(ctx_)) return seq(c, exec(*taken, states));

  std::vector<State> thenStates, elseStates, out;
  for (State& s : states) {
    if (s.flow != Flow::Normal) {
      out.push_back(std::move(s));
      continue;
    }
    CondResult r = evalCond(is->getCond(), s);
    State t = s, e = std::move(s);
    assumeCond(t, r, true);
    assumeCond(e, r, false);
    thenStates.push_back(std::move(t));
    elseStates.push_back(std::move(e));
  }
  c = seq(c, seq(exprCost(is->getCond()), unit(w_.branch)));
  Cost ct = exec(is->getThen(), thenStates);
  Cost ce = exec(is->getElse(), elseStates);
  for (State& s : thenStates) out.push_back(std::move(s));
  for (State& s : elseStates) out.push_back(std::move(s));
  states = std::move(out);
  limitStates(states);
  return seq(c, alt(ct, ce));
}

Cost Analyzer::execSwitch(const SwitchStmt* ss, std::vector<State>& states) {
  Cost c = exec(ss->getInit(), states);
  if (const DeclStmt* cv = ss->getConditionVariableDeclStmt()) c = seq(c, execDecl(cv, states));
  std::vector<State> normals, out;
  for (State& s : states) {
    if (s.flow == Flow::Normal) {
      eval(ss->getCond(), s);
      normals.push_back(std::move(s));
    } else {
      out.push_back(std::move(s));
    }
  }
  c = seq(c, seq(exprCost(ss->getCond()), unit(w_.branch)));
  ModScan scan(ctx_);
  scan.TraverseStmt(const_cast<Stmt*>(ss->getBody()));
  // Every case label is reached with the entry state in which all variables
  // modified anywhere in the switch are unknown; the same state describes the
  // exit. The cost is the sum of all cases (sound with fall-through).
  State entry = normals.empty() ? State{} : mergeStates(normals);
  State any = havoc(entry, scan.mods);
  cur().switchStack.push_back(any);
  std::vector<State> inside;
  Cost body = flat(exec(ss->getBody(), inside));
  cur().switchStack.pop_back();
  if (!normals.empty()) out.push_back(any);
  for (State& s : inside)
    if (s.flow == Flow::Continue || s.flow == Flow::Return) out.push_back(std::move(s));
  states = std::move(out);
  limitStates(states);
  return seq(c, body);
}

Cost Analyzer::execRangeFor(const CXXForRangeStmt* fs, std::vector<State>& states) {
  Cost c = exec(fs->getInit(), states);
  c = seq(c, exec(fs->getRangeStmt(), states));
  c = seq(c, exec(fs->getBeginStmt(), states));
  c = seq(c, exec(fs->getEndStmt(), states));

  // Iteration count: the extent of a C array or of a std::array.
  std::optional<std::uint64_t> extent;
  QualType rt = fs->getRangeInit()->getType().getNonReferenceType();
  if (const ConstantArrayType* cat = ctx_.getAsConstantArrayType(rt)) {
    extent = cat->getSize().getLimitedValue();
  } else if (const auto* spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(rt->getAsCXXRecordDecl())) {
    if (spec->isInStdNamespace() && spec->getName() == "array" &&
        spec->getTemplateArgs().size() == 2 &&
        spec->getTemplateArgs()[1].getKind() == TemplateArgument::Integral)
      extent = spec->getTemplateArgs()[1].getAsIntegral().getLimitedValue();
  }
  std::optional<std::uint64_t> user = loopBoundMarker(fs->getBody());
  bool verified = extent.has_value();
  std::uint64_t k = 0;
  if (extent) {
    k = *extent;
  } else if (user) {
    k = *user;
    assume("range-for loop at line " + std::to_string(lineOf(fs->getForLoc())) + " runs at most " +
           std::to_string(k) + " times (CROSSCHECK_LOOP_BOUND)");
  } else {
    error(fs->getForLoc(), "cannot derive an iteration bound for this range-for loop; iterate over "
                           "a fixed-size array or add CROSSCHECK_LOOP_BOUND(n)");
  }

  std::vector<State> normals, out;
  for (State& s : states) (s.flow == Flow::Normal ? normals : out).push_back(std::move(s));
  State entry = normals.empty() ? State{} : mergeStates(normals);
  ModScan scan(ctx_);
  scan.TraverseStmt(const_cast<Stmt*>(fs->getBody()));
  scan.TraverseStmt(const_cast<Stmt*>(static_cast<const Stmt*>(fs->getLoopVarStmt())));
  State head = havoc(entry, scan.mods);

  FnCtx& fc = cur();
  ++fc.loopDepth;
  fc.switchStack.push_back(std::nullopt);
  std::vector<State> st{head};
  eval(fs->getCond(), st.front());
  Cost test = seq(exprCost(fs->getCond()), unit(w_.branch));
  Cost body = exec(fs->getLoopVarStmt(), st);
  body = flat(seq(body, exec(fs->getBody(), st)));
  Cost inc = exprCost(fs->getInc());
  bool early = false;
  for (State& s : st) {
    if (s.flow == Flow::Break || s.flow == Flow::Return) early = true;
    if (s.flow == Flow::Return) out.push_back(std::move(s));
  }
  fc.switchStack.pop_back();
  --fc.loopDepth;

  if (!fc.speculative) {
    LoopReport lr;
    lr.line = lineOf(fs->getForLoc());
    lr.bound = k;
    lr.verified = verified;
    lr.potential = verified ? "array extent" : "";
    fc.loops[fs] = lr;
  }
  if (!normals.empty()) out.push_back(havoc(entry, scan.mods));
  states = std::move(out);
  limitStates(states);
  Cost total = seq(times(Sat::of(k), seq(seq(test, body), inc)), test);
  if (early) total = seq(total, body);
  return seq(c, total);
}

Cost Analyzer::execLoop(const Stmt* loop, const Expr* cond, const Stmt* body, const Expr* inc,
                        bool isDo, std::optional<std::uint64_t> annotated,
                        std::vector<State>& states) {
  FnCtx& fc = cur();
  SourceLocation loc = loop->getBeginLoc();

  std::vector<State> normals, out;
  for (State& s : states) (s.flow == Flow::Normal ? normals : out).push_back(std::move(s));
  const bool reachable = !normals.empty();
  State origin = reachable ? mergeStates(normals) : State{};

  ModScan scan(ctx_);
  if (cond) scan.TraverseStmt(const_cast<Expr*>(cond));
  if (inc) scan.TraverseStmt(const_cast<Expr*>(inc));
  scan.TraverseStmt(const_cast<Stmt*>(body));

  ++fc.loopDepth;
  fc.switchStack.push_back(std::nullopt);

  // do-while: the body runs once before the first test.
  Cost pre{};
  bool earlyFirst = false;
  std::vector<State> firstBroken;
  State entry = origin;
  if (isDo) {
    std::vector<State> first{origin};
    pre = flat(exec(body, first));
    std::vector<State> cont;
    for (State& s : first) {
      if (s.flow == Flow::Break) {
        earlyFirst = true;
        firstBroken.push_back(std::move(s));
        continue;
      }
      if (s.flow == Flow::Return) { earlyFirst = true; out.push_back(std::move(s)); continue; }
      if (s.flow == Flow::Normal || s.flow == Flow::Continue) {
        s.flow = Flow::Normal;
        cont.push_back(std::move(s));
      }
    }
    entry = cont.empty() ? State{} : mergeStates(cont);
  }

  // Slots of the ranking template: tracked variables used by the loop and
  // declared outside it. Make sure each has a value on entry.
  std::vector<const VarDecl*> slots;
  for (const VarDecl* v : scan.refs) {
    if (!tracked(v)) continue;
    auto m = scan.mods.find(v);
    if (m != scan.mods.end() && m->second.declaredInside) continue;
    lookup(v, entry);
    slots.push_back(v);
  }
  std::sort(slots.begin(), slots.end(), [](const VarDecl* a, const VarDecl* b) {
    return a->getLocation() < b->getLocation();
  });

  // Loop-head state: modified variables become fresh symbols.
  std::map<const VarDecl*, SymId> headSym;
  State head = havoc(entry, scan.mods, &headSym);
  std::map<SymId, LinExpr> toEntry;
  for (const auto& [var, id] : headSym) {
    auto it = entry.val.find(var);
    if (it != entry.val.end()) toEntry[id] = it->second;
  }

  // Candidate invariants over the head symbols, to be proved inductive.
  struct Candidate {
    Constraint inv;
    std::optional<Constraint> strict;  ///< added to the guard when `inv` holds
  };
  std::vector<Candidate> candidates;
  for (const auto& [var, id] : headSym) {
    const ModInfo& info = scan.mods.at(var);
    auto it = entry.val.find(var);
    if (it == entry.val.end()) continue;
    if (info.nonNegative) candidates.push_back({ge(LinExpr::symbol(id), it->second), std::nullopt});
    if (info.nonPositive) candidates.push_back({le(LinExpr::symbol(id), it->second), std::nullopt});
  }
  if (cond) {
    // `a != b` in the guard: try the invariants a <= b and a >= b, which turn
    // the disequality into a strict inequality.
    ++fc.speculative;
    State probe = head;
    CondResult r = evalCond(cond, probe);
    --fc.speculative;
    if (probe.val == head.val) {
      for (const auto& [a, b] : r.neqTrue) {
        Constraint up{le(a, b).e.substitute(toEntry)}, down{ge(a, b).e.substitute(toEntry)};
        if (entails(syms_, entry.facts, up))
          candidates.push_back({le(a, b), lt(a, b)});
        else if (entails(syms_, entry.facts, down))
          candidates.push_back({ge(a, b), gt(a, b)});
      }
    }
  }

  struct Iteration {
    std::vector<State> complete, returned, broken;
    bool early = false;
    Cost test{}, body{}, inc{};
  };
  auto runIteration = [&](const std::vector<Candidate>& invs) {
    Iteration it;
    State s = head;
    for (const Candidate& c : invs) s.facts.push_back(c.inv);
    if (cond) {
      CondResult r = evalCond(cond, s);
      it.test = seq(exprCost(cond), unit(w_.branch));
      assumeCond(s, r, true);
      for (const Candidate& c : invs)
        if (c.strict) s.facts.push_back(*c.strict);
    }
    std::vector<State> st{std::move(s)};
    it.body = flat(exec(body, st));
    for (State& x : st)
      if (x.flow == Flow::Continue) x.flow = Flow::Normal;
    if (inc) {
      for (State& x : st)
        if (x.flow == Flow::Normal) eval(inc, x);
      it.inc = exprCost(inc);
    }
    for (State& x : st) {
      if (x.flow == Flow::Normal) it.complete.push_back(std::move(x));
      else {
        it.early = true;
        if (x.flow == Flow::Return) it.returned.push_back(std::move(x));
        else if (x.flow == Flow::Break) it.broken.push_back(std::move(x));
      }
    }
    return it;
  };

  // Houdini-style refinement: drop candidates that are not inductive.
  ++fc.speculative;
  for (;;) {
    Iteration it = runIteration(candidates);
    std::vector<Candidate> kept;
    for (const Candidate& c : candidates) {
      bool ok = entails(syms_, entry.facts, Constraint{c.inv.e.substitute(toEntry)});
      for (const State& p : it.complete) {
        if (!ok) break;
        std::map<SymId, LinExpr> toPost;
        for (const auto& [var, id] : headSym) {
          auto v = p.val.find(var);
          toPost[id] = v == p.val.end() ? LinExpr::poison() : v->second;
        }
        ok = entails(syms_, p.facts, Constraint{c.inv.e.substitute(toPost)});
      }
      if (ok) kept.push_back(c);
    }
    bool stable = kept.size() == candidates.size();
    candidates = std::move(kept);
    if (stable) break;
  }
  --fc.speculative;

  Iteration it = runIteration(candidates);
  fc.switchStack.pop_back();
  --fc.loopDepth;

  // Ranking potential.
  RankingProblem problem;
  problem.slots = slots.size();
  std::vector<std::string> names;
  for (const VarDecl* v : slots) {
    problem.entry.push_back(entry.val.at(v));
    names.push_back(v->getNameAsString());
  }
  problem.entryFacts = entry.facts;
  for (const State& p : it.complete) {
    RankingProblem::Step step;
    for (const VarDecl* v : slots) {
      step.pre.push_back(head.val.at(v));
      auto pv = p.val.find(v);
      step.post.push_back(pv == p.val.end() ? LinExpr::poison() : pv->second);
    }
    step.premises = p.facts;
    problem.steps.push_back(std::move(step));
  }
  std::optional<std::uint64_t> user = annotated ? annotated : loopBoundMarker(body);
  std::optional<RankingResult> rank = synthesizeRanking(syms_, problem);

  LoopReport lr;
  lr.line = lineOf(loc);
  std::uint64_t k = 0;
  if (rank && (!user || rank->bound <= *user)) {
    k = rank->bound;
    lr.verified = true;
    lr.potential = potentialString(*rank, names);
  } else if (user) {
    k = *user;
    assume("loop at line " + std::to_string(lr.line) + " runs at most " + std::to_string(k) +
           " times (user annotation)");
  } else {
    error(loc, "cannot derive an iteration bound for this loop; make the bound provable "
               "(CROSSCHECK_RANGE / CROSSCHECK_REQUIRE / CROSSCHECK_ASSUME on its inputs) or "
               "state it with CROSSCHECK_LOOP_BOUND(n)");
  }
  lr.bound = k;
  if (!fc.speculative) fc.loops[loop] = lr;

  // Exit states. The loop is left either through its guard, at a loop head
  // where the invariants hold and the guard is false, or through a `break`,
  // in a state reached by one of the paths of the generic iteration (whose
  // head satisfies the invariants) or of the first body of a do-while.
  bool early = it.early || earlyFirst;
  for (State& r : it.returned) out.push_back(std::move(r));
  if (reachable) {
    std::size_t before = out.size();
    if (cond) {
      std::map<const VarDecl*, SymId> exitSym;
      State exit = havoc(isDo ? origin : entry, scan.mods, &exitSym);
      if (isDo) {
        for (const VarDecl* v : slots)
          if (!exitSym.count(v) && !exit.val.count(v)) exit.val[v] = entry.val.at(v);
        exit.facts = entry.facts;  // the test is reached after a completed first body
      }
      std::map<SymId, LinExpr> toExit;
      for (const auto& [var, id] : headSym)
        if (exitSym.count(var)) toExit[id] = LinExpr::symbol(exitSym[var]);
      for (const Candidate& c : candidates) exit.facts.push_back(Constraint{c.inv.e.substitute(toExit)});
      CondResult r = evalCond(cond, exit);
      assumeCond(exit, r, false);
      out.push_back(std::move(exit));
    }
    for (std::vector<State>* group : {&it.broken, &firstBroken})
      for (State& b : *group) {
        b.flow = Flow::Normal;
        out.push_back(std::move(b));
      }
    // `for (;;)` without `break`: nothing leaves the loop normally. Keep one
    // unconstrained state so that the code after it is still analysed.
    if (out.size() == before) out.push_back(havoc(isDo ? origin : entry, scan.mods));
  }
  states = std::move(out);
  limitStates(states);

  // K complete iterations, the final failing test, and possibly one partial
  // iteration that leaves the loop early.
  Cost total = seq(times(Sat::of(k), seq(seq(it.test, it.body), it.inc)), it.test);
  if (early) total = seq(total, it.body);
  return seq(pre, total);
}

Cost Analyzer::exec(const Stmt* st, std::vector<State>& states) {
  if (!st) return Cost{};

  if (const auto* cs = dyn_cast<CompoundStmt>(st)) {
    Cost c{};
    for (const Stmt* child : cs->body()) {
      // A case label (or a label) can be reached although the code before it
      // returned: forget the "returned" distinction at that point.
      if (isa<SwitchCase>(child) || isa<LabelStmt>(child)) c = flat(c);
      c = seq(c, exec(child, states));
    }
    return c;
  }
  if (const auto* ds = dyn_cast<DeclStmt>(st)) return execDecl(ds, states);
  if (const auto* is = dyn_cast<IfStmt>(st)) return execIf(is, states);
  if (const auto* ws = dyn_cast<WhileStmt>(st)) {
    if (ws->getConditionVariable()) {
      error(ws->getWhileLoc(), "condition variables in 'while' are not supported");
      return Cost{};
    }
    return execLoop(ws, ws->getCond(), ws->getBody(), nullptr, false, std::nullopt, states);
  }
  if (const auto* dw = dyn_cast<DoStmt>(st))
    return execLoop(dw, dw->getCond(), dw->getBody(), nullptr, true, std::nullopt, states);
  if (const auto* fs = dyn_cast<ForStmt>(st)) {
    if (fs->getConditionVariable()) {
      error(fs->getForLoc(), "condition variables in 'for' are not supported");
      return Cost{};
    }
    Cost c = exec(fs->getInit(), states);
    std::optional<std::uint64_t> annotated;
    if (const auto* ds = dyn_cast_or_null<DeclStmt>(fs->getInit()))
      for (const Decl* d : ds->decls())
        if (const AnnotateAttr* a = findAnnotation(d, "crosscheck::bounded")) {
          if (auto n = annotationArg(a, 0, ctx_); n && *n >= 0)
            annotated = static_cast<std::uint64_t>(*n);
          else
            error(d->getLocation(), "CROSSCHECK_BOUNDED needs a non-negative constant");
        }
    return seq(c, execLoop(fs, fs->getCond(), fs->getBody(), fs->getInc(), false, annotated, states));
  }
  if (const auto* rf = dyn_cast<CXXForRangeStmt>(st)) return execRangeFor(rf, states);
  if (const auto* ss = dyn_cast<SwitchStmt>(st)) return execSwitch(ss, states);
  if (const auto* sc = dyn_cast<SwitchCase>(st)) {
    FnCtx& fc = cur();
    if (fc.switchStack.empty() || !fc.switchStack.back()) {
      error(sc->getKeywordLoc(), "case label inside a loop nested in its switch is not supported");
      return exec(sc->getSubStmt(), states);
    }
    std::vector<State> next;
    for (State& s : states)
      if (s.flow != Flow::Normal) next.push_back(std::move(s));
    next.push_back(*fc.switchStack.back());
    states = std::move(next);
    return exec(sc->getSubStmt(), states);
  }
  if (const auto* rs = dyn_cast<ReturnStmt>(st)) {
    for (State& s : states) {
      if (s.flow != Flow::Normal) continue;
      if (rs->getRetValue()) eval(rs->getRetValue(), s);
      s.flow = Flow::Return;
    }
    return returning(seq(exprCost(rs->getRetValue()), unit(w_.ret)));
  }
  if (isa<BreakStmt>(st) || isa<ContinueStmt>(st)) {
    for (State& s : states)
      if (s.flow == Flow::Normal) s.flow = isa<BreakStmt>(st) ? Flow::Break : Flow::Continue;
    return unit(w_.branch);
  }
  if (isa<NullStmt>(st)) return Cost{};
  if (const auto* as = dyn_cast<AttributedStmt>(st)) return exec(as->getSubStmt(), states);
  if (const auto* ls = dyn_cast<LabelStmt>(st)) return exec(ls->getSubStmt(), states);
  if (const auto* ts = dyn_cast<CXXTryStmt>(st)) {
    error(ts->getTryLoc(), "'try'/'catch' is not allowed in a real-time function");
    return exec(ts->getTryBlock(), states);
  }
  if (isa<GotoStmt>(st) || isa<IndirectGotoStmt>(st)) {
    error(st->getBeginLoc(), "'goto' is not supported (unstructured control flow)");
    return Cost{};
  }
  if (const auto* e = dyn_cast<Expr>(st)) {
    if (asMarker(e, "loop_bound")) return Cost{};
    if (asMarker(e, "require")) {
      // Leading preconditions are consumed by analyzeFunction.
      FnCtx& fc = cur();
      const auto* body = dyn_cast_or_null<CompoundStmt>(fc.fn->getBody());
      bool leading = false;
      if (body)
        for (const Stmt* s : body->body()) {
          if (s == st) leading = true;
          if (!asMarker(s, "require")) break;
        }
      if (!leading)
        error(e->getExprLoc(), "CROSSCHECK_REQUIRE must come first in the function body; use "
                               "CROSSCHECK_ASSUME for facts established later");
      return Cost{};
    }
    if (const CallExpr* m = asMarker(e, "assume")) {
      assume("assumed at line " + std::to_string(lineOf(e->getExprLoc())) + " (CROSSCHECK_ASSUME)");
      for (State& s : states) {
        if (s.flow != Flow::Normal) continue;
        ++cur().speculative;  // unevaluated operand: no contract checks, no call records
        CondResult r = evalCond(m->getArg(0), s);
        --cur().speculative;
        assumeCond(s, r, true);
      }
      return Cost{};
    }
    for (State& s : states)
      if (s.flow == Flow::Normal) eval(e, s);
    return exprCost(e);
  }
  error(st->getBeginLoc(), std::string("unsupported statement (") + st->getStmtClassName() + ")");
  return Cost{};
}

// ===========================================================================
// Functions.
// ===========================================================================

/// Sets up the analysis of `def` in `fc`: tracked locals, parameter symbols
/// and declared preconditions. Returns the initial state.
State Analyzer::enterFunction(const FunctionDecl* def, FnCtx& fc) {
  // Which locals can be tracked?
  TrackScan ts;
  ts.TraverseStmt(def->getBody());
  auto trackable = [&](const VarDecl* v) {
    QualType t = v->getType();
    return isIntType(t) && !t.isVolatileQualified() && v->hasLocalStorage() &&
           !ts.escaped.count(v) && ts.total[v] == ts.benign[v];
  };
  for (const auto& [v, n] : ts.total)
    if (trackable(v)) fc.tracked.insert(v);

  // Parameters and their preconditions.
  State init;
  fc.summary.paramSyms.assign(def->getNumParams(), std::nullopt);
  for (unsigned i = 0; i < def->getNumParams(); ++i) {
    const ParmVarDecl* p = def->getParamDecl(i);
    if (!isIntType(p->getType()) || p->getType().isVolatileQualified()) continue;
    auto [lo, hi] = symbolRange(p->getType(), ctx_);
    SymId id = syms_.fresh(p->getNameAsString().empty() ? "param" : p->getNameAsString(), lo, hi);
    fc.summary.paramSyms[i] = id;
    fc.slotSyms.push_back(id);
    fc.slotParams.push_back(i);
    if (trackable(p) || ts.total[p] == 0) {
      fc.tracked.insert(p);
      init.val[p] = LinExpr::symbol(id);
    }
    const AnnotateAttr* range = nullptr;
    for (const FunctionDecl* r : def->redecls())
      if (i < r->getNumParams() && !range) range = findAnnotation(r->getParamDecl(i), "crosscheck::range");
    if (range) {
      auto rl = annotationArg(range, 0, ctx_), rh = annotationArg(range, 1, ctx_);
      if (!rl || !rh || *rl > *rh) {
        error(p->getLocation(), "CROSSCHECK_RANGE needs two constants lo <= hi");
      } else {
        fc.summary.requires_.push_back(ge(LinExpr::symbol(id), LinExpr::constant(*rl)));
        fc.summary.requires_.push_back(le(LinExpr::symbol(id), LinExpr::constant(*rh)));
      }
    }
  }
  if (const auto* body = dyn_cast<CompoundStmt>(def->getBody()))
    for (const Stmt* s : body->body()) {
      const CallExpr* m = asMarker(s, "require");
      if (!m) break;
      ++fc.speculative;
      CondResult r = evalCond(m->getArg(0), init);
      --fc.speculative;
      for (const Constraint& c : r.ifTrue) fc.summary.requires_.push_back(c);
    }
  init.facts = fc.summary.requires_;
  return init;
}

/// The declared preconditions of `def`, without analysing its body.
const Contract& Analyzer::contractOf(const FunctionDecl* def) {
  const FunctionDecl* key = def->getCanonicalDecl();
  if (auto it = contracts_.find(key); it != contracts_.end()) return it->second;
  stack_.push_back(std::make_unique<FnCtx>());
  FnCtx& fc = cur();
  fc.fn = def;
  fc.speculative = 1;  // nothing is reported from here
  enterFunction(def, fc);
  Contract ct{fc.summary.paramSyms, fc.summary.requires_};
  stack_.pop_back();
  return contracts_.emplace(key, std::move(ct)).first->second;
}

/// Does the body of `def` call `def`? (Such functions are never specialised:
/// the facts of a calling context hold for the first activation only.)
bool Analyzer::callsItself(const FunctionDecl* def) {
  const FunctionDecl* key = def->getCanonicalDecl();
  if (auto it = selfRecursive_.find(key); it != selfRecursive_.end()) return it->second;
  struct Scan : RecursiveASTVisitor<Scan> {
    const FunctionDecl* self = nullptr;
    bool found = false;
    bool VisitDeclRefExpr(DeclRefExpr* e) {
      if (const auto* fd = dyn_cast<FunctionDecl>(e->getDecl()))
        if (fd->getCanonicalDecl() == self) found = true;
      return !found;
    }
  } scan;
  scan.self = key;
  scan.TraverseStmt(def->getBody());
  return selfRecursive_[key] = scan.found;
}

/// Joins into the record of `call` the interval of every integer argument in
/// state `s`. Only done outside speculative walks: the costs computed there
/// are discarded.
void Analyzer::recordCall(const CallExpr* call, const FunctionDecl* fd,
                          const std::vector<LinExpr>& args,
                          const std::vector<const Expr*>& argExprs, State& s) {
  FnCtx& fc = cur();
  if (fc.speculative) return;
  const FunctionDecl* def = nullptr;
  if (!fd->hasBody(def) || !def->getBody() || def->isDependentContext()) return;
  if (def->getCanonicalDecl() == fc.fn->getCanonicalDecl() || callsItself(def)) return;

  Context here(def->getNumParams());
  for (unsigned i = 0; i < def->getNumParams() && i < args.size(); ++i) {
    QualType pt = def->getParamDecl(i)->getType();
    if (!isIntType(pt) || pt.isVolatileQualified() || args[i].poisoned()) continue;
    // The argument must already have the parameter's type, so that its value
    // is the parameter's value (no conversion in between).
    if (!ctx_.hasSameUnqualifiedType(argExprs[i]->getType(), pt)) continue;
    std::optional<Interval> b = boundsOf(syms_, s.facts, args[i]);
    if (!b) return;  // contradictory facts: this state stands for no execution
    here[i] = *b;
  }
  CallRecord& rec = fc.calls[call];
  if (!rec.any) {
    rec.callee = def->getCanonicalDecl();
    rec.hull = std::move(here);
    rec.any = true;
    return;
  }
  if (rec.callee != def->getCanonicalDecl() || rec.hull.size() != here.size()) {
    rec.hull.assign(rec.hull.size(), Interval{});
    return;
  }
  for (std::size_t i = 0; i < here.size(); ++i) {
    Interval& h = rec.hull[i];
    h.lo = (h.lo && here[i].lo) ? std::optional<std::int64_t>(std::min(*h.lo, *here[i].lo)) : std::nullopt;
    h.hi = (h.hi && here[i].hi) ? std::optional<std::int64_t>(std::max(*h.hi, *here[i].hi)) : std::nullopt;
  }
}

/// The context in which `def` is analysed for `call`: the recorded argument
/// intervals, or no context when nothing useful is known, when the call was
/// never evaluated, or when `def` already has many specialised analyses.
Context Analyzer::contextFor(const CallExpr* call, const FunctionDecl* def) {
  constexpr unsigned kMaxSpecialisations = 8;
  if (stack_.empty()) return {};
  const FunctionDecl* key = def->getCanonicalDecl();
  auto it = cur().calls.find(call);
  if (it == cur().calls.end() || !it->second.any || it->second.callee != key) return {};
  const Context& hull = it->second.hull;
  if (std::all_of(hull.begin(), hull.end(), [](const Interval& i) { return i.unconstrained(); }))
    return {};
  if (cache_.count({key, hull})) return hull;
  if (specialisations_[key] >= kMaxSpecialisations) return {};
  ++specialisations_[key];
  return hull;
}

const Summary& Analyzer::analyzeFunction(const FunctionDecl* def, const Context& context) {
  SummaryKey key{def->getCanonicalDecl(), context};
  if (auto it = cache_.find(key); it != cache_.end()) return it->second;

  stack_.push_back(std::make_unique<FnCtx>());
  FnCtx& fc = cur();
  fc.fn = def;
  FunctionReport& rep = fc.summary.report;
  rep.name = def->getQualifiedNameAsString();
  {
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(def->getLocation()));
    if (p.isValid()) {
      rep.file = p.getFilename();
      rep.line = p.getLine();
    }
  }

  State init = enterFunction(def, fc);
  // Calling context: facts on the parameter symbols, proved at the call sites
  // this analysis is used for (never for functions that call themselves).
  for (std::size_t i = 0; i < context.size() && i < fc.summary.paramSyms.size(); ++i) {
    if (!fc.summary.paramSyms[i]) continue;
    LinExpr p = LinExpr::symbol(*fc.summary.paramSyms[i]);
    if (context[i].lo) init.facts.push_back(ge(p, LinExpr::constant(*context[i].lo)));
    if (context[i].hi) init.facts.push_back(le(p, LinExpr::constant(*context[i].hi)));
  }

  // Walk the body.
  Cost cost{};
  std::vector<State> states{init};
  if (const auto* ctor = dyn_cast<CXXConstructorDecl>(def))
    for (const CXXCtorInitializer* ci : ctor->inits()) {
      eval(ci->getInit(), states.front());
      cost = seq(cost, seq(exprCost(ci->getInit()), unit(w_.assign)));
    }
  if (const auto* dtor = dyn_cast<CXXDestructorDecl>(def); dtor && !dtor->getParent()->hasTrivialDestructor()) {
    for (const FieldDecl* f : dtor->getParent()->fields())
      if (f->getType().isDestructedType() != QualType::DK_none)
        error(def->getLocation(), "destructor of a class with non-trivially destructible members");
  }
  cost = flat(seq(cost, exec(def->getBody(), states)));

  // Recursion.
  Sat total = cost.units;
  if (!(cost.rec == Sat::of(0))) {
    std::vector<std::string> names;
    std::vector<LinExpr> entry;
    for (std::size_t j = 0; j < fc.slotSyms.size(); ++j) {
      entry.push_back(LinExpr::symbol(fc.slotSyms[j]));
      names.push_back(def->getParamDecl(fc.slotParams[j])->getNameAsString());
    }
    // (a) depth potential: nodes <= 1 + b + ... + b^D.
    RankingProblem depth;
    depth.slots = entry.size();
    depth.entry = entry;
    depth.entryFacts = fc.summary.requires_;
    for (const RecSite& site : fc.recSites)
      depth.steps.push_back(RankingProblem::Step{entry, site.args, site.premises});
    std::optional<RankingResult> d = synthesizeRanking(syms_, depth);
    // (b) size potential: U(x) >= 1 + sum U(children), path by path.
    std::optional<RankingResult> u;
    if (!fc.recImprecise) {
      SizeProblem size;
      size.slots = entry.size();
      size.entry = entry;
      size.entryFacts = fc.summary.requires_;
      for (const State& s : states)
        size.paths.push_back(SizeProblem::Path{entry, s.selfCalls, s.facts});
      u = synthesizeSizePotential(syms_, size);
    }
    Sat byDepth = d ? treeNodes(cost.rec, Sat::of(d->bound)) : Sat::infinite();
    Sat bySize = u ? Sat::of(u->bound) : Sat::infinite();
    Sat nodes = byDepth;
    bool useSize = !bySize.inf && (byDepth.inf || bySize.v < byDepth.v);
    if (useSize) nodes = bySize;
    if (nodes.inf) {
      error(def->getLocation(),
            "cannot bound the recursion of '" + rep.name +
                "'; give its integer parameters CROSSCHECK_RANGE / CROSSCHECK_REQUIRE "
                "preconditions under which an affine potential decreases at every call");
    } else {
      RecursionReport rr;
      rr.activations = nodes.v;
      rr.branching = cost.rec.inf ? 0 : cost.rec.v;
      if (d) rr.depth = d->bound;
      rr.potential = useSize ? "size potential " + potentialString(*u, names)
                             : "depth potential " + potentialString(*d, names);
      rep.recursion = rr;
    }
    total = nodes * cost.units;
  }
  if (total.inf && fc.summary.ok)
    error(def->getLocation(), "the cost bound of '" + rep.name + "' is not finite");

  if (!fc.summary.requires_.empty())
    assume("preconditions of '" + rep.name + "' hold at its external call sites");

  fc.summary.wcet = total;
  rep.bounded = !total.inf && fc.summary.ok;
  rep.wcet = total.inf ? 0 : total.v;
  for (const auto& [stmt, lr] : fc.loops) rep.loops.push_back(lr);
  std::sort(rep.loops.begin(), rep.loops.end(),
            [](const LoopReport& a, const LoopReport& b) { return a.line < b.line; });
  rep.assumptions = fc.summary.assumptions;
  rep.ok = fc.summary.ok;

  Summary done = std::move(fc.summary);
  stack_.pop_back();
  return cache_.emplace(std::move(key), std::move(done)).first->second;
}

// ===========================================================================
// Translation-unit driver.
// ===========================================================================

class Collector : public RecursiveASTVisitor<Collector> {
 public:
  Collector(ASTContext& ctx, bool all) : ctx_(ctx), all_(all) {}
  std::vector<const FunctionDecl*> roots;

  bool shouldVisitTemplateInstantiations() const { return true; }
  bool VisitFunctionDecl(FunctionDecl* fd) {
    if (!fd->doesThisDeclarationHaveABody() || fd->isDependentContext()) return true;
    bool annotated = findAnnotation(fd, "crosscheck::realtime") ||
                     findAnnotation(fd, "crosscheck::deadline");
    bool inMain = ctx_.getSourceManager().isInMainFile(
        ctx_.getSourceManager().getExpansionLoc(fd->getLocation()));
    if (annotated || (all_ && inMain && !fd->isImplicit())) roots.push_back(fd);
    return true;
  }

 private:
  ASTContext& ctx_;
  bool all_;
};

/// Fills the "in context" fields of the report: what holds for a function in
/// the calling contexts in which the program actually uses it. The analyses
/// that count are those reachable, through the calls they rely on, from the
/// entry functions: the function named by the `entry` option, or else every
/// analysed function that no analysed function calls.
void Analyzer::fillInContext(Report& report, const std::vector<const FunctionDecl*>& order) {
  std::set<const FunctionDecl*> called;
  for (const auto& [key, sm] : cache_)
    for (const SummaryKey& c : sm.callees) called.insert(c.first);
  std::vector<SummaryKey> work;
  for (std::size_t i = 0; i < order.size(); ++i) {
    bool entry = opts_.entry.empty() ? !called.count(order[i]) : report.functions[i].name == opts_.entry;
    if (entry) work.push_back({order[i], Context{}});
  }
  std::set<SummaryKey> reach;
  while (!work.empty()) {
    SummaryKey k = std::move(work.back());
    work.pop_back();
    auto it = cache_.find(k);
    if (it == cache_.end() || !reach.insert(k).second) continue;
    for (const SummaryKey& c : it->second.callees) work.push_back(c);
  }
  for (std::size_t i = 0; i < order.size(); ++i) {
    FunctionReport& f = report.functions[i];
    std::vector<const FunctionReport*> uses;
    for (const SummaryKey& k : reach)
      if (k.first == order[i]) uses.push_back(&cache_.at(k).report);
    if (uses.empty()) continue;
    f.reachable = true;
    f.contexts = static_cast<unsigned>(uses.size());
    bool allBounded = true;
    std::uint64_t worst = 0;
    for (const FunctionReport* u : uses) {
      allBounded = allBounded && u->bounded;
      worst = std::max(worst, u->wcet);
    }
    if (allBounded) f.wcetInContext = worst;
    for (std::size_t j = 0; j < f.loops.size(); ++j) {
      bool all = true;
      std::uint64_t k = 0;
      for (const FunctionReport* u : uses) {
        if (u->loops.size() != f.loops.size() || u->loops[j].line != f.loops[j].line ||
            !u->loops[j].verified) {
          all = false;
          break;
        }
        k = std::max(k, u->loops[j].bound);
      }
      if (all) f.loops[j].inContext = k;
    }
  }
}

Report Analyzer::run() {
  Collector collector(ctx_, opts_.analyzeAll);
  collector.TraverseDecl(ctx_.getTranslationUnitDecl());

  Report report;
  std::set<const FunctionDecl*> seen;
  std::vector<const FunctionDecl*> order;
  for (const FunctionDecl* fd : collector.roots) {
    if (!seen.insert(fd->getCanonicalDecl()).second) continue;
    order.push_back(fd->getCanonicalDecl());
    FunctionReport rep = analyzeFunction(fd).report;

    DiagnosticsEngine& diags = ctx_.getDiagnostics();
    if (const AnnotateAttr* a = findAnnotation(fd, "crosscheck::deadline")) {
      auto n = annotationArg(a, 0, ctx_);
      if (!n || *n < 0) {
        std::string msg = "CROSSCHECK_DEADLINE needs a non-negative constant";
        diags.Report(fd->getLocation(), errorId_) << msg;
        rep.errors.push_back(msg);
        rep.ok = false;
      } else {
        rep.deadline = static_cast<std::uint64_t>(*n);
        if (rep.bounded && rep.wcet > *rep.deadline) {
          std::string msg = "worst-case cost bound " + std::to_string(rep.wcet) + " of '" +
                            rep.name + "' exceeds its deadline " + std::to_string(*rep.deadline);
          diags.Report(fd->getLocation(), errorId_) << msg;
          rep.errors.push_back(msg);
          rep.ok = false;
        }
      }
    }
    if (rep.bounded) {
      std::string msg = "'" + rep.name + "': worst-case cost bound " + std::to_string(rep.wcet) +
                        " units";
      if (rep.deadline) msg += " (deadline " + std::to_string(*rep.deadline) + ")";
      if (!rep.assumptions.empty())
        msg += ", under " + std::to_string(rep.assumptions.size()) + " assumption(s)";
      diags.Report(fd->getLocation(), remarkId_) << msg;
    }
    report.functions.push_back(std::move(rep));
  }
  fillInContext(report, order);
  return report;
}

}  // namespace

Report analyzeTranslationUnit(ASTContext& context, const Options& options) {
  Analyzer analyzer(context, options);
  return analyzer.run();
}

}  // namespace crosscheck
