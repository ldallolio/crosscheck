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
#include <cctype>
#include <functional>
#include <map>
#include <numeric>
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
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"

#include "../core/Cert.hpp"
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
  // C++: `crosscheck::detail::NAME`; C: `crosscheck_detail_NAME` (attributes.hpp).
  if (!fd || (fd->getQualifiedNameAsString() != ("crosscheck::detail::" + name.str()) &&
              fd->getQualifiedNameAsString() != ("crosscheck_detail_" + name.str())))
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
  /// The global variables a call may modify (set by the analyser): a call in the loop
  /// modifies them, so they are loop-modified variables too.
  std::function<std::set<const VarDecl*>(const CallExpr*)> callWrites;
  bool VisitCallExpr(CallExpr* c) {
    if (callWrites)
      for (const VarDecl* g : callWrites(c)) {
        ModInfo& m = mods[g];
        m.nonNegative = m.nonPositive = false;
        refs.insert(g);
      }
    return true;
  }
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

struct LoopPotential;

struct Summary {
  bool ok = true;
  /// For certificates: the loops' potentials, the tracked variables, and the
  /// analysis used for each call (filled when the analysis ends).
  std::shared_ptr<const std::map<const Stmt*, struct LoopPotential>> potentials;
  std::set<const VarDecl*> tracked;
  std::map<const CallExpr*, SummaryKey> callKeys;
  /// Analyses of callees this analysis relies on.
  std::set<SummaryKey> callees;
  Sat wcet;
  std::vector<std::string> assumptions;
  /// Symbols standing for the integer parameters (by parameter index).
  std::vector<std::optional<SymId>> paramSyms;
  /// Preconditions over `paramSyms` (CROSSCHECK_RANGE, CROSSCHECK_REQUIRE).
  std::vector<Constraint> requires_;
  /// Facts assumed of the inputs (option input-range): true at entry, listed as an
  /// assumption, not checked at call sites.
  std::vector<Constraint> assumedInputs;
  /// Integer fields read through pointer parameters, and the symbols of their values at
  /// entry (assumed unchanged while the function runs).
  std::map<std::pair<const ParmVarDecl*, const FieldDecl*>, SymId> fieldSyms;
  /// Why the function is rejected (first violation found), if it is.
  std::string reason;
  FunctionReport report;
};

struct RecSite {
  std::vector<Constraint> premises;
  std::vector<LinExpr> args;  ///< one entry per recursion slot
};

/// The potential the analysis proved for a loop, kept for certificate emission.
struct LoopPotential {
  std::vector<const VarDecl*> slots;
  RankingResult rank;
};

struct FnCtx {
  const FunctionDecl* fn = nullptr;
  std::map<const Stmt*, LoopPotential> potentials;
  std::map<const CallExpr*, SummaryKey> callKeys;
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
    if (!opts.contractsPath.empty()) loadContracts(opts.contractsPath);
  }

  Report run();

 private:
  // -- library contracts (docs/contracts.md) ------------------------------------
  /// A trusted cost bound `c + sum perArg[i] * max(0, arg_i)` of a function.
  struct LibContract {
    std::uint64_t c = 0;
    std::map<unsigned, std::uint64_t> perArg;
    std::string text;  ///< the bound as written in the report
  };
  std::map<std::string, LibContract> libContracts_;
  std::string libContractsFor_;  ///< the "implementation" field of the contract file
  void loadContracts(const std::string& path) {
    DiagnosticsEngine& d = ctx_.getDiagnostics();
    auto fail = [&](const std::string& why) { d.Report(errorId_) << ("contract file '" + path + "': " + why); };
    auto buf = llvm::MemoryBuffer::getFile(path);
    if (!buf) return fail("cannot be read");
    llvm::Expected<llvm::json::Value> v = llvm::json::parse((*buf)->getBuffer());
    if (!v) { fail(llvm::toString(v.takeError())); return; }
    const llvm::json::Object* o = v->getAsObject();
    if (!o || o->getString("format") != std::optional<llvm::StringRef>("crosscheck-contracts"))
      return fail("not a contract file (format must be \"crosscheck-contracts\")");
    if (auto impl = o->getString("implementation")) libContractsFor_ = impl->str();
    const llvm::json::Array* cs = o->getArray("contracts");
    if (!cs) return fail("no \"contracts\" array");
    for (const llvm::json::Value& e : *cs) {
      const llvm::json::Object* c = e.getAsObject();
      std::optional<llvm::StringRef> name = c ? c->getString("function") : std::nullopt;
      const llvm::json::Object* cost = c ? c->getObject("cost") : nullptr;
      std::optional<std::int64_t> k = cost ? cost->getInteger("c") : std::nullopt;
      if (!name || !k || *k < 0) return fail("each contract needs \"function\" and \"cost\": {\"c\": n, ...}");
      LibContract lc;
      lc.c = static_cast<std::uint64_t>(*k);
      lc.text = std::to_string(lc.c);
      if (const llvm::json::Object* per = cost->getObject("per_arg"))
        for (const auto& [key, val] : *per) {
          unsigned i = 0;
          std::optional<std::int64_t> a = val.getAsInteger();
          if (llvm::StringRef(key).getAsInteger(10, i) || !a || *a < 0)
            return fail("\"per_arg\" maps argument positions (from 0) to non-negative integers");
          lc.perArg[i] = static_cast<std::uint64_t>(*a);
          lc.text += " + " + std::to_string(*a) + "*max(0, argument " + std::to_string(i + 1) + ")";
        }
      libContracts_[name->str()] = std::move(lc);
    }
  }
  const LibContract* libContract(const FunctionDecl* fd) const {
    if (libContracts_.empty()) return nullptr;
    auto it = libContracts_.find(fd->getQualifiedNameAsString());
    return it == libContracts_.end() ? nullptr : &it->second;
  }

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
    c.summary.report.errorSites.push_back(siteOf("rejected", loc, msg));
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

  Site siteOf(const std::string& rule, SourceLocation loc, const std::string& msg) {
    Site s;
    s.rule = rule;
    s.message = msg;
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    if (p.isValid()) {
      s.file = p.getFilename();
      s.line = p.getLine();
      s.column = p.getColumn();
    }
    return s;
  }

  void locate(LoopReport& lr, SourceLocation loc) {
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    if (p.isInvalid()) return;
    lr.file = p.getFilename();
    lr.line = p.getLine();
    lr.column = p.getColumn();
  }

  unsigned lineOf(SourceLocation loc) {
    const SourceManager& sm = ctx_.getSourceManager();
    PresumedLoc p = sm.getPresumedLoc(sm.getExpansionLoc(loc));
    return p.isInvalid() ? 0 : p.getLine();
  }

  // -- global variables ------------------------------------------------------
  /// Globals and static locals whose address is taken somewhere in the translation unit
  /// (never tracked).
  std::set<const VarDecl*> globalEscaped_;
  bool globalsScanned_ = false;
  void scanGlobals() {
    if (globalsScanned_) return;
    globalsScanned_ = true;
    struct G : RecursiveASTVisitor<G> {
      std::set<const VarDecl*>* out;
      bool shouldVisitTemplateInstantiations() const { return true; }
      static const VarDecl* global(const Expr* e) {
        const auto* d = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts());
        const auto* v = d ? dyn_cast<VarDecl>(d->getDecl()) : nullptr;
        return v && v->hasGlobalStorage() ? v->getCanonicalDecl() : nullptr;
      }
      bool VisitUnaryOperator(UnaryOperator* u) {
        if (u->getOpcode() == UO_AddrOf)
          if (const VarDecl* v = global(u->getSubExpr())) out->insert(v);
        return true;
      }
      bool VisitVarDecl(VarDecl* v) {  // a reference bound to a global
        if (v->getType()->isReferenceType() && v->getInit())
          if (const VarDecl* g = global(v->getInit())) out->insert(g);
        return true;
      }
      bool VisitCallExpr(CallExpr* c) {  // a global passed to a reference parameter
        if (const FunctionDecl* fd = c->getDirectCallee())
          for (unsigned i = 0; i < c->getNumArgs() && i < fd->getNumParams(); ++i)
            if (fd->getParamDecl(i)->getType()->isReferenceType())
              if (const VarDecl* g = global(c->getArg(i))) out->insert(g);
        return true;
      }
    } g;
    g.out = &globalEscaped_;
    g.TraverseDecl(ctx_.getTranslationUnitDecl());
  }
  bool trackableGlobal(const VarDecl* v) {
    if (!v || !v->hasGlobalStorage() || v->hasLocalStorage()) return false;
    QualType t = v->getType();
    if (!isIntType(t) || t.isVolatileQualified() || v->getTLSKind() != VarDecl::TLS_None) return false;
    // A const object cannot be modified (and its initializer is evaluated as a constant).
    if (t.isConstQualified()) return false;
    scanGlobals();
    return !globalEscaped_.count(v->getCanonicalDecl());
  }
  /// The globals that a call of `fd` may modify: written in the bodies it may run
  /// (transitively). Functions without an analysed body are assumed to modify none.
  std::map<const FunctionDecl*, std::set<const VarDecl*>> globalWrites_;
  const std::set<const VarDecl*>& globalWrites(const FunctionDecl* fd) {
    const FunctionDecl* key = fd->getCanonicalDecl();
    if (auto it = globalWrites_.find(key); it != globalWrites_.end()) return it->second;
    std::set<const VarDecl*> out;
    std::set<const FunctionDecl*> seen;
    std::vector<const FunctionDecl*> work{key};
    while (!work.empty()) {
      const FunctionDecl* f = work.back();
      work.pop_back();
      if (!seen.insert(f).second) continue;
      const FunctionDecl* def = nullptr;
      if (!f->hasBody(def) || !def->getBody()) continue;
      struct W : RecursiveASTVisitor<W> {
        std::set<const VarDecl*>* out;
        std::vector<const FunctionDecl*>* work;
        void lhs(const Expr* e) {
          const auto* d = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts());
          if (const auto* v = d ? dyn_cast<VarDecl>(d->getDecl()) : nullptr)
            if (v->hasGlobalStorage()) out->insert(v->getCanonicalDecl());
        }
        bool VisitBinaryOperator(BinaryOperator* b) {
          if (b->isAssignmentOp()) lhs(b->getLHS());
          return true;
        }
        bool VisitUnaryOperator(UnaryOperator* u) {
          if (u->isIncrementDecrementOp()) lhs(u->getSubExpr());
          return true;
        }
        bool VisitCallExpr(CallExpr* c) {
          if (const FunctionDecl* g = c->getDirectCallee()) work->push_back(g->getCanonicalDecl());
          return true;
        }
        bool VisitCXXConstructExpr(CXXConstructExpr* c) {
          work->push_back(c->getConstructor()->getCanonicalDecl());
          return true;
        }
      } w;
      w.out = &out;
      w.work = &work;
      w.TraverseStmt(def->getBody());
    }
    return globalWrites_.emplace(key, std::move(out)).first->second;
  }
  /// The tracked variables (globals) that a call may modify.
  std::set<const VarDecl*> trackedWrittenBy(const CallExpr* c) {
    std::set<const VarDecl*> out;
    const FunctionDecl* fd = c->getDirectCallee();
    if (!fd || stack_.empty()) return out;
    const std::set<const VarDecl*>& w = globalWrites(fd);
    for (const VarDecl* v : cur().tracked)
      if (!v->hasLocalStorage() && w.count(v->getCanonicalDecl())) out.insert(v);
    return out;
  }
  /// `tab[i]` for a const integer array with a constant initializer: the least and
  /// greatest entry (missing trailing entries are 0). Whatever the index: reading out
  /// of bounds is undefined behaviour, assumed absent like signed overflow.
  std::map<const VarDecl*, std::optional<std::pair<std::int64_t, std::int64_t>>> tableRange_;
  std::optional<std::pair<std::int64_t, std::int64_t>> tableRange(const Expr* e) {
    const auto* as = dyn_cast<ArraySubscriptExpr>(e->IgnoreParenImpCasts());
    if (!as || !isIntType(as->getType())) return std::nullopt;
    const auto* d = dyn_cast<DeclRefExpr>(as->getBase()->IgnoreParenImpCasts());
    const auto* v = d ? dyn_cast<VarDecl>(d->getDecl()) : nullptr;
    if (!v) return std::nullopt;
    if (auto it = tableRange_.find(v); it != tableRange_.end()) return it->second;
    std::optional<std::pair<std::int64_t, std::int64_t>> out;
    const auto* at = ctx_.getAsConstantArrayType(v->getType());
    const VarDecl* def = v->getDefinition() ? v->getDefinition() : v;
    const auto* il = def->getInit() ? dyn_cast<InitListExpr>(def->getInit()->IgnoreImplicit()) : nullptr;
    if (at && at->getElementType().isConstQualified() && !at->getElementType().isVolatileQualified() &&
        il && il->getNumInits() > 0) {
      std::int64_t lo = 0, hi = 0;
      bool ok = true, first = true;
      for (const Expr* x : il->inits()) {
        Expr::EvalResult r;
        if (!x->EvaluateAsInt(r, ctx_) || r.Val.getInt().getSignificantBits() > 63) { ok = false; break; }
        std::int64_t val = r.Val.getInt().getExtValue();
        lo = first ? val : std::min(lo, val);
        hi = first ? val : std::max(hi, val);
        first = false;
      }
      if (ok && il->getNumInits() < at->getSize().getZExtValue()) { lo = std::min<std::int64_t>(lo, 0); hi = std::max<std::int64_t>(hi, 0); }
      if (ok) out = std::make_pair(lo, hi);
    }
    tableRange_[v] = out;
    return out;
  }
  /// After a call: the tracked globals the callee may modify are unknown.
  void callClobbers(const FunctionDecl* fd, State& s) {
    for (const VarDecl* g : globalWrites(fd))
      for (auto it = s.val.begin(); it != s.val.end();)
        if (it->first->getCanonicalDecl() == g) it = s.val.erase(it);
        else ++it;
  }

  // -- GNU extensions used by intrinsic headers (CMSIS Core) -------------------
  /// The statements of `({ ... })` if they are straight-line: declarations,
  /// expressions and inline assembly (no control flow).
  static std::optional<std::vector<const Stmt*>> straightLine(const StmtExpr* se) {
    std::vector<const Stmt*> out;
    for (const Stmt* st : se->getSubStmt()->body()) {
      if (isa<NullStmt>(st)) continue;
      if (!isa<DeclStmt>(st) && !isa<Expr>(st) && !isa<GCCAsmStmt>(st)) return std::nullopt;
      if (const auto* a = dyn_cast<GCCAsmStmt>(st); a && a->isAsmGoto()) return std::nullopt;
      out.push_back(st);
    }
    return out;
  }
  /// Inline assembly: one arithmetic unit per instruction of its template (trusted).
  Cost asmCost(const GCCAsmStmt* a) {
    if (a->isAsmGoto()) {
      error(a->getBeginLoc(), "'asm goto' is not supported in a real-time function");
      return Cost{};
    }
    std::string t = a->getAsmString()->getString().str();
    std::uint64_t n = 0;
    bool any = false;
    for (char c : t + "\n") {
      if (c == '\n' || c == ';') { n += any; any = false; }
      else if (!std::isspace(static_cast<unsigned char>(c))) any = true;
    }
    std::string first = t.substr(0, t.find_first_of("\n;"));
    assume("inline assembly ('" + first + "') costs one arithmetic unit per instruction");
    Cost c{};
    for (const Expr* in : a->inputs()) c = seq(c, exprCost(in));
    return seq(c, unit(w_.arith * std::max<std::uint64_t>(1, n)));
  }

  // -- symbols and values ---------------------------------------------------
  bool tracked(const VarDecl* v) { return v && cur().tracked.count(v); }

  void addInputRange(FnCtx& fc, SymId id, QualType t) {
    bool u = t->isUnsignedIntegerOrEnumerationType();
    std::int64_t lo = u ? opts_.inputLo : -opts_.inputHi;
    fc.summary.assumedInputs.push_back(ge(LinExpr::symbol(id), LinExpr::constant(lo)));
    fc.summary.assumedInputs.push_back(le(LinExpr::symbol(id), LinExpr::constant(opts_.inputHi)));
  }

  /// `p->f` (or `(*p).f`) for a pointer parameter `p` and an integer field `f`.
  static std::optional<std::pair<const ParmVarDecl*, const FieldDecl*>> fieldOf(const Expr* e) {
    const auto* me = dyn_cast<MemberExpr>(e->IgnoreParenImpCasts());
    if (!me) return std::nullopt;
    const auto* fd = dyn_cast<FieldDecl>(me->getMemberDecl());
    if (!fd || fd->isBitField() || !isIntType(fd->getType()) || fd->getType().isVolatileQualified())
      return std::nullopt;
    const Expr* base = me->getBase()->IgnoreParenImpCasts();
    if (!me->isArrow()) {
      const auto* uo = dyn_cast<UnaryOperator>(base);
      if (!uo || uo->getOpcode() != UO_Deref) return std::nullopt;
      base = uo->getSubExpr()->IgnoreParenImpCasts();
    }
    const auto* dr = dyn_cast<DeclRefExpr>(base);
    const auto* p = dr ? dyn_cast<ParmVarDecl>(dr->getDecl()) : nullptr;
    if (!p || !p->getType()->isPointerType()) return std::nullopt;
    if (p->getType()->getPointeeType().isVolatileQualified()) return std::nullopt;
    return std::make_pair(p, fd);
  }

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

  // -- certificates (docs/certificate-format.md) ------------------------------
 public:
  struct CertCtx;
  struct CertPiece;

 private:
  /// A function of the program certificate: its index and the variables (and logical
  /// variables, in order) of its parameters.
  struct CertFunInfo {
    std::size_t index = 0;
    std::vector<std::size_t> ghostVars;
    std::vector<const ParmVarDecl*> ghostParams;
  };
  std::optional<CertPiece> certCallNode(CertCtx& cc, const CertFunInfo& ci,
                                        const std::vector<const Expr*>& args, const cert::Assn& pre);
  std::optional<CertFunInfo> contractFun(CertCtx& cc, const FunctionDecl* fd);
  bool certificate(const FunctionDecl* def, std::string& reason, cert::SB& bound,
                   std::optional<std::uint64_t>& numeric, std::string& summary);
  std::optional<CertPiece> certStmt(CertCtx& cc, const Stmt* s, const cert::Assn& pre);
  std::optional<CertPiece> certList(CertCtx& cc, const std::vector<const Stmt*>& list,
                                    std::size_t from, const cert::Assn& pre);
  std::optional<CertPiece> certExpr(CertCtx& cc, const Expr* e, const cert::Assn& pre);
  std::optional<CertPiece> certExprAfterCalls(CertCtx& cc, const Expr* e, const cert::Assn& pre);
  std::optional<CertPiece> certIf(CertCtx& cc, const IfStmt* is, const std::vector<const Stmt*>& thenList,
                                  const std::vector<const Stmt*>& elseList, const cert::Assn& pre);
  std::optional<CertPiece> certCall(CertCtx& cc, const CallExpr* call, const cert::Assn& pre);
  std::optional<CertPiece> certSwitch(CertCtx& cc, const SwitchStmt* ss, const cert::Assn& pre);
  std::optional<CertPiece> certIfThen(CertCtx& cc, const cert::PExp& g, std::uint64_t w,
                                      const std::function<std::optional<CertPiece>(const cert::Assn&)>& thenF,
                                      const std::function<std::optional<CertPiece>(const cert::Assn&)>& elseF,
                                      const cert::Assn& pre);
  bool certTestList(CertCtx& cc, const Expr* e, std::vector<cert::PExp>& out, bool& nondet);
  std::optional<CertPiece> certCallsIn(CertCtx& cc, const Expr* e, const cert::Assn& pre);
  std::optional<CertPiece> certLoop(CertCtx& cc, const Stmt* loop, const Expr* cond,
                                    const Stmt* body, const Expr* inc, const cert::Assn& pre);
  std::optional<CertPiece> certAssign(CertCtx& cc, std::uint64_t w, std::size_t x,
                                      const std::optional<cert::PExp>& a, const cert::Assn& pre);
  std::optional<cert::PExp> certAffine(CertCtx& cc, const Expr* e);
  std::optional<cert::PExp> certModular(CertCtx& cc, const Expr* e, unsigned width);
  std::optional<cert::PExp> certValueFor(CertCtx& cc, std::size_t x, const Expr* e);
  std::optional<CertPiece> certStore(CertCtx& cc, std::uint64_t w, std::size_t x,
                                     const std::optional<cert::PExp>& a, const cert::Assn& pre);
  /// `x = y OP c` for OP in >>, /, %, & and a constant c: an unknown value with the facts
  /// that hold of it (`havocC`), guarded by `y >= 0` where they need it. No value: the
  /// expression is not of that form.
  /// `x = tab[i]` for a constant table: an unknown value in [min, max] of its entries.
  std::optional<CertPiece> certStoreTable(CertCtx& cc, std::uint64_t w, std::size_t x, QualType xt,
                                          const Expr* rhs, const cert::Assn& pre);
  std::optional<CertPiece> certStoreDivision(CertCtx& cc, std::uint64_t w, std::size_t x,
                                             QualType xt, const Expr* lhs, BinaryOperatorKind op,
                                             const Expr* rhs, QualType rt, const cert::Assn& pre);
  std::optional<cert::PExp> certTest(CertCtx& cc, const Expr* e);
  std::uint64_t costOf(const Expr* e);
  std::vector<std::string> certificates_;
  // The program certificate of the translation unit: variables, functions, and the
  // functions (checked or contracts) that calls can refer to.
  std::vector<std::string> certNames_{"?choice", "?cost"};
  std::map<std::size_t, unsigned> certUWidth_;
  std::map<const VarDecl*, std::size_t> certGlobalVar_;
  std::vector<cert::FunJson> certFuns_;
  std::map<const FunctionDecl*, CertFunInfo> certFunOf_;
  std::map<const FunctionDecl*, CertFunInfo> certContractOf_;
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
    callClobbers(fd, s);
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
        if (auto key = fieldOf(sub))
          if (auto it = cur().summary.fieldSyms.find(*key); it != cur().summary.fieldSyms.end())
            return LinExpr::symbol(it->second);
        // C++: `++x` / `--x` and `x = e` are lvalues; their value is the variable's new value.
        if (const auto* uo = dyn_cast<UnaryOperator>(sub->IgnoreParens());
            uo && (uo->getOpcode() == UO_PreInc || uo->getOpcode() == UO_PreDec))
          if (const VarDecl* x = TrackScan::varOf(uo->getSubExpr()); tracked(x)) {
            eval(uo, s);
            return lookup(x, s);
          }
        if (auto tr = tableRange(sub)) {
          eval(sub, s);  // the index (its side effects and costs)
          LinExpr v = unknown(t, "entry");
          s.facts.push_back(ge(v, LinExpr::constant(tr->first)));
          s.facts.push_back(le(v, LinExpr::constant(tr->second)));
          return v;
        }
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
  if (const auto* se = dyn_cast<StmtExpr>(e)) {
    LinExpr last = unknown(t);
    if (auto list = straightLine(se))
      for (const Stmt* st : *list) {
        last = unknown(t);
        if (const auto* a = dyn_cast<GCCAsmStmt>(st)) {
          for (const Expr* in : a->inputs()) eval(in, s);
        } else if (const auto* x = dyn_cast<Expr>(st)) {
          last = eval(x, s);
        } else if (const auto* ds = dyn_cast<DeclStmt>(st)) {
          for (const Decl* d : ds->decls())
            if (const auto* vd = dyn_cast<VarDecl>(d); vd && vd->getInit()) {
              LinExpr v = eval(vd->getInit(), s);
              if (tracked(vd)) assignVar(vd, v, s);
            }
        }
      }
    return isIntType(t) ? last : LinExpr::poison();
  }
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
  // An integer used as a condition without a conversion to bool (C: `while (--j)`,
  // `if (x)`): true iff it is not 0, as in the CK_IntegralToBoolean case above.
  if (isIntType(e->getType()) && !e->getType()->isBooleanType()) {
    LinExpr v = eval(e, s);
    if (!v.poisoned()) {
      LinExpr zero = LinExpr::constant(0);
      r.neqTrue.push_back({v, zero});
      r.ifFalse.push_back(le(v, zero));
      r.ifFalse.push_back(ge(v, zero));
    }
    return r;
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
  if (const auto* se = dyn_cast<StmtExpr>(e)) {
    if (auto list = straightLine(se)) {
      Cost c{};
      for (const Stmt* st : *list) {
        if (const auto* a = dyn_cast<GCCAsmStmt>(st)) c = seq(c, asmCost(a));
        else if (const auto* x = dyn_cast<Expr>(st)) c = seq(c, exprCost(x));
        else if (const auto* ds = dyn_cast<DeclStmt>(st))
          for (const Decl* d : ds->decls())
            if (const auto* vd = dyn_cast<VarDecl>(d); vd && vd->getInit())
              c = seq(c, seq(exprCost(vd->getInit()), unit(w_.assign)));
      }
      return c;
    }
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
  if (const LibContract* lc = libContract(fd)) {
    // Speculative evaluations (invariant search, certificates) charge only the call:
    // a certificate pays the contract's bound in its call node.
    if (cur().speculative) return unit(w_.call);
    std::uint64_t cost = lc->c;
    for (const auto& [i, a] : lc->perArg) {
      std::optional<std::int64_t> hi;
      if (call)
        if (auto it = cur().calls.find(call); it != cur().calls.end() && it->second.any &&
                                               i < it->second.hull.size())
          hi = it->second.hull[i].hi;
      if (!hi) {
        error(loc, "argument " + std::to_string(i + 1) + " of '" + fd->getQualifiedNameAsString() +
                       "' has no upper bound, which its contract needs");
        return unit(w_.call);
      }
      cost += a * static_cast<std::uint64_t>(std::max<std::int64_t>(0, *hi));
    }
    assume("cost of '" + fd->getQualifiedNameAsString() + "' is at most " + lc->text +
           " (contract file" + (libContractsFor_.empty() ? std::string() : ", " + libContractsFor_) + ")");
    return seq(unit(w_.call), unit(cost));
  }
  if (const AnnotateAttr* a = findAnnotation(fd, "crosscheck::cost")) {
    if (auto n = annotationArg(a, 0, ctx_); n && *n >= 0) {
      if (cur().speculative) return unit(w_.call);  // see above
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
    if (call && !stack_.empty()) cur().callKeys[call] = {def->getCanonicalDecl(), context};
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
  // Target-specific builtins (Arm DSP and SIMD instructions behind the CMSIS intrinsics,
  // `__builtin_arm_qadd16`, ...): one instruction, or a short fixed sequence.
  if (unsigned id = fd->getBuiltinID(); id != 0 && ctx_.BuiltinInfo.isTSBuiltin(id)) {
    assume("target intrinsics such as '" + name + "' cost one arithmetic unit");
    return unit(w_.arith);
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
  scan.callWrites = [this](const CallExpr* c) { return trackedWrittenBy(c); };
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
  scan.callWrites = [this](const CallExpr* c) { return trackedWrittenBy(c); };
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
    locate(lr, fs->getForLoc());
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
  scan.callWrites = [this](const CallExpr* c) { return trackedWrittenBy(c); };
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
  std::set<const VarDecl*> inCond;
  if (cond) {
    ModScan cs(ctx_);
    cs.TraverseStmt(const_cast<Expr*>(cond));
    for (const auto& [v, m] : cs.mods) inCond.insert(v);
  }
  for (const auto& [var, id] : headSym) {
    const ModInfo& info = scan.mods.at(var);
    auto it = entry.val.find(var);
    if (it == entry.val.end()) continue;
    if (info.nonNegative) candidates.push_back({ge(LinExpr::symbol(id), it->second), std::nullopt});
    if (info.nonPositive) candidates.push_back({le(LinExpr::symbol(id), it->second), std::nullopt});
    // The bounds of the entry value, as absolute bounds (`j >= 1` for `do ... while (--j)`),
    // for the variables that the loop test itself modifies only: elsewhere the relative
    // candidates suffice, and each of these costs an optimisation query in every round.
    if (!inCond.count(var)) continue;
    if (std::optional<Interval> b = boundsOf(syms_, entry.facts, it->second)) {
      if (b->lo) candidates.push_back({ge(LinExpr::symbol(id), LinExpr::constant(*b->lo)), std::nullopt});
      if (b->hi) candidates.push_back({le(LinExpr::symbol(id), LinExpr::constant(*b->hi)), std::nullopt});
    }
  }
  if (cond) {
    // `a != b` in the guard: try the invariants a <= b and a >= b, which turn the
    // disequality into a strict inequality. The guard is evaluated with the candidates
    // as facts, so that a side effect in it (`--j`) has an affine value; every candidate
    // is proved on entry and inductive below, so this only shapes the candidates.
    ++fc.speculative;
    State probe = head;
    for (const Candidate& c : candidates) probe.facts.push_back(c.inv);
    CondResult r = evalCond(cond, probe);
    --fc.speculative;
    for (const auto& [a, b] : r.neqTrue) {
      Constraint up{le(a, b).e.substitute(toEntry)}, down{ge(a, b).e.substitute(toEntry)};
      if (entails(syms_, entry.facts, up))
        candidates.push_back({le(a, b), lt(a, b)});
      else if (entails(syms_, entry.facts, down))
        candidates.push_back({ge(a, b), gt(a, b)});
    }
  }

  struct Iteration {
    std::vector<State> complete, returned, broken;
    std::vector<Constraint> startFacts;  ///< at the start of the body: head, invariants, guard
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
    it.startFacts = s.facts;
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
  locate(lr, loc);
  std::uint64_t k = 0;
  if (rank && (!user || rank->bound <= *user)) {
    k = rank->bound;
    lr.verified = true;
    if (!fc.speculative) fc.potentials[loop] = LoopPotential{slots, *rank};
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
  // The report counts executions of the body (the convention of flow facts and of the
  // observed counts): for a do-while, the first body plus the k iterations bounded
  // by the potential. The cost below uses k for the iterations after the first.
  // The potential is required to be >= 1 only on the paths that return to the head.
  // An iteration left by `break` or `return` may start where it is not (e.g.
  // `while (1) { ... if (i++ >= 1000) break; }`, 1001 executions with K = 1000): then
  // the body runs up to K + 1 times. The cost already counts that body (`early`);
  // the reported loop bound counts it too unless V >= 1 is proved at the start of
  // every iteration.
  bool leavingExtra = false;
  if (lr.verified && rank && it.early) {
    std::int64_t den = std::max<std::int64_t>(1, rank->offset.den);
    for (const Rational& q : rank->weights) den = std::lcm(den, std::max<std::int64_t>(1, q.den));
    LinExpr v = LinExpr::constant(rank->offset.num * (den / std::max<std::int64_t>(1, rank->offset.den)));
    for (std::size_t i = 0; i < slots.size() && i < rank->weights.size(); ++i) {
      const Rational& q = rank->weights[i];
      if (q.num == 0) continue;
      v = v + head.val.at(slots[i]).scaled(q.num * (den / std::max<std::int64_t>(1, q.den)));
    }
    leavingExtra = v.poisoned() ||
                   !entails(syms_, it.startFacts, Constraint{LinExpr::constant(den) - v});
  }
  lr.bound = (isDo && lr.verified ? k + 1 : k) + (leavingExtra ? 1 : 0);
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
  if (const auto* a = dyn_cast<GCCAsmStmt>(st)) {
    for (State& s : states)
      if (s.flow == Flow::Normal)
        for (const Expr* in : a->inputs()) eval(in, s);
    return asmCost(a);
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
    return isIntType(t) && !t.isVolatileQualified() &&
           (v->hasLocalStorage() || trackableGlobal(v)) &&
           !ts.escaped.count(v) && ts.total[v] == ts.benign[v];
  };
  // A global referred to through two declarations would be two variables: not tracked.
  std::map<const VarDecl*, int> decls;
  for (const auto& [v, n] : ts.total)
    if (!v->hasLocalStorage()) ++decls[v->getCanonicalDecl()];
  std::string globals;
  for (const auto& [v, n] : ts.total)
    if (trackable(v) && (v->hasLocalStorage() || decls[v->getCanonicalDecl()] == 1)) {
      fc.tracked.insert(v);
      if (!v->hasLocalStorage()) globals += (globals.empty() ? "" : ", ") + v->getNameAsString();
    }
  if (!globals.empty())
    assume("the global or static variables " + globals + " are not modified by interrupts or other "
           "threads while '" + def->getQualifiedNameAsString() + "' runs, nor by functions without an "
           "analysed body or by inline assembly");

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
  // Integer fields read through pointer parameters: one symbol each (their value at entry),
  // if the function neither writes them nor changes the pointer. That nothing else writes
  // them (aliasing pointers, callees, interrupts) is an assumption.
  {
    struct FieldScan : RecursiveASTVisitor<FieldScan> {
      std::set<std::pair<const ParmVarDecl*, const FieldDecl*>> read, written;
      std::set<const ParmVarDecl*> moved;
      void lhs(const Expr* e) {
        if (auto k = Analyzer::fieldOf(e)) written.insert(*k);
        if (const auto* d = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts()))
          if (const auto* p = dyn_cast<ParmVarDecl>(d->getDecl())) moved.insert(p);
      }
      bool VisitBinaryOperator(BinaryOperator* b) {
        if (b->isAssignmentOp()) lhs(b->getLHS());
        return true;
      }
      bool VisitUnaryOperator(UnaryOperator* u) {
        if (u->isIncrementDecrementOp() || u->getOpcode() == UO_AddrOf) lhs(u->getSubExpr());
        return true;
      }
      bool VisitMemberExpr(MemberExpr* m) {
        if (auto k = Analyzer::fieldOf(m)) read.insert(*k);
        return true;
      }
    } fs;
    fs.TraverseStmt(def->getBody());
    std::string names;
    for (const auto& k : fs.read) {
      if (fs.written.count(k) || fs.moved.count(k.first)) continue;
      auto [lo, hi] = symbolRange(k.second->getType(), ctx_);
      std::string name = k.first->getNameAsString() + "->" + k.second->getNameAsString();
      SymId id = syms_.fresh(name, lo, hi);
      fc.summary.fieldSyms[k] = id;
      names += (names.empty() ? "" : ", ") + name;
      if (opts_.inputRange) addInputRange(fc, id, k.second->getType());
    }
    if (!names.empty())
      assume("the fields " + names + " are not modified while '" + def->getQualifiedNameAsString() +
             "' runs (no write through an aliasing pointer, a callee, inline assembly or an interrupt)");
  }
  if (opts_.inputRange) {
    std::string names;
    for (unsigned i = 0; i < def->getNumParams(); ++i) {
      if (!fc.summary.paramSyms[i]) continue;
      bool declared = false;
      for (const FunctionDecl* r : def->redecls())
        if (i < r->getNumParams() && findAnnotation(r->getParamDecl(i), "crosscheck::range")) declared = true;
      if (declared) continue;
      addInputRange(fc, *fc.summary.paramSyms[i], def->getParamDecl(i)->getType());
      names += (names.empty() ? "" : ", ") + def->getParamDecl(i)->getNameAsString();
    }
    for (const auto& [k, id] : fc.summary.fieldSyms)
      names += (names.empty() ? "" : ", ") + k.first->getNameAsString() + "->" + k.second->getNameAsString();
    if (!names.empty())
      assume("inputs without a declared range are in [" + std::to_string(opts_.inputLo) + ", " +
             std::to_string(opts_.inputHi) + "] (signed: [-" + std::to_string(opts_.inputHi) + ", " +
             std::to_string(opts_.inputHi) + "]; option input-range): " + names);
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
  init.facts.insert(init.facts.end(), fc.summary.assumedInputs.begin(), fc.summary.assumedInputs.end());
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
  bool contract = libContract(fd) != nullptr;
  if (contract) {
    def = fd;  // a library function: its contract needs the arguments' bounds
  } else {
    if (!fd->hasBody(def) || !def->getBody() || def->isDependentContext()) return;
    if (def->getCanonicalDecl() == fc.fn->getCanonicalDecl() || callsItself(def)) return;
  }

  Context here(def->getNumParams());
  for (unsigned i = 0; i < def->getNumParams() && i < args.size(); ++i) {
    QualType pt = def->getParamDecl(i)->getType();
    if (!isIntType(pt) || pt.isVolatileQualified() || args[i].poisoned()) continue;
    // The argument must already have the parameter's type, so that its value
    // is the parameter's value (no conversion in between). For a contract, a
    // conversion is allowed when the interval fits the parameter's type.
    bool same = ctx_.hasSameUnqualifiedType(argExprs[i]->getType(), pt);
    if (!same && !contract) continue;
    std::optional<Interval> b = boundsOf(syms_, s.facts, args[i]);
    if (!b) return;  // contradictory facts: this state stands for no execution
    if (!same) {
      auto [plo, phi] = typeRange(pt, ctx_);
      bool fits = b->lo && b->hi && (!plo || *b->lo >= *plo) && (!phi || *b->hi <= *phi) &&
                  isIntType(argExprs[i]->getType());
      if (!fits) continue;
    }
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
    // Linker name, by which binary-level tools (aiT) designate the routine.
    std::unique_ptr<MangleContext> mc(ctx_.createMangleContext());
    GlobalDecl gd = isa<CXXConstructorDecl>(def)  ? GlobalDecl(cast<CXXConstructorDecl>(def), Ctor_Complete)
                    : isa<CXXDestructorDecl>(def) ? GlobalDecl(cast<CXXDestructorDecl>(def), Dtor_Complete)
                                                  : GlobalDecl(def);
    if (mc->shouldMangleDeclName(def)) {
      llvm::raw_string_ostream os(rep.symbol);
      mc->mangleName(gd, os);
    } else {
      rep.symbol = def->getName().str();
    }
  }
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
  if (opts_.certificates && context.empty()) {
    if (!rep.ok || !rep.bounded) {
      rep.certificate = "no certificate: the function is not bounded";
    } else {
      std::string reason, summary;
      cert::SB cb;
      std::optional<std::uint64_t> numeric;
      if (certificate(def, reason, cb, numeric, summary)) {
        rep.certificate = "emitted";
        rep.certificateBound = numeric;
        rep.certificateSummary = summary;
      } else {
        rep.certificate = "no certificate: " + reason;
      }
    }
  }

  fc.summary.potentials =
      std::make_shared<const std::map<const Stmt*, LoopPotential>>(fc.potentials);
  fc.summary.tracked = fc.tracked;
  fc.summary.callKeys = fc.callKeys;
  Summary done = std::move(fc.summary);
  stack_.pop_back();
  return cache_.emplace(std::move(key), std::move(done)).first->second;
}

// ===========================================================================
// Certificates (docs/certificate-format.md).
//
// A function is lowered to the program of a certificate (the Lean type
// `Checker.ACmd`): tracked signed integer variables become the variables
// x_0, x_1, ...; assignments with an affine right-hand side are assignments,
// other assignments are unknown values; statements that do not write a
// tracked variable cost their weight and nothing else (an unknown value given
// to a variable that no assertion mentions). Assertions are computed forwards
// (strongest postconditions, Fourier-Motzkin elimination); every step is
// justified by Farkas multipliers. Loops use the potential the analysis found.
// Nothing here is trusted: the Lean checker validates the result.
// ===========================================================================

struct Analyzer::CertCtx {
  std::map<const VarDecl*, std::size_t> var;
  std::vector<std::string> names;
  std::size_t choice = 0;  ///< the variable of nondeterministic tests
  std::size_t dummy = 1;   ///< a variable that no assertion mentions (costs only)
  std::size_t depth = 0;   ///< loop nesting: index of the logical variable
  std::size_t gammas = 0;  ///< logical variables 0..gammas-1 are the parameters' values
  /// Fields read through pointer parameters of the function being certified (variables
  /// that the program never assigns: their value at entry).
  std::map<std::pair<const ParmVarDecl*, const FieldDecl*>, std::size_t> fieldVar;
  /// The largest value of each of them that the precondition allows (if any): a symbolic
  /// bound is used only if it is no looser than a constant one there.
  std::vector<std::optional<std::uint64_t>> gammaHi;
  /// The value of `k + kl.gamma` at gammaHi, if every gamma it uses is bounded.
  std::optional<std::int64_t> atHi(std::int64_t k, const std::vector<std::uint64_t>& kl) const {
    std::int64_t v = k;
    for (std::size_t g = 0; g < kl.size(); ++g) {
      if (!kl[g]) continue;
      if (g >= gammaHi.size() || !gammaHi[g]) return std::nullopt;
      v += static_cast<std::int64_t>(kl[g] * *gammaHi[g]);
    }
    return v;
  }
  /// The function whose code is being lowered (the analysed one, or an inlined callee).
  const std::map<const Stmt*, LoopPotential>* potentials = nullptr;
  const std::map<const CallExpr*, SummaryKey>* callKeys = nullptr;
  std::set<const FunctionDecl*> inlining;
  std::string prefix;      ///< for the names of inlined variables
  std::set<const VarDecl*> relevant;  ///< variables that can influence control
  unsigned line = 0;       ///< line of the statement being lowered (for messages)
  /// Enclosing loops and switches of the code being lowered (innermost last). A loop
  /// has flags for `break` and `continue` (index, or npos if it has none).
  struct Exit {
    bool loop = false;
    std::size_t brk = static_cast<std::size_t>(-1), cnt = static_cast<std::size_t>(-1);
  };
  std::vector<Exit> exits;
  /// Constraints the enclosing loops need at the end of their bodies: tried as extra
  /// candidates when two branches are joined.
  std::vector<cert::Assn> hints;
  std::size_t ret = static_cast<std::size_t>(-1);  ///< flag of `return` inside loops/switches
  static constexpr std::size_t none = static_cast<std::size_t>(-1);
  std::size_t freshVar(const std::string& name) {
    names.push_back(name);
    return names.size() - 1;
  }
  std::string fail;
  std::size_t temp() const { return names.size(); }  ///< scratch variable for eliminations
  /// Variables of unsigned type, with their width in bits.
  std::map<std::size_t, unsigned> uwidth;
  /// Globals and static locals: one variable of the program certificate each, shared
  /// by every function (so that a callee's writes are in its `mods`, and the frame rule
  /// drops the caller's facts about them).
  std::map<const VarDecl*, std::size_t> globalVar;
  void addVar(const VarDecl* v) {
    if (var.count(v) || !relevant.count(v)) return;
    if (!v->hasLocalStorage()) {
      const VarDecl* key = v->getCanonicalDecl();
      if (auto it = globalVar.find(key); it != globalVar.end()) {
        var[v] = it->second;
        return;
      }
      globalVar[key] = names.size();
      var[v] = names.size();
      QualType t = v->getType();
      if (t->isUnsignedIntegerType()) uwidth[names.size()] = v->getASTContext().getIntWidth(t);
      names.push_back(v->getQualifiedNameAsString());
      return;
    }
    var[v] = names.size();
    QualType t = v->getType();
    if (t->isUnsignedIntegerType()) uwidth[names.size()] = v->getASTContext().getIntWidth(t);
    names.push_back(prefix + v->getNameAsString());
  }
  bool failed(const std::string& why) {
    if (fail.empty()) fail = why + (line ? " (line " + std::to_string(line) + ")" : "");
    return false;
  }
};

struct Analyzer::CertPiece {
  cert::NodeP node;
  cert::Assn post;
  cert::SB bound;
};

namespace {
Analyzer::CertPiece seqPiece(const Analyzer::CertPiece& a, const Analyzer::CertPiece& b) {
  cert::Node n;
  n.kind = cert::Node::Seq;
  n.c1 = a.node;
  n.mid = a.post;
  n.b1 = a.bound;
  n.b2 = b.bound;
  n.c2 = b.node;
  return Analyzer::CertPiece{std::make_shared<const cert::Node>(std::move(n)), b.post, a.bound + b.bound};
}
}  // namespace

namespace {

using cert::Assn;
using cert::Farkas;
using cert::Lin;
using cert::Node;
using cert::NodeP;
using cert::PExp;
using cert::Vec;

NodeP mk(Node n) { return std::make_shared<const Node>(std::move(n)); }

std::vector<Farkas> identityCerts(const Assn& a) {
  std::vector<Farkas> out;
  for (std::size_t i = 0; i < a.size(); ++i) {
    Farkas f;
    f.lam.assign(a.size(), 0);
    f.lam[i] = 1;
    out.push_back(f);
  }
  return out;
}

/// `weaken`: c is checked from P' to Q'; the surrounding triple is (outer, B, Q).
NodeP weaken(Assn pPrime, std::vector<Farkas> preCerts, cert::SB bound, Assn qPrime,
             std::vector<Farkas> postCerts, NodeP c) {
  Node n;
  n.kind = Node::Weaken;
  n.pre = std::move(pPrime);
  n.preCerts = std::move(preCerts);
  n.bound = bound;
  n.post = std::move(qPrime);
  n.postCerts = std::move(postCerts);
  n.c1 = std::move(c);
  return mk(std::move(n));
}

/// A node checked from `pre` whose precondition is contradictory.
std::optional<NodeP> deadNode(const Assn& pre) {
  std::optional<Farkas> f = cert::farkas(pre, Lin{{}, {}, 1});
  if (!f) return std::nullopt;
  Node n;
  n.kind = Node::Dead;
  n.deadCert = *f;
  n.c1 = mk(Node{});
  return mk(std::move(n));
}

bool signedInt(QualType t) {
  return !t.isNull() && t->isIntegerType() && t->isSignedIntegerType() && !t->isBooleanType();
}

/// Integer variables of the certificates: signed or unsigned, not bool or enum.
bool certInt(QualType t) {
  return !t.isNull() && t->isIntegerType() && !t->isBooleanType() && !t->isEnumeralType();
}

struct Scan : RecursiveASTVisitor<Scan> {
  const std::map<const VarDecl*, std::size_t>* vars = nullptr;
  bool writes = false, calls = false, jumps = false, markers = false;
  const VarDecl* target(const Expr* e) {
    if (const auto* d = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts()))
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl()))
        if (vars->count(v)) return v;
    return nullptr;
  }
  bool VisitBinaryOperator(BinaryOperator* e) {
    if (e->isAssignmentOp() && target(e->getLHS())) writes = true;
    return true;
  }
  bool VisitUnaryOperator(UnaryOperator* e) {
    if (e->isIncrementDecrementOp() && target(e->getSubExpr())) writes = true;
    return true;
  }
  bool VisitCallExpr(CallExpr*) { calls = true; return true; }
  bool VisitCXXConstructExpr(CXXConstructExpr* e) {
    if (e->getConstructor() && !e->getConstructor()->isTrivial()) calls = true;
    return true;
  }
  bool VisitBreakStmt(BreakStmt*) { jumps = true; return true; }
  bool VisitContinueStmt(ContinueStmt*) { jumps = true; return true; }
  bool VisitReturnStmt(ReturnStmt*) { jumps = true; return true; }
  bool VisitGotoStmt(GotoStmt*) { jumps = true; return true; }
  bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr* e) {
    // Unevaluated: annotation markers live here.
    if (e->getKind() == UETT_SizeOf && e->isArgumentType() == false) markers = true;
    return true;
  }
};

Scan scanOf(const Stmt* s, const std::map<const VarDecl*, std::size_t>& vars) {
  Scan sc;
  sc.vars = &vars;
  if (s) sc.TraverseStmt(const_cast<Stmt*>(s));
  return sc;
}

std::vector<const Stmt*> flatten(const Stmt* s) {
  std::vector<const Stmt*> out;
  if (!s) return out;
  if (const auto* cs = dyn_cast<CompoundStmt>(s)) out.assign(cs->body_begin(), cs->body_end());
  else out.push_back(s);
  return out;
}

struct ReturnScan : RecursiveASTVisitor<ReturnScan> {
  bool found = false;
  bool VisitReturnStmt(ReturnStmt*) { found = true; return false; }
  bool TraverseLambdaExpr(LambdaExpr*) { return true; }
};
bool hasReturn(const Stmt* s) {
  ReturnScan r;
  r.TraverseStmt(const_cast<Stmt*>(s));
  return r.found;
}

/// `break` / `continue` of the construct being lowered: not inside a nested loop (nor,
/// for `break`, inside a nested switch).
struct JumpScan {
  bool brk = false, cnt = false;
  void run(const Stmt* s, bool inLoop, bool inSwitch) {
    if (!s) return;
    if (isa<BreakStmt>(s)) { if (!inLoop && !inSwitch) brk = true; return; }
    if (isa<ContinueStmt>(s)) { if (!inLoop) cnt = true; return; }
    if (isa<LambdaExpr>(s)) return;
    bool loop = isa<ForStmt>(s) || isa<WhileStmt>(s) || isa<DoStmt>(s) || isa<CXXForRangeStmt>(s);
    bool sw = isa<SwitchStmt>(s);
    for (const Stmt* c : s->children()) run(c, inLoop || loop, inSwitch || sw);
  }
};
JumpScan jumpsOf(const Stmt* s) {
  JumpScan j;
  if (s) for (const Stmt* c : s->children()) j.run(c, false, false);
  if (s && (isa<BreakStmt>(s) || isa<ContinueStmt>(s))) j.run(s, false, false);
  return j;
}
/// Does `s` leave the list it is in (return, or break / continue of the current construct)?
bool endsList(const Stmt* s) {
  // Loops and switches handle their own jumps (flags); they never end the list.
  if (isa<ForStmt>(s) || isa<WhileStmt>(s) || isa<DoStmt>(s) || isa<SwitchStmt>(s) ||
      isa<CXXForRangeStmt>(s))
    return false;
  if (hasReturn(s)) return true;
  JumpScan j = jumpsOf(s);
  return j.brk || j.cnt;
}


bool addChecked(std::int64_t a, std::int64_t b, std::int64_t& r) { return !__builtin_add_overflow(a, b, &r); }
bool mulChecked(std::int64_t a, std::int64_t b, std::int64_t& r) { return !__builtin_mul_overflow(a, b, &r); }

std::optional<PExp> addP(const PExp& a, const PExp& b, std::int64_t kb) {
  PExp r;
  r.sv.assign(std::max(a.sv.size(), b.sv.size()), 0);
  for (std::size_t i = 0; i < r.sv.size(); ++i) {
    std::int64_t x = i < a.sv.size() ? a.sv[i] : 0, y = i < b.sv.size() ? b.sv[i] : 0, t;
    if (!mulChecked(kb, y, t) || !addChecked(x, t, r.sv[i])) return std::nullopt;
  }
  std::int64_t t;
  if (!mulChecked(kb, b.c, t) || !addChecked(a.c, t, r.c)) return std::nullopt;
  return r;
}

std::optional<PExp> scaleP(const PExp& a, std::int64_t k) {
  PExp r;
  for (std::int64_t c : a.sv) {
    std::int64_t t;
    if (!mulChecked(k, c, t)) return std::nullopt;
    r.sv.push_back(t);
  }
  if (!mulChecked(k, a.c, r.c)) return std::nullopt;
  return r;
}

void trimP(PExp& p) {
  while (!p.sv.empty() && p.sv.back() == 0) p.sv.pop_back();
}

/// Strongest postcondition of `x := a` (exact over the rationals).
Assn spAssign(const Assn& pre, std::size_t x, const PExp& a, std::size_t temp) {
  std::int64_t s = cert::coeff(a.sv, x);
  Assn out;
  if (s == 1 || s == -1) {
    // x_old = s * (x_new - r), where a = s*x_old + r.
    PExp r = a;
    if (x < r.sv.size()) r.sv[x] = 0;
    PExp old;  // s*x - s*r
    old.sv = cert::vadd(cert::vsmul(s, cert::unitVec(x)), cert::vsmul(-s, r.sv));
    old.c = -s * r.c;
    for (const Lin& e : pre) {
      std::int64_t k = cert::coeff(e.sv, x);
      if (k == 0) { out.push_back(e); continue; }
      Lin f = e;
      if (x < f.sv.size()) f.sv[x] = 0;
      f.sv = cert::vadd(f.sv, cert::vsmul(k, old.sv));
      f.c = e.c + k * old.c;
      out.push_back(f);
    }
    return cert::normalize(out);
  }
  // Rename x to `temp`, add x = a[temp/x], eliminate temp.
  auto rename = [&](Vec v) {
    std::int64_t k = cert::coeff(v, x);
    if (k != 0) {
      v[x] = 0;
      if (v.size() <= temp) v.resize(temp + 1, 0);
      v[temp] = k;
    }
    return v;
  };
  for (const Lin& e : pre) out.push_back(Lin{rename(e.sv), e.lv, e.c});
  Vec av = rename(a.sv);
  Vec xv = cert::unitVec(x);
  out.push_back(Lin{cert::vadd(xv, cert::vsmul(-1, av)), {}, -a.c});
  out.push_back(Lin{cert::vadd(av, cert::vsmul(-1, xv)), {}, a.c});
  return cert::eliminate(cert::normalize(out), temp);
}

}  // namespace

std::uint64_t Analyzer::costOf(const Expr* e) {
  ++cur().speculative;
  Cost c = flat(exprCost(e));
  --cur().speculative;
  return c.units.inf ? 0 : c.units.v;
}

std::optional<cert::PExp> Analyzer::certAffine(CertCtx& cc, const Expr* e) {
  if (!e) return std::nullopt;
  if (std::optional<std::int64_t> v = constantValue(e)) return PExp{{}, *v};
  e = e->IgnoreParens();
  if (const auto* ce = dyn_cast<ImplicitCastExpr>(e)) {
    CastKind k = ce->getCastKind();
    if (k == CK_LValueToRValue || k == CK_NoOp ||
        (k == CK_IntegralCast && certInt(ce->getType()) && certInt(ce->getSubExpr()->getType()) &&
         widens(ce->getSubExpr()->getType(), ce->getType())))
      return certAffine(cc, ce->getSubExpr());
    return std::nullopt;
  }
  if (const auto* dr = dyn_cast<DeclRefExpr>(e)) {
    const auto* v = dyn_cast<VarDecl>(dr->getDecl());
    auto it = v ? cc.var.find(v) : cc.var.end();
    if (it == cc.var.end()) return std::nullopt;
    return PExp{cert::unitVec(it->second), 0};
  }
  if (auto key = fieldOf(e))
    if (auto it = cc.fieldVar.find(*key); it != cc.fieldVar.end())
      return PExp{cert::unitVec(it->second), 0};
  if (!signedInt(e->getType())) return std::nullopt;
  if (const auto* uo = dyn_cast<UnaryOperator>(e)) {
    if (uo->getOpcode() == UO_Minus)
      if (auto a = certAffine(cc, uo->getSubExpr())) return scaleP(*a, -1);
    if (uo->getOpcode() == UO_Plus) return certAffine(cc, uo->getSubExpr());
    return std::nullopt;
  }
  if (const auto* bo = dyn_cast<BinaryOperator>(e)) {
    BinaryOperatorKind op = bo->getOpcode();
    if (op == BO_Add || op == BO_Sub) {
      auto a = certAffine(cc, bo->getLHS()), b = certAffine(cc, bo->getRHS());
      if (a && b) return addP(*a, *b, op == BO_Add ? 1 : -1);
      return std::nullopt;
    }
    if (op == BO_Mul) {
      auto a = certAffine(cc, bo->getLHS()), b = certAffine(cc, bo->getRHS());
      if (!a || !b) return std::nullopt;
      trimP(*a), trimP(*b);
      if (a->sv.empty()) return scaleP(*b, a->c);
      if (b->sv.empty()) return scaleP(*a, b->c);
      return std::nullopt;
    }
  }
  return std::nullopt;
}

/// An affine `m` whose value is congruent modulo 2^width to the C value of `e`
/// (the value `e` gets when it is stored into an unsigned variable of that width).
/// Addition, subtraction and multiplication preserve congruences; a conversion keeps
/// one if it preserves values or reduces modulo 2^W with W >= width (an unsigned
/// type at least that wide). Signed arithmetic is exact (overflow is undefined
/// behaviour, assumed absent); unsigned arithmetic narrower than `width` is refused.
std::optional<cert::PExp> Analyzer::certModular(CertCtx& cc, const Expr* e, unsigned width) {
  if (!e) return std::nullopt;
  if (std::optional<PExp> a = certAffine(cc, e)) return a;
  e = e->IgnoreParens();
  if (const auto* ce = dyn_cast<CastExpr>(e)) {
    CastKind k = ce->getCastKind();
    QualType to = ce->getType(), from = ce->getSubExpr()->getType();
    if (k == CK_LValueToRValue || k == CK_NoOp) return certModular(cc, ce->getSubExpr(), width);
    if (k == CK_IntegralCast && certInt(to) && certInt(from) &&
        (widens(from, to) || (to->isUnsignedIntegerType() && ctx_.getIntWidth(to) >= width)))
      return certModular(cc, ce->getSubExpr(), width);
    return std::nullopt;
  }
  QualType t = e->getType();
  if (!certInt(t)) return std::nullopt;
  if (t->isUnsignedIntegerType() && ctx_.getIntWidth(t) < width) return std::nullopt;
  if (const auto* uo = dyn_cast<UnaryOperator>(e)) {
    if (uo->getOpcode() == UO_Minus)
      if (auto a = certModular(cc, uo->getSubExpr(), width)) return scaleP(*a, -1);
    if (uo->getOpcode() == UO_Plus) return certModular(cc, uo->getSubExpr(), width);
    return std::nullopt;
  }
  if (const auto* bo = dyn_cast<BinaryOperator>(e)) {
    BinaryOperatorKind op = bo->getOpcode();
    if (op == BO_Add || op == BO_Sub) {
      auto a = certModular(cc, bo->getLHS(), width), b = certModular(cc, bo->getRHS(), width);
      if (a && b) return addP(*a, *b, op == BO_Add ? 1 : -1);
      return std::nullopt;
    }
    if (op == BO_Mul) {
      auto a = certModular(cc, bo->getLHS(), width), b = certModular(cc, bo->getRHS(), width);
      if (!a || !b) return std::nullopt;
      trimP(*a), trimP(*b);
      if (a->sv.empty()) return scaleP(*b, a->c);
      if (b->sv.empty()) return scaleP(*a, b->c);
    }
  }
  return std::nullopt;
}

/// The value of `e` stored into the certificate variable `x`: exact for a signed
/// variable, modulo 2^width for an unsigned one (certStore adds the range check).
std::optional<cert::PExp> Analyzer::certValueFor(CertCtx& cc, std::size_t x, const Expr* e) {
  auto uw = cc.uwidth.find(x);
  std::optional<PExp> a = uw == cc.uwidth.end() ? certAffine(cc, e) : certModular(cc, e, uw->second);
  if (a) trimP(*a);
  return a;
}

/// The C store `x = e`, where `a` is the value from certValueFor. For an unsigned
/// `x` the stored value is `a` reduced modulo 2^width, which is `a` itself only when
/// `0 <= a <= 2^width - 1`: the certificate's program tests this and havocs `x`
/// otherwise (tests of weight 0). The checker proves the wrapping branches dead when
/// they are: nothing about the absence of wrap-around is taken on trust. For 64-bit
/// variables the upper test is `a <= 2^62`, which also excludes wrap-around.
std::optional<Analyzer::CertPiece> Analyzer::certStore(CertCtx& cc, std::uint64_t w, std::size_t x,
                                                      const std::optional<cert::PExp>& a,
                                                      const cert::Assn& pre) {
  auto uw = cc.uwidth.find(x);
  if (uw == cc.uwidth.end() || !a) return certAssign(cc, w, x, a, pre);
  std::int64_t hi = uw->second >= 63 ? (std::int64_t(1) << 62) : ((std::int64_t(1) << uw->second) - 1);
  PExp up = *a;
  up.c -= hi;                                // a - hi <= 0
  std::optional<PExp> lo = scaleP(*a, -1);   // -a <= 0
  if (!lo) return certAssign(cc, w, x, std::nullopt, pre);
  trimP(up), trimP(*lo);
  auto havocF = [&](const Assn& p) { return certAssign(cc, w, x, std::nullopt, p); };
  auto storeF = [&](const Assn& p) { return certAssign(cc, w, x, a, p); };
  auto inner = [&](const Assn& p) { return certIfThen(cc, *lo, 0, storeF, havocF, p); };
  return certIfThen(cc, up, 0, inner, havocF, pre);
}

std::optional<Analyzer::CertPiece> Analyzer::certStoreTable(CertCtx& cc, std::uint64_t w,
                                                           std::size_t x, QualType xt,
                                                           const Expr* rhs, const cert::Assn& pre) {
  std::optional<std::pair<std::int64_t, std::int64_t>> tr = tableRange(rhs);
  if (!tr || !certInt(xt)) return std::nullopt;
  auto [tlo, thi] = typeRange(xt, ctx_);  // the entries must fit: no conversion of the value
  if ((tlo && tr->first < *tlo) || (thi && tr->second > *thi)) return std::nullopt;
  std::vector<PExp> cs{PExp{cert::vsmul(-1, cert::unitVec(x)), tr->first},
                       PExp{cert::unitVec(x), -tr->second}};
  Assn frame = cert::eliminate(pre, x);
  std::optional<std::vector<Farkas>> pc = cert::farkasAll(pre, frame);
  if (!pc) return cc.failed("internal: an assignment could not be justified"), std::nullopt;
  Node n;
  n.kind = Node::HavocC;
  n.w = w;
  n.x = x;
  n.gs = cs;
  Assn post = frame;
  for (const PExp& g : cs) post.push_back(cert::toLin(g));
  return CertPiece{weaken(frame, *pc, w, post, identityCerts(post), mk(n)), post, w};
}

std::optional<Analyzer::CertPiece> Analyzer::certStoreDivision(
    CertCtx& cc, std::uint64_t w, std::size_t x, QualType xt, const Expr* lhs, BinaryOperatorKind op,
    const Expr* rhs, QualType rt, const cert::Assn& pre) {
  if (op != BO_Shr && op != BO_Div && op != BO_Rem && op != BO_And) return std::nullopt;
  std::optional<std::int64_t> cv = constantValue(rhs);
  std::optional<PExp> y = lhs ? certAffine(cc, lhs) : std::nullopt;
  if (op == BO_And && !cv) {  // the mask may be on the left
    std::swap(lhs, rhs);
    cv = constantValue(rhs);
    y = certAffine(cc, lhs);
  }
  if (!cv || !y || *cv < 0) return std::nullopt;
  // The stored value is the result itself: the result type must fit the variable.
  if (!certInt(rt) || !certInt(xt) || !(ctx_.hasSameUnqualifiedType(rt, xt) || widens(rt, xt)))
    return std::nullopt;
  std::int64_t c = *cv;
  if (op == BO_Shr) {
    if (c >= 62) return std::nullopt;
    c = std::int64_t{1} << c;
  }
  if ((op == BO_Div || op == BO_Shr || op == BO_Rem) && c <= 0) return std::nullopt;
  trimP(*y);
  PExp xv{cert::unitVec(x), 0};
  auto lin = [](const PExp& a, std::int64_t k, const PExp& b, std::int64_t cst) {  // k*a - b + cst
    PExp r{cert::vadd(cert::vsmul(k, a.sv), cert::vsmul(-1, b.sv)), k * a.c - b.c + cst};
    trimP(r);
    return r;
  };
  std::vector<PExp> csPos, csAny;  // facts for y >= 0, and facts for every y
  if (op == BO_Div || op == BO_Shr) {
    csPos = {lin(xv, c, *y, 0), lin(*y, 1, PExp{cert::vsmul(c, xv.sv), 0}, -(c - 1))};
  } else if (op == BO_Rem) {
    csPos = {PExp{cert::vsmul(-1, xv.sv), 0}, PExp{xv.sv, -(c - 1)}, lin(xv, 1, *y, 0)};
  } else {  // x & c, c >= 0: 0 <= x <= c always, and x <= y for y >= 0
    csAny = {PExp{cert::vsmul(-1, xv.sv), 0}, PExp{xv.sv, -c}};
    csPos = csAny;
    csPos.push_back(lin(xv, 1, *y, 0));
  }
  auto store = [&](const std::vector<PExp>& cs, const Assn& p) -> std::optional<CertPiece> {
    if (cs.empty()) return certAssign(cc, w, x, std::nullopt, p);
    Assn frame = cert::eliminate(p, x);
    std::optional<std::vector<Farkas>> pc = cert::farkasAll(p, frame);
    if (!pc) return cc.failed("internal: an assignment could not be justified"), std::nullopt;
    Node n;
    n.kind = Node::HavocC;
    n.w = w;
    n.x = x;
    n.gs = cs;
    Assn post = frame;
    for (const PExp& g : cs) post.push_back(cert::toLin(g));
    return CertPiece{weaken(frame, *pc, w, post, identityCerts(post), mk(n)), post, w};
  };
  // if (-y <= 0) x := ? with csPos else x := ? with csAny (tests of weight 0)
  PExp guard{cert::vsmul(-1, y->sv), -y->c};
  trimP(guard);
  return certIfThen(cc, guard, 0, [&](const Assn& p) { return store(csPos, p); },
                    [&](const Assn& p) { return store(csAny, p); }, pre);
}

std::optional<cert::PExp> Analyzer::certTest(CertCtx& cc, const Expr* e) {
  e = e->IgnoreParenImpCasts();
  if (const auto* uo = dyn_cast<UnaryOperator>(e); uo && uo->getOpcode() == UO_LNot) {
    if (auto g = certTest(cc, uo->getSubExpr())) {
      // not (g <= 0)  is  1 - g <= 0
      auto n = scaleP(*g, -1);
      if (n) n->c += 1;
      return n;
    }
    return std::nullopt;
  }
  const auto* bo = dyn_cast<BinaryOperator>(e);
  if (!bo || !bo->isRelationalOp()) return std::nullopt;
  auto a = certAffine(cc, bo->getLHS()), b = certAffine(cc, bo->getRHS());
  if (!a || !b) return std::nullopt;
  std::optional<PExp> d;
  switch (bo->getOpcode()) {
    case BO_LT: d = addP(*a, *b, -1); if (d) d->c += 1; break;   // a - b + 1 <= 0
    case BO_LE: d = addP(*a, *b, -1); break;                       // a - b <= 0
    case BO_GT: d = addP(*b, *a, -1); if (d) d->c += 1; break;   // b - a + 1 <= 0
    case BO_GE: d = addP(*b, *a, -1); break;                       // b - a <= 0
    default: break;
  }
  if (d) trimP(*d);
  return d;
}

std::optional<Analyzer::CertPiece> Analyzer::certAssign(CertCtx& cc, std::uint64_t w, std::size_t x,
                                                       const std::optional<cert::PExp>& a,
                                                       const cert::Assn& pre) {
  if (!cert::feasible(pre))
    if (auto d = deadNode(pre)) return CertPiece{*d, pre, 0};
  Node n;
  n.w = w;
  n.x = x;
  Assn q, pPrime;
  if (a) {
    n.kind = Node::Assign;
    n.a = *a;
    q = spAssign(pre, x, *a, cc.temp());
    for (const Lin& e : q) pPrime.push_back(cert::subst(e, x, *a));
  } else {
    n.kind = Node::Havoc;
    q = cert::eliminate(pre, x);
    pPrime = q;
  }
  std::optional<std::vector<Farkas>> pc = cert::farkasAll(pre, pPrime);
  if (!pc) return cc.failed("internal: an assignment could not be justified"), std::nullopt;
  return CertPiece{weaken(pPrime, *pc, w, q, identityCerts(q), mk(n)), q, w};
}

std::optional<Analyzer::CertPiece> Analyzer::certExpr(CertCtx& cc, const Expr* e,
                                                     const cert::Assn& pre) {
  Scan sc = scanOf(e, cc.var);
  if (sc.calls) {
    // Inline the calls, then lower the expression with their results unknown.
    std::optional<CertPiece> c = certCallsIn(cc, e, pre);
    if (!c) return std::nullopt;
    std::optional<CertPiece> rest = certExprAfterCalls(cc, e, c->post);
    if (!rest) return std::nullopt;
    return seqPiece(*c, *rest);
  }
  return certExprAfterCalls(cc, e, pre);
}

std::optional<Analyzer::CertPiece> Analyzer::certExprAfterCalls(CertCtx& cc, const Expr* e,
                                                               const cert::Assn& pre) {
  Scan sc = scanOf(e, cc.var);
  const Expr* x = e->IgnoreParenImpCasts();
  std::uint64_t w = costOf(e);
  if (!sc.writes) {
    // Cost only: an unknown value for a variable that no assertion mentions.
    Node n;
    n.kind = Node::Havoc;
    n.w = w;
    n.x = cc.dummy;
    return CertPiece{mk(n), pre, w};
  }
  auto targetOf = [&](const Expr* t) -> std::optional<std::size_t> {
    if (const auto* d = dyn_cast<DeclRefExpr>(t->IgnoreParenImpCasts()))
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl()))
        if (auto it = cc.var.find(v); it != cc.var.end()) return it->second;
    return std::nullopt;
  };
  if (const auto* bo = dyn_cast<BinaryOperator>(x); bo && bo->isAssignmentOp()) {
    std::optional<std::size_t> t = targetOf(bo->getLHS());
    if (!t || scanOf(bo->getRHS(), cc.var).writes)
      return cc.failed("assignment inside an expression"), std::nullopt;
    bool isUnsigned = cc.uwidth.count(*t) > 0;
    // For a signed target, a compound assignment computed in an unsigned type may wrap.
    bool exact = isUnsigned || !isa<CompoundAssignOperator>(bo) ||
                 signedInt(cast<CompoundAssignOperator>(bo)->getComputationResultType());
    std::optional<PExp> rhs = certValueFor(cc, *t, bo->getRHS());
    if (const VarDecl* tv = TrackScan::varOf(bo->getLHS())) {
      // x = y >> k, y / c, y % c, y & m; x >>= k, x /= c, ...
      if (bo->getOpcode() == BO_Assign && !rhs)
        if (auto p = certStoreTable(cc, w, *t, tv->getType(), bo->getRHS(), pre)) return p;
      if (bo->getOpcode() == BO_Assign && !rhs)
        if (const auto* d = dyn_cast<BinaryOperator>(bo->getRHS()->IgnoreParenImpCasts()))
          if (auto p = certStoreDivision(cc, w, *t, tv->getType(), d->getLHS(), d->getOpcode(),
                                         d->getRHS(), d->getType(), pre))
            return p;
      if (const auto* cao = dyn_cast<CompoundAssignOperator>(bo))
        if (auto p = certStoreDivision(cc, w, *t, tv->getType(), bo->getLHS(),
                                       BinaryOperator::getOpForCompoundAssignment(bo->getOpcode()),
                                       bo->getRHS(), cao->getComputationResultType(), pre))
          return p;
    }
    std::optional<PExp> a;
    PExp self{cert::unitVec(*t), 0};
    switch (bo->getOpcode()) {
      case BO_Assign: a = rhs; break;
      case BO_AddAssign: if (rhs && exact) a = addP(self, *rhs, 1); break;
      case BO_SubAssign: if (rhs && exact) a = addP(self, *rhs, -1); break;
      default: break;  // other compound assignments: unknown value
    }
    if (a) trimP(*a);
    return certStore(cc, w, *t, a, pre);
  }
  if (const auto* uo = dyn_cast<UnaryOperator>(x); uo && uo->isIncrementDecrementOp()) {
    std::optional<std::size_t> t = targetOf(uo->getSubExpr());
    if (!t) return cc.failed("assignment inside an expression"), std::nullopt;
    PExp a{cert::unitVec(*t), uo->isIncrementOp() ? 1 : -1};
    return certStore(cc, w, *t, a, pre);
  }
  if (const auto* co = dyn_cast<BinaryOperator>(x); co && co->getOpcode() == BO_Comma) {
    // `a, b` in a for-increment: a then b. The cost of the comma itself is zero.
    auto p1 = certExpr(cc, co->getLHS(), pre);
    if (!p1) return std::nullopt;
    auto p2 = certExpr(cc, co->getRHS(), p1->post);
    if (!p2) return std::nullopt;
    Node n;
    n.kind = Node::Seq;
    n.c1 = p1->node;
    n.mid = p1->post;
    n.b1 = p1->bound;
    n.b2 = p2->bound;
    n.c2 = p2->node;
    return CertPiece{mk(n), p2->post, p1->bound + p2->bound};
  }
  return cc.failed("assignment inside an expression"), std::nullopt;
}

std::optional<Analyzer::CertPiece> Analyzer::certList(CertCtx& cc, const std::vector<const Stmt*>& list,
                                                     std::size_t from, const cert::Assn& pre) {
  if (from >= list.size()) return CertPiece{mk(Node{}), pre, 0};
  const Stmt* st = list[from];
  if (cc.prefix.empty()) cc.line = lineOf(st->getBeginLoc());
  auto setFlag = [&](std::size_t flag, std::uint64_t w, const Assn& p) -> std::optional<CertPiece> {
    if (flag == CertCtx::none) return cc.failed("internal: jump without a flag"), std::nullopt;
    return certAssign(cc, w, flag, PExp{{}, 1}, p);
  };
  // Jumps end the list: the rest is not reached.
  if (isa<BreakStmt>(st)) {
    if (cc.exits.empty()) return cc.failed("break outside a loop or switch"), std::nullopt;
    const CertCtx::Exit& x = cc.exits.back();
    if (!x.loop) {
      Node n;
      n.kind = Node::Havoc;
      n.w = w_.branch;
      n.x = cc.dummy;
      return CertPiece{mk(n), pre, n.w};
    }
    return setFlag(x.brk, w_.branch, pre);
  }
  if (isa<ContinueStmt>(st)) {
    for (auto it = cc.exits.rbegin(); it != cc.exits.rend(); ++it)
      if (it->loop) return setFlag(it->cnt, w_.branch, pre);
    return cc.failed("continue outside a loop"), std::nullopt;
  }
  if (const auto* rs = dyn_cast<ReturnStmt>(st)) {
    std::optional<CertPiece> c = certStmt(cc, rs, pre);  // its cost
    if (!c || cc.exits.empty()) return c;
    std::optional<CertPiece> f = setFlag(cc.ret, 0, c->post);
    if (!f) return std::nullopt;
    return seqPiece(*c, *f);
  }
  std::vector<const Stmt*> rest(list.begin() + static_cast<std::ptrdiff_t>(from) + 1, list.end());
  // A conditional or block that may leave the list: the rest of the list goes into its
  // branches, so that it follows only the paths that do not leave.
  if (endsList(st)) {
    if (const auto* cs = dyn_cast<CompoundStmt>(st)) {
      std::vector<const Stmt*> l(cs->body_begin(), cs->body_end());
      l.insert(l.end(), rest.begin(), rest.end());
      return certList(cc, l, 0, pre);
    }
    if (const auto* is = dyn_cast<IfStmt>(st)) {
      std::vector<const Stmt*> t = flatten(is->getThen()), e = flatten(is->getElse());
      t.insert(t.end(), rest.begin(), rest.end());
      e.insert(e.end(), rest.begin(), rest.end());
      return certIf(cc, is, t, e, pre);
    }
    if (const auto* as = dyn_cast<AttributedStmt>(st)) {
      std::vector<const Stmt*> l{as->getSubStmt()};
      l.insert(l.end(), rest.begin(), rest.end());
      return certList(cc, l, 0, pre);
    }
    return cc.failed("jump in a statement that is not a conditional or a block"), std::nullopt;
  }
  // Loops and switches that contain a `return` (or a `continue` of an enclosing loop,
  // for a switch) set a flag; the rest of the list runs only if it is not set.
  bool escRet = hasReturn(st);
  if (escRet && cc.ret == CertCtx::none) cc.ret = cc.freshVar(cc.prefix + "?return");
  std::size_t escCnt = CertCtx::none;
  if (isa<SwitchStmt>(st) && jumpsOf(st).cnt)
    for (auto it = cc.exits.rbegin(); it != cc.exits.rend(); ++it)
      if (it->loop) { escCnt = it->cnt; break; }
  CertPiece head{mk(Node{}), pre, 0};
  if (escRet) {
    std::optional<CertPiece> z = certAssign(cc, 0, cc.ret, PExp{{}, 0}, pre);
    if (!z) return std::nullopt;
    head = *z;
  }
  std::optional<CertPiece> first = certStmt(cc, st, head.post);
  if (!first) return std::nullopt;
  if (escRet) first = seqPiece(head, *first);
  if (rest.empty() && !escRet) return first;
  std::function<std::optional<CertPiece>(const Assn&)> restF = [&](const Assn& p) {
    return certList(cc, list, from + 1, p);
  };
  auto skipF = [&](const Assn& p) -> std::optional<CertPiece> { return CertPiece{mk(Node{}), p, 0}; };
  std::function<std::optional<CertPiece>(const Assn&)> guarded = restF;
  for (std::size_t flag : {escCnt, escRet ? cc.ret : CertCtx::none}) {
    if (flag == CertCtx::none) continue;
    auto inner = guarded;
    guarded = [&, flag, inner](const Assn& p) {
      return certIfThen(cc, PExp{cert::unitVec(flag), 0}, 0, inner, skipF, p);
    };
  }
  if (rest.empty() && escRet) return first;
  std::optional<CertPiece> r = guarded(first->post);
  if (!r) return std::nullopt;
  return seqPiece(*first, *r);
}

std::optional<Analyzer::CertPiece> Analyzer::certIfThen(
    CertCtx& cc, const cert::PExp& g, std::uint64_t w,
    const std::function<std::optional<CertPiece>(const cert::Assn&)>& thenF,
    const std::function<std::optional<CertPiece>(const cert::Assn&)>& elseF, const cert::Assn& pre) {
  Assn pre1 = pre, pre2 = pre;
  pre1.insert(pre1.begin(), cert::toLin(g));
  pre2.insert(pre2.begin(), cert::negLin(g));
  auto branch = [&](const std::function<std::optional<CertPiece>(const Assn&)>& f,
                    const Assn& p) -> std::optional<CertPiece> {
    if (!cert::feasible(p))
      if (auto d = deadNode(p)) return CertPiece{*d, {Lin{{}, {}, 1}}, 0};
    return f(p);
  };
  std::optional<CertPiece> b1 = branch(thenF, pre1);
  if (!b1) return std::nullopt;
  std::optional<CertPiece> b2 = branch(elseF, pre2);
  if (!b2) return std::nullopt;
  bool dead1 = b1->node->kind == Node::Dead, dead2 = b2->node->kind == Node::Dead;
  Assn join;
  if (dead1) join = b2->post;
  else if (dead2) join = b1->post;
  else {
    Assn cands = b1->post;
    cands.insert(cands.end(), b2->post.begin(), b2->post.end());
    for (const Assn& h : cc.hints) cands.insert(cands.end(), h.begin(), h.end());
    for (const Lin& e : cert::normalize(cands))
      if (cert::farkas(b1->post, e) && cert::farkas(b2->post, e)) join.push_back(e);
  }
  auto wrap = [&](CertPiece& b, const Assn& p) -> std::optional<NodeP> {
    if (b.node->kind == Node::Dead) return b.node;
    std::optional<std::vector<Farkas>> qc = cert::farkasAll(b.post, join);
    if (!qc) return std::nullopt;
    return weaken(p, identityCerts(p), b.bound, b.post, *qc, b.node);
  };
  std::optional<NodeP> n1 = wrap(*b1, pre1), n2 = wrap(*b2, pre2);
  if (!n1 || !n2) return cc.failed("internal: join"), std::nullopt;
  Node n;
  n.kind = Node::Ite;
  n.w = w;
  n.a = g;
  n.b1 = b1->bound;
  n.b2 = b2->bound;
  n.c1 = *n1;
  n.c2 = *n2;
  return CertPiece{mk(n), join, cert::SB(w) + cert::smax(b1->bound, b2->bound)};
}

std::optional<Analyzer::CertPiece> Analyzer::certSwitch(CertCtx& cc, const SwitchStmt* ss,
                                                       const cert::Assn& pre) {
  if (ss->getInit() || ss->getConditionVariable())
    return cc.failed("switch with an initialiser or a condition variable"), std::nullopt;
  Scan sc = scanOf(ss->getCond(), cc.var);
  if (sc.writes) return cc.failed("switch test with an assignment"), std::nullopt;
  CertPiece acc{mk(Node{}), pre, 0};
  if (sc.calls) {
    std::optional<CertPiece> c = certCallsIn(cc, ss->getCond(), pre);
    if (!c) return std::nullopt;
    acc = *c;
  }
  {
    Node t;
    t.kind = Node::Havoc;
    t.w = costOf(ss->getCond()) + w_.branch;
    t.x = cc.dummy;
    acc = seqPiece(acc, CertPiece{mk(t), acc.post, t.w});
  }
  // Case groups: the statements from one label to the next. Each group runs or not,
  // nondeterministically: this covers every entry label and every fall-through, and
  // costs the sum of the cases, like the analysis.
  const auto* body = dyn_cast<CompoundStmt>(ss->getBody());
  if (!body) return cc.failed("switch without a block"), std::nullopt;
  std::vector<std::vector<const Stmt*>> groups;
  for (const Stmt* st : body->body()) {
    if (const auto* sw = dyn_cast<SwitchCase>(st)) {
      const Stmt* sub = sw->getSubStmt();
      while (const auto* inner = dyn_cast_or_null<SwitchCase>(sub)) sub = inner->getSubStmt();
      groups.push_back({});
      if (sub) groups.back().push_back(sub);
    } else if (!groups.empty()) {
      groups.back().push_back(st);
    }
  }
  struct CaseScan : RecursiveASTVisitor<CaseScan> {
    bool nested = false;
    bool TraverseSwitchStmt(SwitchStmt*) { return true; }
    bool VisitCaseStmt(CaseStmt*) { nested = true; return false; }
    bool VisitDefaultStmt(DefaultStmt*) { nested = true; return false; }
  };
  for (const auto& g : groups)
    for (const Stmt* st : g) {
      CaseScan cs;
      cs.TraverseStmt(const_cast<Stmt*>(st));
      if (cs.nested) return cc.failed("case label inside a nested statement"), std::nullopt;
    }
  cc.exits.push_back(CertCtx::Exit{});
  for (const auto& g : groups) {
    Assn chosen = cert::eliminate(acc.post, cc.choice);
    std::optional<std::vector<Farkas>> pc = cert::farkasAll(acc.post, chosen);
    if (!pc) { cc.exits.pop_back(); return cc.failed("internal: choice"), std::nullopt; }
    Node h;
    h.kind = Node::Havoc;
    h.x = cc.choice;
    acc = seqPiece(acc, CertPiece{weaken(chosen, *pc, 0, chosen, identityCerts(chosen), mk(h)), chosen, 0});
    std::optional<CertPiece> c = certIfThen(
        cc, PExp{cert::unitVec(cc.choice), 0}, 0,
        [&](const Assn& p) { return certList(cc, g, 0, p); },
        [&](const Assn& p) -> std::optional<CertPiece> { return CertPiece{mk(Node{}), p, 0}; }, acc.post);
    if (!c) { cc.exits.pop_back(); return std::nullopt; }
    acc = seqPiece(acc, *c);
  }
  cc.exits.pop_back();
  return acc;
}

bool Analyzer::certTestList(CertCtx& cc, const Expr* e, std::vector<cert::PExp>& out, bool& nondet) {
  if (!e) return true;  // no test: true
  if (std::optional<std::int64_t> v = constantValue(e)) {
    if (*v == 0) out.push_back(PExp{{}, 1});  // false: 1 <= 0
    return true;
  }
  const Expr* x = e->IgnoreParenImpCasts();
  if (const auto* bo = dyn_cast<BinaryOperator>(x); bo && bo->getOpcode() == BO_LAnd)
    return certTestList(cc, bo->getLHS(), out, nondet) && certTestList(cc, bo->getRHS(), out, nondet);
  if (std::optional<PExp> g = certTest(cc, e)) {
    out.push_back(*g);
    return true;
  }
  nondet = true;  // a conjunct the fragment cannot express: an unknown boolean
  return true;
}

std::optional<Analyzer::CertPiece> Analyzer::certIf(CertCtx& cc, const IfStmt* is,
                                                   const std::vector<const Stmt*>& thenList,
                                                   const std::vector<const Stmt*>& elseList,
                                                   const cert::Assn& pre) {
  if (is->getInit() || is->getConditionVariable() || is->isConsteval() || is->isConstexpr())
    return cc.failed("if with an initialiser, a condition variable or constexpr"), std::nullopt;
  Scan sc = scanOf(is->getCond(), cc.var);
  if (sc.writes) return cc.failed("test with an assignment"), std::nullopt;
  std::optional<CertPiece> calls;
  if (sc.calls) {
    calls = certCallsIn(cc, is->getCond(), pre);
    if (!calls) return std::nullopt;
  }
  const Assn& pre0 = calls ? calls->post : pre;
  std::uint64_t w = costOf(is->getCond()) + w_.branch;
  std::optional<PExp> g = certTest(cc, is->getCond());
  Assn start = pre0;
  NodeP choose;
  if (!g) {
    // A test the fragment cannot express: a nondeterministic choice.
    start = cert::eliminate(pre0, cc.choice);
    std::optional<std::vector<Farkas>> pc = cert::farkasAll(pre0, start);
    if (!pc) return cc.failed("internal: choice"), std::nullopt;
    Node h;
    h.kind = Node::Havoc;
    h.x = cc.choice;
    choose = weaken(start, *pc, 0, start, identityCerts(start), mk(h));
    g = PExp{cert::unitVec(cc.choice), 0};
  }
  Assn pre1 = start, pre2 = start;
  pre1.insert(pre1.begin(), cert::toLin(*g));
  pre2.insert(pre2.begin(), cert::negLin(*g));
  auto branch = [&](const std::vector<const Stmt*>& l, const Assn& p) -> std::optional<CertPiece> {
    if (!cert::feasible(p))
      if (auto d = deadNode(p)) return CertPiece{*d, {Lin{{}, {}, 1}}, 0};
    return certList(cc, l, 0, p);
  };
  std::optional<CertPiece> b1 = branch(thenList, pre1);
  if (!b1) return std::nullopt;
  std::optional<CertPiece> b2 = branch(elseList, pre2);
  if (!b2) return std::nullopt;
  bool dead1 = b1->node->kind == Node::Dead, dead2 = b2->node->kind == Node::Dead;
  Assn join;
  if (dead1) join = b2->post;
  else if (dead2) join = b1->post;
  else {
    Assn cands = b1->post;
    cands.insert(cands.end(), b2->post.begin(), b2->post.end());
    for (const Assn& h : cc.hints) cands.insert(cands.end(), h.begin(), h.end());
    for (const Lin& e : cert::normalize(cands))
      if (cert::farkas(b1->post, e) && cert::farkas(b2->post, e)) join.push_back(e);
  }
  auto wrap = [&](CertPiece& b, const Assn& p) -> std::optional<NodeP> {
    if (b.node->kind == Node::Dead) return b.node;
    std::optional<std::vector<Farkas>> qc = cert::farkasAll(b.post, join);
    if (!qc) return std::nullopt;
    return weaken(p, identityCerts(p), b.bound, b.post, *qc, b.node);
  };
  std::optional<NodeP> n1 = wrap(*b1, pre1), n2 = wrap(*b2, pre2);
  if (!n1 || !n2) return cc.failed("internal: join"), std::nullopt;
  Node n;
  n.kind = Node::Ite;
  n.w = w;
  n.a = *g;
  n.b1 = b1->bound;
  n.b2 = b2->bound;
  n.c1 = *n1;
  n.c2 = *n2;
  cert::SB bound = cert::SB(w) + cert::smax(b1->bound, b2->bound);
  CertPiece out{mk(n), join, bound};
  if (choose) out = seqPiece(CertPiece{choose, start, 0}, out);
  if (calls) out = seqPiece(*calls, out);
  return out;
}

std::optional<Analyzer::CertPiece> Analyzer::certLoop(CertCtx& cc, const Stmt* loop, const Expr* cond,
                                                     const Stmt* body, const Expr* inc,
                                                     const cert::Assn& pre) {
  auto pit = cc.potentials->find(loop);
  if (pit == cc.potentials->end())
    return cc.failed("loop without a derived potential (annotated or not bounded)"), std::nullopt;
  Scan sc = scanOf(cond, cc.var);
  if (sc.calls || sc.writes) return cc.failed("loop test with a call or an assignment"), std::nullopt;
  std::vector<PExp> gs;
  bool nondet = false;
  if (!certTestList(cc, cond, gs, nondet)) return cc.failed("loop test not in the fragment"), std::nullopt;
  std::uint64_t w = cond ? costOf(cond) + w_.branch : 0;

  // The potential, scaled to integer coefficients: pot = D * V, decrease d = D.
  const LoopPotential& lp = pit->second;
  std::int64_t den = std::max<std::int64_t>(1, lp.rank.offset.den);
  for (const Rational& q : lp.rank.weights) den = std::lcm(den, std::max<std::int64_t>(1, q.den));
  PExp pot;
  for (std::size_t i = 0; i < lp.slots.size(); ++i) {
    const Rational& q = lp.rank.weights[i];
    if (q.num == 0) continue;
    auto it = cc.var.find(lp.slots[i]);
    if (it == cc.var.end()) return cc.failed("potential over a variable outside the fragment"), std::nullopt;
    if (pot.sv.size() <= it->second) pot.sv.resize(it->second + 1, 0);
    pot.sv[it->second] += q.num * (den / q.den);
  }
  pot.c = lp.rank.offset.num * (den / lp.rank.offset.den);
  trimP(pot);
  std::uint64_t dA = static_cast<std::uint64_t>(den);
  std::size_t j = cc.depth;

  // Jumps out of the body become flags tested by the loop: break, continue, return.
  JumpScan js = jumpsOf(body);
  bool rets = hasReturn(body);
  CertCtx::Exit ex;
  ex.loop = true;
  if (js.brk) ex.brk = cc.freshVar(cc.prefix + "?break" + std::to_string(j));
  if (js.cnt) ex.cnt = cc.freshVar(cc.prefix + "?continue" + std::to_string(j));
  if (rets && cc.ret == CertCtx::none) cc.ret = cc.freshVar(cc.prefix + "?return");
  std::size_t choiceVar = nondet ? cc.freshVar(cc.prefix + "?test" + std::to_string(j)) : CertCtx::none;
  std::vector<std::size_t> exitFlags;
  if (ex.brk != CertCtx::none) exitFlags.push_back(ex.brk);
  if (rets) exitFlags.push_back(cc.ret);
  std::size_t nC = gs.size();  // conjuncts of the C test
  for (std::size_t f : exitFlags) gs.push_back(PExp{cert::unitVec(f), 0});
  if (nondet) gs.push_back(PExp{cert::unitVec(choiceVar), 0});
  if (gs.empty()) return cc.failed("loop without a test or a break"), std::nullopt;
  bool single = gs.size() == 1 && exitFlags.empty() && !nondet;

  // Prologue: flags cleared, the unknown part of the test chosen.
  CertPiece prolog{mk(Node{}), pre, 0};
  auto then = [&](std::optional<CertPiece> p) {
    if (!p) return false;
    prolog = seqPiece(prolog, *p);
    return true;
  };
  for (std::size_t f : exitFlags)
    if (!then(certAssign(cc, 0, f, PExp{{}, 0}, prolog.post))) return std::nullopt;
  if (nondet && !then(certAssign(cc, 0, choiceVar, std::nullopt, prolog.post))) return std::nullopt;
  const Assn& entry = prolog.post;

  std::vector<const Stmt*> stmts = flatten(body);
  auto skipF = [&](const Assn& p) -> std::optional<CertPiece> { return CertPiece{mk(Node{}), p, 0}; };
  auto runBody = [&](const Assn& p, const Assn& hint) -> std::optional<CertPiece> {
    ++cc.depth;
    cc.exits.push_back(ex);
    cc.hints.push_back(hint);
    CertPiece acc{mk(Node{}), p, 0};
    bool ok = true;
    auto add = [&](std::optional<CertPiece> q) {
      if (!q) { ok = false; return; }
      acc = seqPiece(acc, *q);
    };
    if (ex.cnt != CertCtx::none) add(certAssign(cc, 0, ex.cnt, PExp{{}, 0}, acc.post));
    if (ok) add(certList(cc, stmts, 0, acc.post));
    if (ok && inc) {
      // The increment runs unless the body left the loop (continue does run it).
      std::function<std::optional<CertPiece>(const Assn&)> incF = [&](const Assn& q) {
        return certExpr(cc, inc, q);
      };
      for (std::size_t f : exitFlags) {
        auto inner = incF;
        incF = [&, f, inner](const Assn& q) {
          return certIfThen(cc, PExp{cert::unitVec(f), 0}, 0, inner, skipF, q);
        };
      }
      add(incF(acc.post));
    }
    if (ok && nondet) add(certAssign(cc, 0, choiceVar, std::nullopt, acc.post));
    cc.hints.pop_back();
    cc.exits.pop_back();
    --cc.depth;
    if (!ok) return std::nullopt;
    return acc;
  };
  auto testLins = [&]() {
    Assn t;
    for (const PExp& g : gs) t.push_back(cert::toLin(g));
    return t;
  };

  // Invariant: Houdini over the constraints known on entry, the guard relaxed by one,
  // and the ranges of the flags.
  Assn cands = cert::normalize(entry);
  if (gs.size() >= 1 && !gs.empty()) {
    Lin relaxed = cert::toLin(gs[0]);
    relaxed.c -= 1;
    Assn one = cert::normalize({relaxed});
    if (!one.empty() && cert::farkas(entry, one[0])) cands.push_back(one[0]);
  }
  for (std::size_t f : exitFlags) {
    cands.push_back(Lin{cert::vsmul(-1, cert::unitVec(f)), {}, 0});  // f >= 0
    cands.push_back(Lin{cert::unitVec(f), {}, -1});                  // f <= 1
  }
  cands = cert::normalize(cands);
  cands.erase(std::remove_if(cands.begin(), cands.end(),
                             [&](const Lin& e) {
                               return cert::coeff(e.lv, j) != 0 || !cert::farkas(entry, e);
                             }),
              cands.end());
  for (std::size_t round = 0; round <= cands.size() + 1; ++round) {
    Assn p = testLins();
    p.insert(p.end(), cands.begin(), cands.end());
    std::optional<CertPiece> b = runBody(p, cands);
    if (!b) return std::nullopt;
    Assn kept;
    for (const Lin& e : cands)
      if (cert::farkas(b->post, e)) kept.push_back(e);
    if (kept.size() == cands.size()) break;
    cands = std::move(kept);
  }
  const Assn& inv = cands;

  // Potentials to try. In a function with parameters, first the one the loop test
  // suggests (`1 - g` for the test `g <= 0`, e.g. `n - i` for `i < n`), whose entry bound
  // is often a function of the parameters (a summary); then the analysis' potential. The
  // checker verifies either.
  std::vector<std::pair<PExp, std::uint64_t>> potentials;
  if (cc.gammas && nC > 0) {
    PExp gp{cert::vsmul(-1, gs[0].sv), 1 - gs[0].c};
    trimP(gp);
    if (!(gp.sv == pot.sv && gp.c == pot.c)) potentials.push_back({gp, 1});
  }
  potentials.push_back({pot, dA});
  // A potential whose entry bound is a fraction of a parameter (`blockSize >> 2`) has a
  // summary once scaled: `a*pot` with decrease `a*d`. Tried first (a tie keeps it).
  if (cc.gammas) {
    std::vector<std::pair<PExp, std::uint64_t>> scaled;
    for (const auto& [p0, d0] : potentials) {
      std::int64_t a = cert::symbolicScale(entry, p0, cc.temp(), cc.gammas);
      if (a > 1 && a <= 64) {
        PExp ps{cert::vsmul(a, p0.sv), a * p0.c};
        scaled.push_back({ps, d0 * static_cast<std::uint64_t>(a)});
      }
    }
    potentials.insert(potentials.begin(), scaled.begin(), scaled.end());
  }
  std::string lastWhy;
  // The candidates are compared by their bound at the largest admissible parameters;
  // the first one wins a tie.
  std::optional<CertPiece> best;
  std::uint64_t bestValue = 0;
  std::vector<std::uint64_t> hiVec;
  for (const auto& h : cc.gammaHi) hiVec.push_back(h ? *h : 0);
  for (const auto& [pot0, d] : potentials) {
  // The iteration that leaves by a jump need not decrease the potential: it is paid by
  // a term c * (1 - flags), which is c while the loop runs and 0 once a flag is set.
  std::vector<std::int64_t> extras{0};
  if (!exitFlags.empty()) {
    extras.clear();
    for (std::int64_t m = 1; m <= 64; m *= 2) extras.push_back(m * static_cast<std::int64_t>(d));
  }
  for (std::int64_t c : extras) {
    PExp potc = pot0;
    potc.c += c;
    for (std::size_t f : exitFlags) {
      if (potc.sv.size() <= f) potc.sv.resize(f + 1, 0);
      potc.sv[f] -= c;
    }
    Assn guardInv = testLins();
    guardInv.insert(guardInv.end(), inv.begin(), inv.end());
    std::optional<Farkas> posCert = cert::farkas(guardInv, Lin{cert::vsmul(-1, potc.sv), {},
                                                               static_cast<std::int64_t>(d) - potc.c});
    if (!posCert) { lastWhy = "the potential is not shown positive by the invariant"; continue; }
    // Entry bound: symbolic in the parameters if possible, else a constant.
    std::optional<std::pair<std::int64_t, std::vector<std::uint64_t>>> sym;
    if (cc.gammas) {
      sym = cert::symbolicUpper(entry, potc, cc.temp(), cc.gammas);
      if (sym && sym->second.empty()) sym.reset();
    }
    std::optional<std::int64_t> k = cert::upperBound(entry, potc);
    if (!k && !sym) { lastWhy = "the potential is unbounded on entry"; continue; }
    Assn bodyPre = guardInv;
    bodyPre.insert(bodyPre.begin(), cert::ghost(potc, j, 0));
    Assn bodyPost = inv;
    bodyPost.insert(bodyPost.begin(), cert::ghost(potc, j, static_cast<std::int64_t>(d)));
    std::optional<CertPiece> b = runBody(bodyPre, bodyPost);
    if (!b) return std::nullopt;
    std::optional<std::vector<Farkas>> qc = cert::farkasAll(b->post, bodyPost);
    if (!qc) { lastWhy = "the decrease of the potential could not be certified"; continue; }
    // A symbolic entry bound needs a constant body bound (the bound stays affine), and is
    // used only if it is no looser than the constant one at the largest parameter values.
    bool useSym = sym && b->bound.constant();
    if (useSym && k) {
      std::vector<std::uint64_t> hi;
      for (const auto& h : cc.gammaHi) hi.push_back(h ? *h : 0);
      bool allBounded = cc.atHi(sym->first, sym->second).has_value();
      std::uint64_t vs = cert::sbAt(cert::whileBoundSym(sym->first, sym->second, d, w, b->bound.c), hi);
      std::uint64_t vn = cert::whileBound(*k, d, w, b->bound).c;
      if (!allBounded || vs > vn) useSym = false;
    }
    if (!useSym && !k) { lastWhy = "symbolic entry bound with a symbolic body bound"; continue; }
    std::int64_t kk = useSym ? sym->first : *k;
    std::vector<std::uint64_t> kl = useSym ? sym->second : std::vector<std::uint64_t>{};

    Node wn;
    wn.kind = single ? Node::While : Node::WhileAnd;
    wn.w = w;
    if (single) wn.a = gs[0];
    else wn.gs = gs;
    wn.inv = inv;
    wn.pot = potc;
    wn.d = d;
    wn.k = kk;
    wn.kl = kl;
    wn.j = j;
    wn.posCert = *posCert;
    wn.b1 = b->bound;
    wn.c1 = weaken(bodyPre, identityCerts(bodyPre), b->bound, b->post, *qc, b->node);
    Assn pw = inv;
    {
      Vec lv;
      for (std::uint64_t x : kl) lv.push_back(-static_cast<std::int64_t>(x));
      pw.insert(pw.begin(), Lin{potc.sv, lv, potc.c - kk});
    }
    Assn qw = inv;
    if (single) qw.insert(qw.begin(), cert::negLin(gs[0]));
    cert::SB bw = useSym ? cert::whileBoundSym(kk, kl, d, w, b->bound.c)
                         : cert::whileBound(kk, d, w, b->bound);
    std::optional<std::vector<Farkas>> pc = cert::farkasAll(entry, pw);
    if (!pc) { lastWhy = "internal: loop entry"; continue; }
    CertPiece lp{weaken(pw, *pc, bw, qw, identityCerts(qw), mk(wn)), qw, bw};
    std::uint64_t value = cert::sbAt(bw, hiVec);
    if (!best || value < bestValue) {
      best = seqPiece(prolog, lp);
      bestValue = value;
    }
    break;  // the first accepted extra term is the smallest for this potential
  }
  }
  if (best) return best;
  return cc.failed(lastWhy), std::nullopt;
}

namespace {
/// The calls of an expression that are not inside another call's arguments.
struct OuterCalls : RecursiveASTVisitor<OuterCalls> {
  std::vector<const CallExpr*> calls;
  bool TraverseCallExpr(CallExpr* c) { calls.push_back(c); return true; }
  bool TraverseCXXMemberCallExpr(CXXMemberCallExpr* c) { calls.push_back(c); return true; }
  bool TraverseCXXOperatorCallExpr(CXXOperatorCallExpr* c) { calls.push_back(c); return true; }
  bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr*) { return true; }
  bool TraverseLambdaExpr(LambdaExpr*) { return true; }
};
}  // namespace

std::optional<Analyzer::CertPiece> Analyzer::certCallsIn(CertCtx& cc, const Expr* e,
                                                        const cert::Assn& pre) {
  OuterCalls oc;
  oc.TraverseStmt(const_cast<Expr*>(e));
  CertPiece acc{mk(Node{}), pre, 0};
  for (const CallExpr* c : oc.calls) {
    std::optional<CertPiece> p = certCall(cc, c, acc.post);
    if (!p) return std::nullopt;
    acc = seqPiece(acc, *p);
  }
  return acc;
}

namespace {
/// The constraint `e` of a callee read at the call site (Lean `Lin.inst`; only its
/// meaning matters, the checker computes the list itself).
Lin instLin(const Lin& e, const std::vector<PExp>& inst) {
  Lin r{e.sv, {}, e.c};
  for (std::size_t j = 0; j < e.lv.size() && j < inst.size(); ++j) {
    r.sv = cert::vadd(r.sv, cert::vsmul(e.lv[j], inst[j].sv));
    r.c += e.lv[j] * inst[j].c;
  }
  return r;
}
/// `a - ub <= 0` (Lean `ubLin`).
Lin ubLin(const PExp& a, const cert::SB& ub) {
  Vec lv;
  for (std::uint64_t x : ub.co) lv.push_back(-static_cast<std::int64_t>(x));
  return Lin{a.sv, lv, a.c - static_cast<std::int64_t>(ub.c)};
}
/// The constraints of `p` that do not mention `mods` (Lean `frameOf`).
Assn frameOf(const std::vector<std::size_t>& mods, const Assn& p) {
  Assn out;
  for (const Lin& e : p) {
    bool keep = true;
    for (std::size_t x : mods)
      if (cert::coeff(e.sv, x) != 0) keep = false;
    if (keep) out.push_back(e);
  }
  return out;
}
}  // namespace

/// A call of the function `ci` of the program certificate: its parameters (variables
/// of the callee) are set to the arguments, its precondition and the bounds of its
/// arguments are proved, and only the facts that do not mention its variables survive.
std::optional<Analyzer::CertPiece> Analyzer::certCallNode(CertCtx& cc, const CertFunInfo& ci,
                                                         const std::vector<const Expr*>& args,
                                                         const cert::Assn& pre) {
  const cert::FunJson& F = certFuns_.at(ci.index);
  CertPiece acc{mk(Node{}), pre, 0};
  for (std::size_t g = 0; g < ci.ghostVars.size(); ++g) {
    const ParmVarDecl* p = ci.ghostParams[g];
    unsigned i = p->getFunctionScopeIndex();
    if (i >= args.size()) return std::nullopt;
    std::size_t x = ci.ghostVars[g];
    std::optional<PExp> a = ctx_.hasSameUnqualifiedType(args[i]->getType(), p->getType()) ||
                                    widens(args[i]->getType(), p->getType()) || cc.uwidth.count(x)
                                ? certValueFor(cc, x, args[i])
                                : std::nullopt;
    std::optional<CertPiece> b = certStore(cc, 0, x, a, acc.post);
    if (!b) return std::nullopt;
    acc = seqPiece(acc, *b);
  }
  std::vector<PExp> inst;
  for (std::size_t x : ci.ghostVars) inst.push_back(PExp{cert::unitVec(x), 0});
  Assn goals;
  for (const Lin& e : F.pre) goals.push_back(instLin(e, inst));
  std::optional<std::vector<Farkas>> pcs = cert::farkasAll(acc.post, goals);
  if (!pcs) return std::nullopt;
  std::vector<cert::SB> ubs;
  std::vector<Farkas> ucs;
  std::vector<std::uint64_t> co = F.bound.co;
  while (!co.empty() && co.back() == 0) co.pop_back();
  for (std::size_t g = 0; g < co.size(); ++g) {
    // A bound in the caller's parameters if there is one (summaries compose), else a
    // constant.
    std::optional<cert::SB> ub;
    std::optional<std::int64_t> k = cert::upperBound(acc.post, inst[g]);
    if (auto sy = cert::symbolicUpper(acc.post, inst[g], cc.temp(), cc.gammas)) {
      std::optional<std::int64_t> v = cc.atHi(std::max<std::int64_t>(0, sy->first), sy->second);
      if (!k || (v && *v <= std::max<std::int64_t>(0, *k))) {
        cert::SB u(static_cast<std::uint64_t>(std::max<std::int64_t>(0, sy->first)));
        u.co = sy->second;
        ub = u;
      }
    }
    if (!ub && k) ub = cert::SB(static_cast<std::uint64_t>(std::max<std::int64_t>(0, *k)));
    if (!ub) return std::nullopt;
    std::optional<Farkas> fk = cert::farkas(acc.post, ubLin(inst[g], *ub));
    if (!fk) return std::nullopt;
    ubs.push_back(*ub);
    ucs.push_back(*fk);
  }
  Node n;
  n.kind = Node::Call;
  n.w = 0;  // the call's own cost is charged by the enclosing expression (costOf)
  n.f = ci.index;
  n.inst = inst;
  n.preCerts = *pcs;
  n.ubs = ubs;
  n.postCerts = ucs;
  cert::SB bound(F.bound.c);
  for (std::size_t g = 0; g < co.size(); ++g) bound = bound + cert::scale(co[g], ubs[g]);
  return seqPiece(acc, CertPiece{mk(n), frameOf(F.mods, acc.post), bound});
}

/// The assumed contract of a function with a trusted cost, created at its first use:
/// `CROSSCHECK_COST(n)` gives the constant bound `n`; a contract file a bound
/// `c + sum a_i * max(0, arg_i)`, its arguments being variables of the contract.
std::optional<Analyzer::CertFunInfo> Analyzer::contractFun(CertCtx& cc, const FunctionDecl* fd) {
  const FunctionDecl* key = fd->getCanonicalDecl();
  if (auto it = certContractOf_.find(key); it != certContractOf_.end()) return it->second;
  cert::FunJson F;
  CertFunInfo info;
  F.name = "contract " + fd->getQualifiedNameAsString();
  if (const AnnotateAttr* a = findAnnotation(fd, "crosscheck::cost")) {
    auto n = annotationArg(a, 0, ctx_);
    if (!n || *n < 0) return std::nullopt;
    F.bound = cert::SB(static_cast<std::uint64_t>(*n));
  } else if (const LibContract* lc = libContract(fd)) {
    F.bound = cert::SB(lc->c);
    for (unsigned i = 0; i < fd->getNumParams(); ++i) {
      auto pa = lc->perArg.find(i);
      if (pa == lc->perArg.end()) continue;
      const ParmVarDecl* p = fd->getParamDecl(i);
      if (!certInt(p->getType())) return std::nullopt;
      std::size_t x = cc.freshVar(F.name + "::" + (p->getName().empty() ? "arg" + std::to_string(i) : p->getNameAsString()));
      if (p->getType()->isUnsignedIntegerType()) cc.uwidth[x] = ctx_.getIntWidth(p->getType());
      std::size_t g = info.ghostVars.size();
      info.ghostVars.push_back(x);
      info.ghostParams.push_back(p);
      F.pre.push_back(Lin{cert::unitVec(x), cert::vsmul(-1, cert::unitVec(g)), 0});
      F.pre.push_back(Lin{cert::vsmul(-1, cert::unitVec(x)), cert::unitVec(g), 0});
      if (F.bound.co.size() <= g) F.bound.co.resize(g + 1, 0);
      F.bound.co[g] = pa->second;
      F.mods.push_back(x);
    }
  } else {
    return std::nullopt;
  }
  info.index = certFuns_.size();
  certFuns_.push_back(std::move(F));
  certContractOf_[key] = info;
  return info;
}

std::optional<Analyzer::CertPiece> Analyzer::certCall(CertCtx& cc, const CallExpr* call,
                                                     const cert::Assn& pre) {
  const FunctionDecl* fd = call->getDirectCallee();
  if (!fd) return cc.failed("indirect call"), std::nullopt;
  std::vector<const Expr*> cargs(call->arg_begin(), call->arg_end());
  if (isa<CXXOperatorCallExpr>(call))
    if (const auto* md = dyn_cast<CXXMethodDecl>(fd); md && md->isInstance() && !cargs.empty())
      cargs.erase(cargs.begin());
  auto argCalls = [&](const Assn& p0) -> std::optional<CertPiece> {
    CertPiece acc{mk(Node{}), p0, 0};
    for (const Expr* a : cargs) {
      Scan sc = scanOf(a, cc.var);
      if (sc.writes) return cc.failed("assignment in an argument"), std::nullopt;
      if (sc.calls) {
        std::optional<CertPiece> inner = certCallsIn(cc, a, acc.post);
        if (!inner) return std::nullopt;
        acc = seqPiece(acc, *inner);
      }
    }
    return acc;
  };
  // A function with a trusted cost (CROSSCHECK_COST, contract file): an assumed contract.
  if (std::optional<CertFunInfo> ci = contractFun(cc, fd)) {
    std::optional<CertPiece> acc = argCalls(pre);
    if (!acc) return std::nullopt;
    std::optional<CertPiece> c = certCallNode(cc, *ci, cargs, acc->post);
    if (!c) return cc.failed("call of '" + fd->getQualifiedNameAsString() + "': its contract's precondition or argument bounds could not be shown"), std::nullopt;
    return seqPiece(*acc, *c);
  }
  auto kit = cc.callKeys->find(call);
  if (kit == cc.callKeys->end())
    return cc.failed("call to a function without an analysed body"), std::nullopt;
  auto sit = cache_.find(kit->second);
  const FunctionDecl* def = nullptr;
  if (sit == cache_.end() || !fd->hasBody(def) || !def || !sit->second.ok)
    return cc.failed("call to a function that is not bounded"), std::nullopt;
  const Summary& sm = sit->second;
  const auto* body = dyn_cast_or_null<CompoundStmt>(def->getBody());
  if (!body) return cc.failed("callee without a body"), std::nullopt;
  if (cc.inlining.count(def->getCanonicalDecl()) || cc.inlining.size() > 8)
    return cc.failed("recursive or deeply nested calls"), std::nullopt;
  std::vector<const Expr*> args(call->arg_begin(), call->arg_end());
  if (isa<CXXOperatorCallExpr>(call))
    if (const auto* md = dyn_cast<CXXMethodDecl>(fd); md && md->isInstance() && !args.empty())
      args.erase(args.begin());
  // Calls in the arguments first. The cost of the arguments and of the call itself is
  // charged by the enclosing expression (costOf); here only the callee's body.
  CertPiece acc{mk(Node{}), pre, 0};
  for (const Expr* a : args) {
    Scan sc = scanOf(a, cc.var);
    if (sc.writes) return cc.failed("assignment in an argument"), std::nullopt;
    if (sc.calls) {
      std::optional<CertPiece> inner = certCallsIn(cc, a, acc.post);
      if (!inner) return std::nullopt;
      acc = seqPiece(acc, *inner);
    }
  }
  // A callee with its own certificate: a call of its summary instead of its body.
  if (auto ci = certFunOf_.find(def->getCanonicalDecl()); ci != certFunOf_.end()) {
    std::string savedFail = cc.fail;
    if (std::optional<CertPiece> c = certCallNode(cc, ci->second, args, acc.post))
      return seqPiece(acc, *c);
    cc.fail = savedFail;  // otherwise inline it
  }
  std::string savedPrefix = cc.prefix;
  cc.prefix = def->getNameAsString() + "::";
  // Parameters receive the arguments (evaluated in the caller's variables).
  std::vector<std::pair<std::size_t, std::optional<PExp>>> binds;
  for (unsigned i = 0; i < def->getNumParams() && i < args.size(); ++i) {
    const ParmVarDecl* p = def->getParamDecl(i);
    if (!sm.tracked.count(p) || !certInt(p->getType())) continue;
    cc.addVar(p);
    if (!cc.var.count(p)) continue;
    std::size_t x = cc.var.at(p);
    // The argument as converted to the parameter's type (an implicit conversion of
    // args[i] itself is part of the expression).
    std::optional<PExp> a = ctx_.hasSameUnqualifiedType(args[i]->getType(), p->getType()) ||
                                    widens(args[i]->getType(), p->getType()) || cc.uwidth.count(x)
                                ? certValueFor(cc, x, args[i])
                                : std::nullopt;
    binds.push_back({x, a});
  }
  for (const VarDecl* v : sm.tracked)
    if (!isa<ParmVarDecl>(v) && certInt(v->getType())) cc.addVar(v);
  // Simultaneous binding: arguments only mention the caller's variables.
  for (const auto& [x, a] : binds) {
    std::optional<CertPiece> b = certStore(cc, 0, x, a, acc.post);
    if (!b) { cc.prefix = savedPrefix; return std::nullopt; }
    acc = seqPiece(acc, *b);
  }
  const auto* savedPot = cc.potentials;
  const auto* savedKeys = cc.callKeys;
  cc.potentials = sm.potentials.get();
  cc.callKeys = &sm.callKeys;
  cc.inlining.insert(def->getCanonicalDecl());
  // A `return` of the callee ends the callee only: its body gets its own exits,
  // return flag and join hints, not those of the caller's enclosing loops.
  std::vector<CertCtx::Exit> savedExits;
  std::vector<cert::Assn> savedHints;
  std::swap(savedExits, cc.exits);
  std::swap(savedHints, cc.hints);
  std::size_t savedRet = cc.ret;
  cc.ret = CertCtx::none;
  std::vector<const Stmt*> list(body->body_begin(), body->body_end());
  std::optional<CertPiece> b = certList(cc, list, 0, acc.post);
  std::swap(savedExits, cc.exits);
  std::swap(savedHints, cc.hints);
  cc.ret = savedRet;
  cc.inlining.erase(def->getCanonicalDecl());
  cc.potentials = savedPot;
  cc.callKeys = savedKeys;
  cc.prefix = savedPrefix;
  if (!b) return std::nullopt;
  return seqPiece(acc, *b);
}

std::optional<Analyzer::CertPiece> Analyzer::certStmt(CertCtx& cc, const Stmt* st, const cert::Assn& pre) {
  if (cc.prefix.empty()) cc.line = lineOf(st->getBeginLoc());
  if (const auto* cs = dyn_cast<CompoundStmt>(st)) {
    std::vector<const Stmt*> list(cs->body_begin(), cs->body_end());
    return certList(cc, list, 0, pre);
  }
  if (isa<NullStmt>(st)) return CertPiece{mk(Node{}), pre, 0};
  if (const auto* ds = dyn_cast<DeclStmt>(st)) {
    std::vector<const Stmt*> none;
    CertPiece acc{mk(Node{}), pre, 0};
    bool firstDone = false;
    for (const Decl* d : ds->decls()) {
      const auto* vd = dyn_cast<VarDecl>(d);
      if (!vd) continue;
      const Expr* init = vd->getInit();
      Scan sc = scanOf(init, cc.var);
      if (sc.writes) return cc.failed("assignment inside an expression"), std::nullopt;
      std::optional<CertPiece> p;
      auto it = cc.var.find(vd);
      CertPiece before{mk(Node{}), acc.post, 0};
      if (sc.calls) {
        std::optional<CertPiece> c = certCallsIn(cc, init, acc.post);
        if (!c) return std::nullopt;
        before = *c;
      }
      std::uint64_t wd = (init ? costOf(init) : 0) + (init && isIntType(vd->getType()) ? w_.assign : 0);
      if (it != cc.var.end()) {
        std::optional<PExp> a = init ? certValueFor(cc, it->second, init) : std::nullopt;
        p = std::nullopt;
        if (!a && init) p = certStoreTable(cc, wd, it->second, vd->getType(), init, before.post);
        if (!p && !a && init)
          if (const auto* d = dyn_cast<BinaryOperator>(init->IgnoreParenImpCasts()))
            p = certStoreDivision(cc, wd, it->second, vd->getType(), d->getLHS(), d->getOpcode(),
                                  d->getRHS(), d->getType(), before.post);
        if (!p) p = certStore(cc, wd, it->second, a, before.post);
      } else {
        Node n;
        n.kind = Node::Havoc;
        n.w = wd;
        n.x = cc.dummy;
        p = CertPiece{mk(n), before.post, wd};
      }
      if (p && sc.calls) p = seqPiece(before, *p);
      if (!p) return std::nullopt;
      if (!firstDone) {
        acc = *p;
        firstDone = true;
      } else {
        Node s;
        s.kind = Node::Seq;
        s.c1 = acc.node;
        s.mid = acc.post;
        s.b1 = acc.bound;
        s.b2 = p->bound;
        s.c2 = p->node;
        acc = CertPiece{mk(s), p->post, acc.bound + p->bound};
      }
    }
    return acc;
  }
  if (const auto* is = dyn_cast<IfStmt>(st))
    return certIf(cc, is, flatten(is->getThen()), flatten(is->getElse()), pre);
  if (const auto* sw = dyn_cast<SwitchStmt>(st)) return certSwitch(cc, sw, pre);
  if (const auto* ws = dyn_cast<WhileStmt>(st)) {
    if (ws->getConditionVariable()) return cc.failed("condition variable"), std::nullopt;
    return certLoop(cc, ws, ws->getCond(), ws->getBody(), nullptr, pre);
  }
  if (const auto* fs = dyn_cast<ForStmt>(st)) {
    if (fs->getConditionVariable()) return cc.failed("condition variable"), std::nullopt;
    CertPiece init{mk(Node{}), pre, 0};
    if (fs->getInit()) {
      std::optional<CertPiece> i = certStmt(cc, fs->getInit(), pre);
      if (!i) return std::nullopt;
      init = *i;
    }
    std::optional<CertPiece> l = certLoop(cc, fs, fs->getCond(), fs->getBody(), fs->getInc(), init.post);
    if (!l) return std::nullopt;
    if (!fs->getInit()) return l;
    Node s;
    s.kind = Node::Seq;
    s.c1 = init.node;
    s.mid = init.post;
    s.b1 = init.bound;
    s.b2 = l->bound;
    s.c2 = l->node;
    return CertPiece{mk(s), l->post, init.bound + l->bound};
  }
  if (const auto* rs = dyn_cast<ReturnStmt>(st)) {
    const Expr* v = rs->getRetValue();
    Scan sc = scanOf(v, cc.var);
    if (sc.writes) return cc.failed("assignment inside an expression"), std::nullopt;
    Node n;
    n.kind = Node::Havoc;
    n.x = cc.dummy;
    if (sc.calls) {
      std::optional<CertPiece> c = certCallsIn(cc, v, pre);
      if (!c) return std::nullopt;
      n.w = costOf(v) + w_.ret;
      return seqPiece(*c, CertPiece{mk(n), c->post, n.w});
    }
    n.w = costOf(v) + w_.ret;
    return CertPiece{mk(n), pre, n.w};
  }
  if (const auto* e = dyn_cast<Expr>(st)) {
    if (asMarker(e, "require")) return CertPiece{mk(Node{}), pre, 0};
    if (asMarker(e, "assume") || asMarker(e, "loop_bound"))
      return cc.failed("trusted annotation (CROSSCHECK_ASSUME / LOOP_BOUND) not in the fragment yet"),
             std::nullopt;
    return certExpr(cc, e, pre);
  }
  if (const auto* as = dyn_cast<AttributedStmt>(st)) return certStmt(cc, as->getSubStmt(), pre);
  return cc.failed(std::string("statement not in the fragment (") + st->getStmtClassName() + ")"),
         std::nullopt;
}

namespace {
/// Variables that can influence control: those of tests and potentials, closed
/// under the assignments and parameter passing that feed them. The others are not
/// variables of the certificate (their assignments only cost their weight).
struct FlowScan : RecursiveASTVisitor<FlowScan> {
  std::set<const VarDecl*> control;
  /// The arguments whose values a function's contract cost depends on.
  std::function<std::vector<unsigned>(const FunctionDecl*)> costArgs;
  std::vector<std::pair<const VarDecl*, std::set<const VarDecl*>>> flows;
  std::set<const FunctionDecl*> seen;
  static std::set<const VarDecl*> varsOf(const Stmt* s) {
    struct V : RecursiveASTVisitor<V> {
      std::set<const VarDecl*> out;
      bool VisitDeclRefExpr(DeclRefExpr* d) {
        if (const auto* v = dyn_cast<VarDecl>(d->getDecl())) out.insert(v);
        return true;
      }
    } v;
    if (s) v.TraverseStmt(const_cast<Stmt*>(s));
    return v.out;
  }
  static const VarDecl* lhsVar(const Expr* e) {
    if (const auto* d = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) return dyn_cast<VarDecl>(d->getDecl());
    return nullptr;
  }
  void test(const Expr* e) {
    auto vs = varsOf(e);
    control.insert(vs.begin(), vs.end());
  }
  bool VisitIfStmt(IfStmt* s) { test(s->getCond()); return true; }
  bool VisitWhileStmt(WhileStmt* s) { test(s->getCond()); return true; }
  bool VisitForStmt(ForStmt* s) { test(s->getCond()); return true; }
  bool VisitDoStmt(DoStmt* s) { test(s->getCond()); return true; }
  bool VisitSwitchStmt(SwitchStmt* s) { test(s->getCond()); return true; }
  bool VisitConditionalOperator(ConditionalOperator* c) { test(c->getCond()); return true; }
  bool VisitBinaryOperator(BinaryOperator* e) {
    if (e->isLogicalOp()) test(e);
    if (e->isAssignmentOp())
      if (const VarDecl* v = lhsVar(e->getLHS())) {
        auto src = varsOf(e->getRHS());
        if (e->isCompoundAssignmentOp()) src.insert(v);
        flows.push_back({v, src});
      }
    return true;
  }
  bool VisitVarDecl(VarDecl* v) {
    if (v->getInit()) flows.push_back({v, varsOf(v->getInit())});
    return true;
  }
  bool VisitCallExpr(CallExpr* c) {
    const FunctionDecl* fd = c->getDirectCallee();
    const FunctionDecl* def = nullptr;
    if (fd && costArgs)
      for (unsigned i : costArgs(fd))
        if (i < c->getNumArgs()) test(c->getArg(i));
    if (!fd || !fd->hasBody(def) || !def) return true;
    unsigned first = 0;
    if (isa<CXXOperatorCallExpr>(c))
      if (const auto* md = dyn_cast<CXXMethodDecl>(fd); md && md->isInstance()) first = 1;
    for (unsigned i = 0; i + first < c->getNumArgs() && i < def->getNumParams(); ++i)
      flows.push_back({def->getParamDecl(i), varsOf(c->getArg(i + first))});
    if (seen.insert(def->getCanonicalDecl()).second && def->getBody())
      TraverseStmt(def->getBody());
    return true;
  }
  bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr*) { return true; }
  std::set<const VarDecl*> close() {
    std::set<const VarDecl*> r = control;
    for (bool changed = true; changed;) {
      changed = false;
      for (const auto& [t, src] : flows)
        if (r.count(t))
          for (const VarDecl* v : src) changed |= r.insert(v).second;
    }
    return r;
  }
};
}  // namespace

bool Analyzer::certificate(const FunctionDecl* def, std::string& reason, cert::SB& bound,
                           std::optional<std::uint64_t>& numeric, std::string& summary) {
  FnCtx& fc = cur();
  CertCtx cc;
  if (callsItself(def)) { reason = "recursive function (not in the fragment yet)"; return false; }
  // The variables of the program certificate of the translation unit; this function's
  // own variables are added to them (kept only if its certificate is emitted).
  cc.names = certNames_;
  cc.uwidth = certUWidth_;
  cc.globalVar = certGlobalVar_;
  cc.prefix = def->getQualifiedNameAsString() + "::";
  cc.potentials = &fc.potentials;
  cc.callKeys = &fc.callKeys;
  cc.inlining.insert(def->getCanonicalDecl());
  {
    FlowScan fs;
    fs.costArgs = [this](const FunctionDecl* f) {
      std::vector<unsigned> out;
      if (const LibContract* lc = libContract(f))
        for (const auto& [i, a] : lc->perArg) out.push_back(i);
      return out;
    };
    fs.seen.insert(def->getCanonicalDecl());
    fs.TraverseStmt(def->getBody());
    auto addSlots = [&](const std::map<const Stmt*, LoopPotential>& m) {
      for (const auto& [l, lp] : m)
        for (std::size_t i = 0; i < lp.slots.size() && i < lp.rank.weights.size(); ++i)
          if (lp.rank.weights[i].num != 0) fs.control.insert(lp.slots[i]);
    };
    addSlots(fc.potentials);
    for (const auto& [key, sm] : cache_)
      if (sm.potentials && fs.seen.count(key.first)) addSlots(*sm.potentials);
    cc.relevant = fs.close();
  }
  // Variables: integer parameters, then tracked locals (signed or unsigned).
  for (unsigned i = 0; i < def->getNumParams(); ++i) {
    const ParmVarDecl* p = def->getParamDecl(i);
    if (fc.tracked.count(p) && certInt(p->getType())) cc.addVar(p);
  }
  std::vector<const VarDecl*> locals;
  for (const VarDecl* v : fc.tracked)
    if (!isa<ParmVarDecl>(v) && certInt(v->getType())) locals.push_back(v);
  std::sort(locals.begin(), locals.end(),
            [](const VarDecl* a, const VarDecl* b) { return a->getLocation() < b->getLocation(); });
  for (const VarDecl* v : locals) cc.addVar(v);
  for (const auto& [k, id] : fc.summary.fieldSyms)
    cc.fieldVar[k] = cc.freshVar(cc.prefix + k.first->getNameAsString() + "->" + k.second->getNameAsString());
  cc.prefix.clear();

  // Precondition: the declared ranges and requirements on the parameters, and
  // `x_p = gamma_p` for each integer parameter: its value at entry is a logical
  // variable, in which the bound is expressed (a summary).
  Assn pre;
  CertFunInfo info;
  for (unsigned i = 0; i < def->getNumParams(); ++i) {
    auto it = cc.var.find(def->getParamDecl(i));
    if (it == cc.var.end()) continue;
    std::size_t g = info.ghostVars.size();
    info.ghostVars.push_back(it->second);
    info.ghostParams.push_back(def->getParamDecl(i));
    pre.push_back(Lin{cert::unitVec(it->second), cert::vsmul(-1, cert::unitVec(g)), 0});
    pre.push_back(Lin{cert::vsmul(-1, cert::unitVec(it->second)), cert::unitVec(g), 0});
  }
  cc.gammas = info.ghostVars.size();
  cc.depth = cc.gammas;
  std::map<SymId, std::size_t> paramIndex;
  for (unsigned i = 0; i < def->getNumParams(); ++i)
    if (i < fc.summary.paramSyms.size() && fc.summary.paramSyms[i])
      if (auto it = cc.var.find(def->getParamDecl(i)); it != cc.var.end())
        paramIndex[*fc.summary.paramSyms[i]] = it->second;
  for (const auto& [k, id] : fc.summary.fieldSyms)
    if (auto it = cc.fieldVar.find(k); it != cc.fieldVar.end()) paramIndex[id] = it->second;
  std::vector<Constraint> entryFacts = fc.summary.requires_;
  entryFacts.insert(entryFacts.end(), fc.summary.assumedInputs.begin(), fc.summary.assumedInputs.end());
  for (const Constraint& c : entryFacts) {
    if (c.e.poisoned()) continue;
    Lin l;
    l.c = c.e.constantTerm();
    bool ok = true;
    for (const auto& [s, k] : c.e.terms()) {
      auto it = paramIndex.find(s);
      if (it == paramIndex.end()) { ok = false; break; }
      if (l.sv.size() <= it->second) l.sv.resize(it->second + 1, 0);
      l.sv[it->second] = k;
    }
    if (ok) pre.push_back(l);
  }
  // Unsigned parameters lie in [0, 2^w - 1] (upper limit only for w <= 32, so that
  // the constant fits; leaving it out only weakens the precondition).
  for (unsigned i = 0; i < def->getNumParams(); ++i) {
    auto it = cc.var.find(def->getParamDecl(i));
    if (it == cc.var.end()) continue;
    auto uw = cc.uwidth.find(it->second);
    if (uw == cc.uwidth.end()) continue;
    Lin lo;
    lo.sv = cert::vsmul(-1, cert::unitVec(it->second));
    pre.push_back(lo);
    if (uw->second <= 32) {
      Lin up;
      up.sv = cert::unitVec(it->second);
      up.c = -((std::int64_t(1) << uw->second) - 1);
      pre.push_back(up);
    }
  }
  pre = cert::normalize(pre);
  for (std::size_t x : info.ghostVars) {
    std::optional<std::int64_t> hi = cert::upperBound(pre, PExp{cert::unitVec(x), 0});
    cc.gammaHi.push_back(hi ? std::optional<std::uint64_t>(static_cast<std::uint64_t>(std::max<std::int64_t>(0, *hi)))
                            : std::nullopt);
  }

  const auto* body = dyn_cast_or_null<CompoundStmt>(def->getBody());
  if (!body) { reason = "no body"; return false; }
  std::vector<const Stmt*> list(body->body_begin(), body->body_end());
  std::optional<CertPiece> p = certList(cc, list, 0, pre);
  // The variables created (also those of contracts) stay in the program's table.
  certNames_ = cc.names;
  certUWidth_ = cc.uwidth;
  certGlobalVar_ = cc.globalVar;
  if (!p) {
    reason = cc.fail.empty() ? "unsupported construct" : cc.fail;
    return false;
  }
  NodeP top = weaken(pre, identityCerts(pre), p->bound, p->post, {}, p->node);
  bound = p->bound;
  std::vector<std::vector<std::size_t>> mods;
  for (const cert::FunJson& f : certFuns_) mods.push_back(f.mods);
  cert::FunJson fj;
  fj.name = def->getQualifiedNameAsString();
  fj.pre = pre;
  fj.bound = bound;
  fj.mods = cert::writes(*top, mods);
  fj.body = top;
  info.index = certFuns_.size();
  certFuns_.push_back(std::move(fj));
  certFunOf_[def->getCanonicalDecl()] = info;
  // The bound at the largest parameter values the precondition allows (for the report).
  std::vector<std::string> gnames;
  std::vector<std::uint64_t> at;
  numeric = bound.c;
  for (std::size_t g = 0; g < info.ghostParams.size(); ++g) {
    gnames.push_back(info.ghostParams[g]->getNameAsString());
    std::uint64_t v = 0;
    if (g < bound.co.size() && bound.co[g]) {
      std::optional<std::int64_t> hi = cert::upperBound(pre, PExp{cert::unitVec(info.ghostVars[g]), 0});
      if (!hi) numeric.reset();
      else v = static_cast<std::uint64_t>(std::max<std::int64_t>(0, *hi));
    }
    at.push_back(v);
  }
  if (numeric) numeric = cert::sbAt(bound, at);
  summary = cert::sbString(bound, gnames);
  return true;
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
        rep.errorSites.push_back(siteOf("rejected", fd->getLocation(), msg));
        rep.ok = false;
      } else {
        rep.deadline = static_cast<std::uint64_t>(*n);
        if (rep.bounded && rep.wcet > *rep.deadline) {
          std::string msg = "worst-case cost bound " + std::to_string(rep.wcet) + " of '" +
                            rep.name + "' exceeds its deadline " + std::to_string(*rep.deadline);
          diags.Report(fd->getLocation(), errorId_) << msg;
          rep.errors.push_back(msg);
          rep.errorSites.push_back(siteOf("deadline", fd->getLocation(), msg));
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
  if (!certFuns_.empty())
    report.certificates.push_back(cert::programJson(
        ctx_.getSourceManager().getFileEntryRefForID(ctx_.getSourceManager().getMainFileID())
            ? std::string(ctx_.getSourceManager()
                              .getFileEntryRefForID(ctx_.getSourceManager().getMainFileID())
                              ->getName())
            : std::string("translation unit"),
        certNames_, certFuns_));
  return report;
}

}  // namespace

Report analyzeTranslationUnit(ASTContext& context, const Options& options) {
  Analyzer analyzer(context, options);
  return analyzer.run();
}

}  // namespace crosscheck
