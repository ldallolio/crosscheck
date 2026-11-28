// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
//
// Export of C functions as mini-C programs (`MiniC.MStmt` in the Lean formalization).
// See MiniC.hpp. This file is independent of the certificate generator on purpose: the
// checker compares its output with the program of the certificate (`MiniC.validate`).

#include "analysis/MiniC.hpp"

#include <clang/AST/ExprCXX.h>
#include <clang/AST/RecursiveASTVisitor.h>

#include <vector>

namespace crosscheck::minic {
namespace {

using namespace clang;

struct Refused {
  std::string why;
};

std::string num(std::int64_t v) { return std::to_string(v); }
std::string unum(std::uint64_t v) { return std::to_string(v); }

class Exporter {
 public:
  Exporter(ASTContext& ctx, const Inputs& in) : ctx_(ctx), in_(in) {}

  std::string function(const FunctionDecl* def) {
    const auto* body = dyn_cast_or_null<CompoundStmt>(def->getBody());
    if (!body) throw Refused{"no body"};
    checkVariables(def);
    std::string b = jlist(body);
    // The return flag; a function without a `return` inside a loop or `switch` has none,
    // and any index that no variable of the certificate uses serves.
    std::optional<std::size_t> r = optFlag("?return");
    return "{\"ret\":" + unum(r ? *r : (std::size_t{1} << 20)) + ",\"body\":" + b + "}";
  }

 private:
  ASTContext& ctx_;
  const Inputs& in_;

  // -- variables -----------------------------------------------------------------------

  std::optional<std::size_t> tracked(const VarDecl* v) const {
    auto it = in_.vars->find(v);
    if (it == in_.vars->end()) return std::nullopt;
    return it->second;
  }

  /// The tracked variables used by `def` are its own integer locals and parameters, are
  /// not volatile, static or unsigned, and their address is never taken (so that the
  /// assignments the exporter sees are the only writes).
  void checkVariables(const FunctionDecl* def) {
    struct V : RecursiveASTVisitor<V> {
      Exporter* ex;
      const FunctionDecl* def;
      std::string bad;
      bool VisitDeclRefExpr(DeclRefExpr* d) {
        const auto* v = dyn_cast<VarDecl>(d->getDecl());
        if (!v || !ex->tracked(v)) return true;
        // Globals are variables of the program certificate shared by every function: a
        // call runs the callee's certificate on them (so its writes are seen). What is
        // assumed is that no other code (an interrupt handler, another thread) writes
        // them while the function runs; `volatile` ones are refused below. Static locals
        // are globals visible in one function: their declaration runs once, before the
        // first call, and is exported as nothing (see `decl`).
        if (v->hasLocalStorage() && v->getDeclContext() != def) bad = "a tracked variable of another function";
        else if (v->getType().isVolatileQualified()) bad = "a volatile tracked variable";
        else if (!signedNonBool(v->getType()) && !ex->uwidth(v->getType()))
          bad = "a tracked variable that is neither a signed integer nor unsigned int or wider";
        else if (v->getType()->isReferenceType()) bad = "a reference";
        return true;
      }
      bool VisitUnaryOperator(UnaryOperator* u) {
        if (u->getOpcode() == UO_AddrOf)
          if (const auto* d = dyn_cast<DeclRefExpr>(u->getSubExpr()->IgnoreParens()))
            if (const auto* v = dyn_cast<VarDecl>(d->getDecl()); v && ex->tracked(v))
              bad = "the address of a tracked variable is taken";
        return true;
      }
      bool VisitLambdaExpr(LambdaExpr*) { bad = "a lambda"; return true; }
      bool VisitVarDecl(VarDecl* v) {
        if (v->getType()->isReferenceType()) bad = "a reference variable";
        return true;
      }
    } vis;
    vis.ex = this;
    vis.def = def;
    vis.TraverseStmt(def->getBody());
    if (!vis.bad.empty()) throw Refused{vis.bad};
  }

  static bool signedNonBool(QualType t) {
    return !t.isNull() && t->isIntegerType() && t->isSignedIntegerType() && !t->isBooleanType() &&
           !t->isEnumeralType();
  }

  /// The width of `t` if it is `unsigned int`, `unsigned long` or `unsigned long long`
  /// (the unsigned types that the integer promotions leave alone): the unsigned variables
  /// of the fragment.
  std::optional<unsigned> uwidth(QualType t) const {
    if (t.isNull()) return std::nullopt;
    const auto* bt = t.getCanonicalType()->getAs<BuiltinType>();
    if (!bt) return std::nullopt;
    switch (bt->getKind()) {
      case BuiltinType::UInt: case BuiltinType::ULong: case BuiltinType::ULongLong:
        return static_cast<unsigned>(ctx_.getIntWidth(t));
      default: return std::nullopt;
    }
  }
  /// The largest value the certificate's program lets an unsigned variable of this width
  /// receive from an affine expression: 2^width - 1, and 2^62 for 64 bits.
  static std::int64_t uhi(unsigned width) {
    return width >= 63 ? (std::int64_t{1} << 62) : ((std::int64_t{1} << width) - 1);
  }

  /// `t` is not changed by the integer promotions (so `x + 1` is computed in `x`'s type).
  bool unpromoted(QualType t) const { return !ctx_.isPromotableIntegerType(t); }

  /// Every value of `from` is a value of `to`.
  bool preserves(QualType from, QualType to) const {
    if (!from->isIntegerType() || !to->isIntegerType() || from->isBooleanType() ||
        to->isBooleanType())
      return false;
    unsigned wf = ctx_.getIntWidth(from), wt = ctx_.getIntWidth(to);
    bool sf = from->isSignedIntegerType(), st = to->isSignedIntegerType();
    if (sf == st) return wt >= wf;
    if (!sf && st) return wt > wf;  // unsigned into a wider signed type
    return false;                   // signed into unsigned: negative values change
  }

  // -- scans ---------------------------------------------------------------------------

  /// Calls, writes to tracked variables, jumps and statement expressions in `s`
  /// (unevaluated operands, e.g. of `sizeof`, are skipped).
  struct Effects {
    bool calls = false, writes = false;
    bool opaque = false;  ///< constructor calls, statement expressions, inline assembly
  };
  Effects effects(const Stmt* s) const {
    struct V : RecursiveASTVisitor<V> {
      const Exporter* ex;
      Effects e;
      bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr*) { return true; }
      bool VisitCallExpr(CallExpr*) { e.calls = true; return true; }
      bool VisitCXXConstructExpr(CXXConstructExpr*) { e.calls = e.opaque = true; return true; }
      bool VisitStmtExpr(StmtExpr*) { e.calls = e.opaque = true; return true; }
      bool VisitGCCAsmStmt(GCCAsmStmt*) { e.calls = e.opaque = true; return true; }
      void target(const Expr* t) {
        if (const auto* d = dyn_cast<DeclRefExpr>(t->IgnoreParenImpCasts()))
          if (const auto* v = dyn_cast<VarDecl>(d->getDecl()); v && ex->tracked(v)) e.writes = true;
      }
      bool VisitBinaryOperator(BinaryOperator* b) {
        if (b->isAssignmentOp()) target(b->getLHS());
        return true;
      }
      bool VisitUnaryOperator(UnaryOperator* u) {
        if (u->isIncrementDecrementOp()) target(u->getSubExpr());
        return true;
      }
    } vis;
    vis.ex = this;
    vis.TraverseStmt(const_cast<Stmt*>(s));
    return vis.e;
  }

  /// True while the calls of the expression being exported have been written as `call`
  /// statements before it: the expression's own value is then unknown where it uses them.
  mutable bool callsDone_ = false;
  void pure(const Expr* e, const char* what) const {
    Effects f = effects(e);
    if (f.calls && !(callsDone_ && !f.opaque)) throw Refused{std::string("a call in ") + what};
    if (f.writes) throw Refused{std::string("an assignment in ") + what};
  }

  /// A value that the generator describes by facts (`havocC`): `y >> k`, `y / c`,
  /// `y % c`, `y & m`, a read of a constant table. Not in the fragment yet: refused, so
  /// that the source is never less precise than the certificate's program.
  static bool describedByFacts(const Expr* e) {
    const Expr* x = e->IgnoreParenImpCasts();
    if (const auto* b = dyn_cast<BinaryOperator>(x)) {
      switch (b->getOpcode()) {
        case BO_Shr: case BO_Div: case BO_Rem: case BO_And: return true;
        default: return false;
      }
    }
    if (const auto* as = dyn_cast<ArraySubscriptExpr>(x)) {
      // an array variable of const elements (whose initialiser gives a range)
      const auto* d = dyn_cast<DeclRefExpr>(as->getBase()->IgnoreParenImpCasts());
      const auto* v = d ? dyn_cast<VarDecl>(d->getDecl()) : nullptr;
      if (!v) return false;
      const ArrayType* at = v->getType()->getAsArrayTypeUnsafe();
      return at && at->getElementType().isConstQualified();
    }
    return false;
  }

  // -- expressions ---------------------------------------------------------------------

  std::optional<std::int64_t> constant(const Expr* e) const {
    if (!e || e->isValueDependent() || !e->getType()->isIntegralOrEnumerationType() ||
        e->isGLValue() || e->HasSideEffects(ctx_))
      return std::nullopt;
    Expr::EvalResult r;
    if (!e->EvaluateAsInt(r, ctx_)) return std::nullopt;
    const llvm::APSInt& v = r.Val.getInt();
    if (v.isSigned() ? v.getSignificantBits() > 64 : v.getActiveBits() > 63) return std::nullopt;
    return v.isSigned() ? v.getSExtValue() : static_cast<std::int64_t>(v.getZExtValue());
  }

  static std::string other() { return "{\"e\":\"other\"}"; }

  /// The value of `e` as an integer of ℤ, exactly, or `other`.
  std::string exp(const Expr* e) const {
    if (std::optional<std::int64_t> k = constant(e)) return "{\"e\":\"lit\",\"k\":" + num(*k) + "}";
    e = e->IgnoreParens();
    if (const auto* ce = dyn_cast<ImplicitCastExpr>(e)) {
      CastKind k = ce->getCastKind();
      if (k == CK_LValueToRValue || k == CK_NoOp) return exp(ce->getSubExpr());
      if (k == CK_IntegralCast && preserves(ce->getSubExpr()->getType(), ce->getType()))
        return exp(ce->getSubExpr());
      return other();
    }
    if (const auto* d = dyn_cast<DeclRefExpr>(e)) {
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl()))
        if (std::optional<std::size_t> x = tracked(v)) return "{\"e\":\"var\",\"x\":" + unum(*x) + "}";
      return other();
    }
    // Arithmetic is exact in signed types only (unsigned arithmetic wraps).
    if (!signedNonBool(e->getType())) return other();
    if (const auto* u = dyn_cast<UnaryOperator>(e)) {
      if (u->getOpcode() == UO_Minus) return "{\"e\":\"neg\",\"a\":" + exp(u->getSubExpr()) + "}";
      if (u->getOpcode() == UO_Plus) return exp(u->getSubExpr());
      return other();
    }
    if (const auto* b = dyn_cast<BinaryOperator>(e)) {
      const char* op = nullptr;
      switch (b->getOpcode()) {
        case BO_Add: op = "add"; break;
        case BO_Sub: op = "sub"; break;
        case BO_Mul: op = "mul"; break;
        case BO_Shl: {
          // x << k in a signed type is x * 2^k (overflow is undefined behaviour)
          std::optional<std::int64_t> k = constant(b->getRHS());
          if (!k || *k < 0 || *k >= 62) return other();
          return "{\"e\":\"mul\",\"a\":" + exp(b->getLHS()) + ",\"b\":{\"e\":\"lit\",\"k\":" +
                 num(std::int64_t{1} << *k) + "}}";
        }
        default: return other();
      }
      return std::string("{\"e\":\"") + op + "\",\"a\":" + exp(b->getLHS()) + ",\"b\":" +
             exp(b->getRHS()) + "}";
    }
    return other();
  }

  /// The value of `e` modulo 2^width, as an expression over ℤ whose value is congruent to
  /// it: sums, differences, products and negations are computed in ℤ, which is correct
  /// modulo 2^width as long as no intermediate result is truncated to fewer than `width`
  /// bits (an unsigned type narrower than `width`, or a conversion to one). Signed
  /// subexpressions are exact (no overflow) and their conversion to unsigned is the
  /// reduction. Used only for a store into an unsigned variable (`assignU`), which keeps
  /// the value only if it lies in the variable's range.
  std::string expMod(const Expr* e, unsigned width) const {
    if (std::optional<std::int64_t> k = constant(e)) return "{\"e\":\"lit\",\"k\":" + num(*k) + "}";
    e = e->IgnoreParens();
    if (const auto* ce = dyn_cast<ImplicitCastExpr>(e)) {
      CastKind k = ce->getCastKind();
      QualType to = ce->getType(), from = ce->getSubExpr()->getType();
      if (k == CK_LValueToRValue || k == CK_NoOp) return expMod(ce->getSubExpr(), width);
      if (k == CK_IntegralCast && from->isIntegerType() && to->isIntegerType() && !from->isBooleanType() &&
          !to->isBooleanType() &&
          (preserves(from, to) || (to->isUnsignedIntegerType() && ctx_.getIntWidth(to) >= width)))
        return expMod(ce->getSubExpr(), width);
      return other();
    }
    if (const auto* d = dyn_cast<DeclRefExpr>(e)) {
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl()))
        if (std::optional<std::size_t> x = tracked(v)) return "{\"e\":\"var\",\"x\":" + unum(*x) + "}";
      return other();
    }
    QualType t = e->getType();
    if (!t->isIntegerType() || t->isBooleanType() || t->isEnumeralType()) return other();
    if (t->isUnsignedIntegerType() && ctx_.getIntWidth(t) < width) return other();
    if (const auto* u = dyn_cast<UnaryOperator>(e)) {
      if (u->getOpcode() == UO_Minus) return "{\"e\":\"neg\",\"a\":" + expMod(u->getSubExpr(), width) + "}";
      if (u->getOpcode() == UO_Plus) return expMod(u->getSubExpr(), width);
      return other();
    }
    if (const auto* b = dyn_cast<BinaryOperator>(e)) {
      if (b->getOpcode() == BO_Shl) {
        // x << k is x * 2^k modulo the width of its type (k below that width, else undefined)
        std::optional<std::int64_t> k = constant(b->getRHS());
        if (!k || *k < 0 || *k >= 62 || *k >= static_cast<std::int64_t>(ctx_.getIntWidth(t))) return other();
        return "{\"e\":\"mul\",\"a\":" + expMod(b->getLHS(), width) + ",\"b\":{\"e\":\"lit\",\"k\":" +
               num(std::int64_t{1} << *k) + "}}";
      }
      const char* op = b->getOpcode() == BO_Add ? "add" : b->getOpcode() == BO_Sub ? "sub" : b->getOpcode() == BO_Mul ? "mul" : nullptr;
      if (!op) return other();
      return std::string("{\"e\":\"") + op + "\",\"a\":" + expMod(b->getLHS(), width) + ",\"b\":" +
             expMod(b->getRHS(), width) + "}";
    }
    return other();
  }

  /// A test, as the truth of a comparison, its negation, or `other`.
  std::string cond(const Expr* e) const {
    e = e->IgnoreParenImpCasts();
    if (const auto* u = dyn_cast<UnaryOperator>(e); u && u->getOpcode() == UO_LNot)
      return "{\"c\":\"not\",\"a\":" + cond(u->getSubExpr()) + "}";
    if (const auto* b = dyn_cast<BinaryOperator>(e)) {
      const char* op = nullptr;
      switch (b->getOpcode()) {
        case BO_LT: op = "<"; break;
        case BO_LE: op = "<="; break;
        case BO_GT: op = ">"; break;
        case BO_GE: op = ">="; break;
        default: break;
      }
      if (op)
        return std::string("{\"c\":\"cmp\",\"op\":\"") + op + "\",\"a\":" + exp(b->getLHS()) +
               ",\"b\":" + exp(b->getRHS()) + "}";
    }
    return "{\"c\":\"other\"}";
  }

  /// A loop test as a conjunction (`&&`); a constant conjunct is dropped if true and is
  /// `1 <= 0` if false.
  void conjuncts(const Expr* e, std::vector<std::string>& out) const {
    if (std::optional<std::int64_t> k = constant(e)) {
      if (*k == 0)
        out.push_back("{\"c\":\"cmp\",\"op\":\"<=\",\"a\":{\"e\":\"lit\",\"k\":1},\"b\":{\"e\":\"lit\",\"k\":0}}");
      return;
    }
    const Expr* x = e->IgnoreParenImpCasts();
    if (const auto* b = dyn_cast<BinaryOperator>(x); b && b->getOpcode() == BO_LAnd) {
      conjuncts(b->getLHS(), out);
      conjuncts(b->getRHS(), out);
      return;
    }
    out.push_back(cond(e));
  }

  // -- statements ----------------------------------------------------------------------

  static std::string skip() { return "{\"s\":\"skip\"}"; }
  static std::string cost(std::uint64_t w) { return "{\"s\":\"cost\",\"w\":" + unum(w) + "}"; }
  static std::string assign(std::uint64_t w, std::size_t x, const std::string& e) {
    return "{\"s\":\"assign\",\"w\":" + unum(w) + ",\"x\":" + unum(x) + ",\"e\":" + e + "}";
  }
  /// `x = y OP c` for OP in `/`, `>>`, `%`, `&` and a constant `c` (Lean `divStore`): a
  /// value described by facts. No value: not of a form the fragment models exactly, the
  /// caller refuses. The conditions are checked here, on the C types:
  /// - `c >= 0`; a divisor is positive; a shift count is below 62 (it becomes a quotient);
  /// - the result of the operation, of type `rt`, is stored into `x` without change of
  ///   value (`preserves(rt, xt)`): the facts are about the result, not about a converted
  ///   value;
  /// - the operand `y` is a value the fragment gives exactly (`exp`), else `x` is unknown.
  /// The facts for a quotient or a remainder are stated for `y >= 0` only, so conversions
  /// of a negative `y` to an unsigned computation type do not matter.
  std::optional<std::string> divStore(std::uint64_t w, std::size_t x, QualType xt, const Expr* y,
                                      BinaryOperatorKind op, const Expr* rhs, QualType rt) const {
    std::optional<std::int64_t> c = constant(rhs);
    if (op == BO_And && !c) {  // the mask may be on the left
      std::swap(y, rhs);
      c = constant(rhs);
    }
    if (!c || *c < 0 || !preserves(rt, xt)) return std::nullopt;
    const char* name = nullptr;
    std::int64_t k = *c;
    switch (op) {
      case BO_Div: name = "div"; if (k < 1) return std::nullopt; break;
      case BO_Rem: name = "rem"; if (k < 1) return std::nullopt; break;
      case BO_Shr: name = "div"; if (k >= 62) return std::nullopt; k = std::int64_t{1} << k; break;
      case BO_And: name = "and"; break;
      default: return std::nullopt;
    }
    std::string ys = exp(y);
    if (ys.find("\"other\"") != std::string::npos) return assign(w, x, other());
    std::string s = std::string("{\"s\":\"div\",\"w\":") + unum(w) + ",\"x\":" + unum(x) + ",\"op\":\"" +
                    name + "\",\"y\":" + ys + ",\"c\":" + num(k);
    if (ys.find("{\"e\":\"var\",\"x\":" + unum(x) + "}") != std::string::npos) {
      // y mentions x: its old value goes to a scratch variable first.
      auto sc = in_.scratch.find(y);
      if (sc == in_.scratch.end()) throw Refused{"a division of a variable by a constant, stored in itself, without a scratch variable"};
      std::size_t t = sc->second;
      for (const auto& [v, i] : *in_.vars)
        if (i == t) throw Refused{"internal: a scratch variable that is a variable of the source"};
      if (t < 2) throw Refused{"internal: a scratch variable that is reserved"};
      s += ",\"old\":" + unum(t);
    }
    return s + "}";
  }
  /// The operation and operands if `e` is `y OP c` with OP in `/`, `>>`, `%`, `&`.
  const BinaryOperator* divisionLike(const Expr* e) const {
    if (constant(e)) return nullptr;  // a constant expression is its value
    const auto* b = dyn_cast<BinaryOperator>(e->IgnoreParenImpCasts());
    if (!b) return nullptr;
    switch (b->getOpcode()) {
      case BO_Shr: case BO_Div: case BO_Rem: case BO_And: return b;
      default: return nullptr;
    }
  }
  /// A store into an unsigned variable of `width` bits (Lean `assignU`).
  static std::string assignU(std::uint64_t w, std::size_t x, unsigned width, const std::string& e) {
    return "{\"s\":\"assignU\",\"w\":" + unum(w) + ",\"x\":" + unum(x) + ",\"hi\":" + num(uhi(width)) +
           ",\"e\":" + e + "}";
  }
  static std::string seq(const std::vector<std::string>& ss) {
    std::string s = "{\"s\":\"seq\",\"ss\":[";
    for (std::size_t i = 0; i < ss.size(); ++i) s += (i ? "," : "") + ss[i];
    return s + "]}";
  }

  std::string ret(const ReturnStmt* rs) const {
    const Expr* v = rs->getRetValue();
    std::string c = cost((v ? in_.costOf(v) : 0) + in_.ret);
    if (!v) return c;
    Effects f = effects(v);
    if (f.calls && !f.opaque && !f.writes) {  // the calls first, then the return
      std::vector<std::string> ss;
      callStmts(v, ss);
      ss.push_back(c);
      return seq(ss);
    }
    pure(v, "a return value");
    return c;
  }

  static std::vector<const Stmt*> flatten(const Stmt* s) {
    if (!s) return {};
    if (const auto* cs = dyn_cast<CompoundStmt>(s)) return {cs->body_begin(), cs->body_end()};
    return {s};
  }

  // -- statements with jumps (Lean `MiniC.JStmt`) -------------------------------------
  //
  // `break`, `continue`, `return` and `switch` are written as they are in C: their
  // meaning is given in Lean (`MiniC.JExec`), and their elimination with flag variables
  // is done by the checker (`MiniC.elim`, proved: `MiniC.validatedJ_sound`). The exporter
  // only names the flag variables of the certificate (found by name: `?break<d>`,
  // `?continue<d>` for a loop at nesting depth `d`, `?case<s>` for a `switch` at
  // `switch` nesting depth `s`, `?return`); the checker refuses flags that are variables
  // of the source or that are not fresh along a nesting path.

  std::size_t loopDepth_ = 0, switchDepth_ = 0;

  std::optional<std::size_t> optFlag(const std::string& name) const {
    std::optional<std::size_t> f = in_.flag ? in_.flag(name) : std::nullopt;
    if (!f) return std::nullopt;
    for (const auto& [v, i] : *in_.vars)
      if (i == *f) throw Refused{"internal: a flag variable that is a variable of the source"};
    return f;
  }

  static std::string jbasic(const std::string& s) { return "{\"j\":\"basic\",\"s\":" + s + "}"; }
  static std::string jseq(const std::vector<std::string>& js) {
    std::string s = "{\"j\":\"seq\",\"js\":[";
    for (std::size_t i = 0; i < js.size(); ++i) s += (i ? "," : "") + js[i];
    return s + "]}";
  }

  std::string jlist(const Stmt* s) {
    std::vector<std::string> js;
    for (const Stmt* c : flatten(s)) js.push_back(jstmt(c));
    return jseq(js);
  }

  /// A `switch`: the cost of the test and the case groups (the statements from one label
  /// to the next); statements before the first label are not reachable. Labels inside
  /// nested statements are refused.
  std::string switchStmt(const SwitchStmt* ss) {
    if (ss->getInit() || ss->getConditionVariable())
      throw Refused{"switch with an initialiser or a condition variable"};
    pure(ss->getCond(), "a test");
    const auto* body = dyn_cast<CompoundStmt>(ss->getBody());
    if (!body) throw Refused{"switch without a block"};
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
        if (cs.nested) throw Refused{"a case label inside a nested statement"};
      }
    std::optional<std::size_t> sc = optFlag("?case" + std::to_string(switchDepth_));
    if (!sc) throw Refused{"a switch without its variable in the certificate (?case" +
                           std::to_string(switchDepth_) + ")"};
    ++switchDepth_;
    std::string gs;
    try {
      for (std::size_t i = 0; i < groups.size(); ++i) {
        std::vector<std::string> js;
        for (const Stmt* st : groups[i]) js.push_back(jstmt(st));
        gs += (i ? "," : "") + jseq(js);
      }
    } catch (...) {
      --switchDepth_;
      throw;
    }
    --switchDepth_;
    return "{\"j\":\"switch\",\"w\":" + unum(in_.costOf(ss->getCond()) + in_.branch) + ",\"sc\":" +
           unum(*sc) + ",\"groups\":[" + gs + "]}";
  }

  /// A `while` or `for` loop: `init; while (test) { body; inc }`, with the flags of its
  /// jumps if the certificate has them. A loop without a test is `while` with no conjunct.
  std::string loop(const Stmt* init, const Expr* test, const Expr* inc, const Stmt* body) {
    if (test) pure(test, "a loop test");
    std::string d = std::to_string(loopDepth_);
    std::optional<std::size_t> fb = optFlag("?break" + d), fc = optFlag("?continue" + d);
    std::string u = inc ? effect(inc, in_.costOf(inc)) : std::string();
    ++loopDepth_;
    std::string bd;
    try {
      bd = jlist(body);
    } catch (...) {
      --loopDepth_;
      throw;
    }
    --loopDepth_;
    std::string l = "{\"j\":\"loop\"," + loopTest(test) + ",\"body\":" + bd;
    if (inc) l += ",\"inc\":" + u;
    if (fb) l += ",\"fb\":" + unum(*fb);
    if (fc) l += ",\"fc\":" + unum(*fc);
    l += "}";
    if (!init) return l;
    return jseq({jbasic(stmt(init)), l});
  }

  void checkIf(const IfStmt* is) const {
    if (is->getInit() || is->getConditionVariable() || is->isConsteval() || is->isConstexpr())
      throw Refused{"if with an initialiser, a condition variable or constexpr"};
    pure(is->getCond(), "a test");
  }

  /// A statement, with jumps.
  std::string jstmt(const Stmt* st) {
    if (isa<CompoundStmt>(st)) return jlist(st);
    if (isa<BreakStmt>(st)) return "{\"j\":\"break\",\"w\":" + unum(in_.branch) + "}";
    if (isa<ContinueStmt>(st)) return "{\"j\":\"continue\",\"w\":" + unum(in_.branch) + "}";
    if (const auto* rs = dyn_cast<ReturnStmt>(st)) return "{\"j\":\"return\",\"s\":" + ret(rs) + "}";
    if (const auto* is = dyn_cast<IfStmt>(st)) {
      checkIf(is);
      return "{\"j\":\"if\",\"w\":" + unum(in_.costOf(is->getCond()) + in_.branch) + ",\"c\":" +
             cond(is->getCond()) + ",\"a\":" + jlist(is->getThen()) + ",\"b\":" + jlist(is->getElse()) + "}";
    }
    if (const auto* ws = dyn_cast<WhileStmt>(st)) {
      if (ws->getConditionVariable()) throw Refused{"condition variable"};
      return loop(nullptr, ws->getCond(), nullptr, ws->getBody());
    }
    if (const auto* fs = dyn_cast<ForStmt>(st)) {
      if (fs->getConditionVariable()) throw Refused{"condition variable"};
      return loop(fs->getInit(), fs->getCond(), fs->getInc(), fs->getBody());
    }
    if (const auto* dw = dyn_cast<DoStmt>(st)) {
      // `do { body } while (test)` (Lean `JStmt.doLoop`); the checker accepts it when the
      // body has no `break` or `continue` of its own.
      pure(dw->getCond(), "a loop test");
      std::string d = std::to_string(loopDepth_);
      std::optional<std::size_t> fb = optFlag("?break" + d), fc = optFlag("?continue" + d);
      ++loopDepth_;
      std::string bd;
      try {
        bd = jlist(dw->getBody());
      } catch (...) {
        --loopDepth_;
        throw;
      }
      --loopDepth_;
      std::string l = "{\"j\":\"do\"," + loopTest(dw->getCond()) + ",\"body\":" + bd;
      if (fb) l += ",\"fb\":" + unum(*fb);
      if (fc) l += ",\"fc\":" + unum(*fc);
      return l + "}";
    }
    if (const auto* sw = dyn_cast<SwitchStmt>(st)) return switchStmt(sw);
    if (const auto* as = dyn_cast<AttributedStmt>(st)) return jstmt(as->getSubStmt());
    return jbasic(stmt(st));
  }

  std::optional<std::size_t> targetOf(const Expr* t) const {
    if (const auto* d = dyn_cast<DeclRefExpr>(t->IgnoreParens()))
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl())) return tracked(v);
    return std::nullopt;
  }

  /// An expression evaluated for its effect, of weight `w`.
  /// The calls of `e` that are not inside another call, in source order, each as a
  /// `call` statement (Lean `MStmt.call`) preceded by those of its arguments: the
  /// arguments are stored into the variables of the callee's tracked integer parameters,
  /// exactly (`exp`, or `expMod` for an unsigned parameter) or as unknown values.
  void callStmts(const Expr* e, std::vector<std::string>& out) const {
    struct OC : RecursiveASTVisitor<OC> {
      std::vector<const CallExpr*> calls;
      bool TraverseCallExpr(CallExpr* c) { calls.push_back(c); return true; }
      bool TraverseCXXMemberCallExpr(CXXMemberCallExpr* c) { calls.push_back(c); return true; }
      bool TraverseCXXOperatorCallExpr(CXXOperatorCallExpr* c) { calls.push_back(c); return true; }
      bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr*) { return true; }
      bool TraverseLambdaExpr(LambdaExpr*) { return true; }
    } oc;
    oc.TraverseStmt(const_cast<Expr*>(e));
    for (const CallExpr* c : oc.calls) {
      const FunctionDecl* fd = c->getDirectCallee();
      if (!fd) throw Refused{"an indirect call"};
      if (isa<CXXMemberCallExpr>(c) || isa<CXXOperatorCallExpr>(c)) throw Refused{"a call of a member function"};
      std::optional<CalleeInfo> ci = in_.callee ? in_.callee(fd) : std::nullopt;
      if (!ci) throw Refused{"a call of a function without an entry in the certificate file"};
      if (!ci->plain) throw Refused{"a call of a function whose summary has more logical variables than parameters"};
      for (const Expr* a : c->arguments()) {
        Effects f = effects(a);
        if (f.writes) throw Refused{"an assignment in an argument"};
        if (f.opaque) throw Refused{"a call"};
        if (f.calls) callStmts(a, out);
      }
      std::string s = "{\"s\":\"call\",\"f\":" + unum(ci->index) + ",\"args\":[";
      bool first = true;
      for (const auto& [p, x] : ci->params) {
        unsigned i = p->getFunctionScopeIndex();
        if (i >= c->getNumArgs()) throw Refused{"a call with fewer arguments than parameters"};
        const Expr* a = c->getArg(i);
        QualType pt = p->getType();
        s += first ? "" : ",";
        first = false;
        s += "{\"x\":" + unum(x);
        if (std::optional<unsigned> uw = uwidth(pt))
          s += ",\"hi\":" + num(uhi(*uw)) + ",\"e\":" + expMod(a, *uw) + "}";
        else if (signedNonBool(pt) && preserves(a->getType(), pt))
          s += ",\"e\":" + exp(a) + "}";
        else
          s += ",\"e\":" + other() + "}";
      }
      out.push_back(s + "]}");
    }
  }

  std::string effect(const Expr* e, std::uint64_t w) {
    const Expr* x = e->IgnoreParenImpCasts();
    if (const auto* co = dyn_cast<BinaryOperator>(x); co && co->getOpcode() == BO_Comma)
      return seq({effect(co->getLHS(), in_.costOf(co->getLHS())),
                  effect(co->getRHS(), in_.costOf(co->getRHS()))});
    Effects f = effects(e);
    if (f.opaque) throw Refused{"a call"};
    if (f.calls) {
      // The calls first, then the expression itself, whose value is unknown where it
      // uses their results; its weight (the cost model's, calls included) is unchanged.
      std::vector<std::string> ss;
      callStmts(e, ss);
      callsDone_ = true;
      try {
        ss.push_back(effectOf(e, x, f, w));
      } catch (...) {
        callsDone_ = false;
        throw;
      }
      callsDone_ = false;
      return seq(ss);
    }
    return effectOf(e, x, f, w);
  }

  std::string effectOf(const Expr* /*e*/, const Expr* x, const Effects& f, std::uint64_t w) {
    if (!f.writes) return cost(w);  // stores to memory or untracked variables only
    if (const auto* b = dyn_cast<BinaryOperator>(x); b && b->isAssignmentOp()) {
      std::optional<std::size_t> t = targetOf(b->getLHS());
      if (!t) throw Refused{"an assignment inside an expression"};
      pure(b->getRHS(), "the right-hand side of an assignment");
      QualType xt = b->getLHS()->getType();
      if (b->getOpcode() == BO_Assign) {
        if (const BinaryOperator* d = divisionLike(b->getRHS())) {
          if (auto s = divStore(w, *t, xt, d->getLHS(), d->getOpcode(), d->getRHS(), d->getType())) return *s;
          throw Refused{"a division, shift, remainder or mask outside the forms of the fragment"};
        }
        if (describedByFacts(b->getRHS())) throw Refused{"a table read (not in the fragment yet)"};
        if (std::optional<unsigned> uw = uwidth(xt)) return assignU(w, *t, *uw, expMod(b->getRHS(), *uw));
        return assign(w, *t, exp(b->getRHS()));
      }
      switch (b->getOpcode()) {
        case BO_DivAssign: case BO_RemAssign: case BO_ShrAssign: case BO_AndAssign: {
          // x op= c is x = (T) (x op c): the result type of the operation is the
          // computation result type.
          const auto* cao = cast<CompoundAssignOperator>(b);
          BinaryOperatorKind op = b->getOpcode() == BO_DivAssign   ? BO_Div
                                  : b->getOpcode() == BO_RemAssign ? BO_Rem
                                  : b->getOpcode() == BO_ShrAssign ? BO_Shr
                                                                   : BO_And;
          if (auto s = divStore(w, *t, xt, b->getLHS(), op, b->getRHS(), cao->getComputationResultType()))
            return *s;
          throw Refused{"a division, shift, remainder or mask outside the forms of the fragment"};
        }
        default: break;
      }
      if (std::optional<unsigned> uw = uwidth(xt)) {
        // An unsigned x: x op= e is (x op e) modulo 2^width when the computation is not
        // done in a narrower type; the store keeps the value only if it is in range.
        const auto* cu = cast<CompoundAssignOperator>(b);
        QualType ct = cu->getComputationResultType();
        std::string self = "{\"e\":\"var\",\"x\":" + unum(*t) + "}";
        bool wide = ct->isIntegerType() && !ct->isBooleanType() &&
                    (ct->isUnsignedIntegerType() ? ctx_.getIntWidth(ct) >= *uw : preserves(xt, ct));
        const char* op = b->getOpcode() == BO_AddAssign   ? "add"
                         : b->getOpcode() == BO_SubAssign ? "sub"
                         : b->getOpcode() == BO_MulAssign ? "mul"
                                                          : nullptr;
        if (wide && b->getOpcode() == BO_ShlAssign) {
          std::optional<std::int64_t> k = constant(b->getRHS());
          if (k && *k >= 0 && *k < 62 && *k < static_cast<std::int64_t>(ctx_.getIntWidth(ct)))
            return assignU(w, *t, *uw, "{\"e\":\"mul\",\"a\":" + self + ",\"b\":{\"e\":\"lit\",\"k\":" +
                                          num(std::int64_t{1} << *k) + "}}");
        }
        if (!wide || !op) return assign(w, *t, other());
        return assignU(w, *t, *uw, std::string("{\"e\":\"") + op + "\",\"a\":" + self + ",\"b\":" +
                                      expMod(b->getRHS(), *uw) + "}");
      }
      const auto* ca = cast<CompoundAssignOperator>(b);
      // x op= e is x = (T) (x op e), computed in the computation type: exact only if
      // that type is signed and converting back to x's type preserves values.
      QualType ct = ca->getComputationResultType();
      bool exact = signedNonBool(ct) && preserves(ct, xt) &&
                   (b->getOpcode() == BO_AddAssign || b->getOpcode() == BO_SubAssign ||
                    b->getOpcode() == BO_MulAssign || b->getOpcode() == BO_ShlAssign);
      if (!exact) return assign(w, *t, other());
      std::string self = "{\"e\":\"var\",\"x\":" + unum(*t) + "}";
      if (b->getOpcode() == BO_MulAssign)
        return assign(w, *t, "{\"e\":\"mul\",\"a\":" + self + ",\"b\":" + exp(b->getRHS()) + "}");
      if (b->getOpcode() == BO_ShlAssign) {
        std::optional<std::int64_t> k = constant(b->getRHS());
        if (!k || *k < 0 || *k >= 62) return assign(w, *t, other());
        return assign(w, *t, "{\"e\":\"mul\",\"a\":" + self + ",\"b\":{\"e\":\"lit\",\"k\":" +
                                 num(std::int64_t{1} << *k) + "}}");
      }
      return assign(w, *t, std::string("{\"e\":\"") + (b->getOpcode() == BO_AddAssign ? "add" : "sub") +
                               "\",\"a\":" + self + ",\"b\":" + exp(b->getRHS()) + "}");
    }
    if (const auto* u = dyn_cast<UnaryOperator>(x); u && u->isIncrementDecrementOp()) {
      std::optional<std::size_t> t = targetOf(u->getSubExpr());
      if (!t) throw Refused{"an assignment inside an expression"};
      QualType xt = u->getSubExpr()->getType();
      if (!unpromoted(xt)) return assign(w, *t, other());  // x + 1 converted back: may wrap
      std::string self = "{\"e\":\"var\",\"x\":" + unum(*t) + "}";
      if (std::optional<unsigned> uw = uwidth(xt))
        return assignU(w, *t, *uw, std::string("{\"e\":\"") + (u->isIncrementOp() ? "add" : "sub") +
                                      "\",\"a\":" + self + ",\"b\":{\"e\":\"lit\",\"k\":1}}");
      return assign(w, *t, std::string("{\"e\":\"") + (u->isIncrementOp() ? "add" : "sub") + "\",\"a\":" +
                               self + ",\"b\":{\"e\":\"lit\",\"k\":1}}");
    }
    throw Refused{"an assignment inside an expression"};
  }

  std::string decl(const DeclStmt* ds) {
    std::vector<std::string> ss;
    for (const Decl* d : ds->decls()) {
      const auto* vd = dyn_cast<VarDecl>(d);
      if (!vd) continue;
      // A static local is initialised once, before the first call: its declaration does
      // nothing at a call (a dynamic C++ initialiser, run at the first call, is refused).
      if (vd->isStaticLocal()) {
        if (vd->getInit() && !vd->getInit()->isConstantInitializer(ctx_, false))
          throw Refused{"a static local variable with a dynamic initialiser"};
        continue;
      }
      const Expr* init = vd->getInit();
      bool withCalls = false;
      if (init) {
        Effects f = effects(init);
        if (f.calls && !f.opaque && !f.writes) {  // the calls first (Lean `MStmt.call`)
          callStmts(init, ss);
          withCalls = true;
        } else {
          pure(init, "an initialiser");
        }
      }
      (void)withCalls;
      std::uint64_t w = (init ? in_.costOf(init) : 0) +
                        (init && vd->getType()->isIntegralOrEnumerationType() ? in_.assign : 0);
      if (std::optional<std::size_t> x = tracked(vd)) {
        if (const BinaryOperator* d = init ? divisionLike(init) : nullptr) {
          auto s = divStore(w, *x, vd->getType(), d->getLHS(), d->getOpcode(), d->getRHS(), d->getType());
          if (!s) throw Refused{"a division, shift, remainder or mask outside the forms of the fragment"};
          ss.push_back(*s);
          continue;
        }
        if (init && describedByFacts(init)) throw Refused{"a table read (not in the fragment yet)"};
        if (std::optional<unsigned> uw = init ? uwidth(vd->getType()) : std::nullopt)
          ss.push_back(assignU(w, *x, *uw, expMod(init, *uw)));
        else
          ss.push_back(assign(w, *x, init ? exp(init) : other()));
      }
      else
        ss.push_back(cost(w));
    }
    return seq(ss);
  }

  /// A statement without jumps (declarations, expressions), as `MStmt`.
  std::string stmt(const Stmt* st) {
    if (isa<NullStmt>(st)) return skip();
    if (const auto* ds = dyn_cast<DeclStmt>(st)) return decl(ds);
    if (const auto* e = dyn_cast<Expr>(st)) {
      if (in_.isRequire && in_.isRequire(e)) return skip();
      if (in_.isTrusted && in_.isTrusted(e)) throw Refused{"a trusted annotation (CROSSCHECK_ASSUME, CROSSCHECK_LOOP_BOUND)"};
      return effect(e, in_.costOf(e));
    }
    if (const auto* as = dyn_cast<AttributedStmt>(st)) return stmt(as->getSubStmt());
    throw Refused{std::string("statement not in the fragment (") + st->getStmtClassName() + ")"};
  }

  /// The weight and the conjuncts of a loop test (a constant false conjunct is `1 <= 0`).
  std::string loopTest(const Expr* c) const {
    std::vector<std::string> cs;
    if (c) conjuncts(c, cs);
    // Mini-C gives no meaning to a loop whose test has an unknown part (Lean `lower`
    // returns none): refuse, so that no source is written for the function.
    for (const std::string& x : cs)
      if (x.find("\"other\"") != std::string::npos)
        throw Refused{"a loop test that is not a conjunction of comparisons of tracked values"};
    std::string s = "\"w\":" + unum(c ? in_.costOf(c) + in_.branch : 0) + ",\"cs\":[";
    for (std::size_t i = 0; i < cs.size(); ++i) s += (i ? "," : "") + cs[i];
    return s + "]";
  }
};

}  // namespace

Result exportFunction(const FunctionDecl* def, ASTContext& ctx, const Inputs& in) {
  Result r;
  try {
    Exporter ex(ctx, in);
    r.json = ex.function(def);
  } catch (const Refused& e) {
    r.reason = e.why;
  }
  return r;
}

}  // namespace crosscheck::minic
