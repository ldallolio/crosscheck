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
    return block(std::vector<const Stmt*>(body->body_begin(), body->body_end()));
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
        if (!v->hasLocalStorage() || v->getDeclContext() != def) bad = "a tracked global or static variable";
        else if (v->getType().isVolatileQualified()) bad = "a volatile tracked variable";
        else if (!signedNonBool(v->getType())) bad = "a tracked variable that is not a signed integer";
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
        if (v->isStaticLocal()) bad = "a static local variable";
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
  };
  Effects effects(const Stmt* s) const {
    struct V : RecursiveASTVisitor<V> {
      const Exporter* ex;
      Effects e;
      bool TraverseUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr*) { return true; }
      bool VisitCallExpr(CallExpr*) { e.calls = true; return true; }
      bool VisitCXXConstructExpr(CXXConstructExpr*) { e.calls = true; return true; }
      bool VisitStmtExpr(StmtExpr*) { e.calls = true; return true; }
      bool VisitGCCAsmStmt(GCCAsmStmt*) { e.calls = true; return true; }
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

  void pure(const Expr* e, const char* what) const {
    Effects f = effects(e);
    if (f.calls) throw Refused{std::string("a call in ") + what};
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
  static std::string seq(const std::vector<std::string>& ss) {
    std::string s = "{\"s\":\"seq\",\"ss\":[";
    for (std::size_t i = 0; i < ss.size(); ++i) s += (i ? "," : "") + ss[i];
    return s + "]}";
  }

  std::string ret(const ReturnStmt* rs) const {
    const Expr* v = rs->getRetValue();
    if (v) pure(v, "a return value");
    return cost((v ? in_.costOf(v) : 0) + in_.ret);
  }

  static bool hasReturn(const Stmt* s) {
    if (!s) return false;
    if (isa<ReturnStmt>(s)) return true;
    for (const Stmt* c : s->children())
      if (hasReturn(c)) return true;
    return false;
  }

  static std::vector<const Stmt*> flatten(const Stmt* s) {
    if (!s) return {};
    if (const auto* cs = dyn_cast<CompoundStmt>(s)) return {cs->body_begin(), cs->body_end()};
    return {s};
  }

  /// A statement list of the function's body, outside loops. `return` ends the
  /// function: what follows it is not run; a conditional or block that contains a
  /// `return` takes the rest of the list into its branches.
  std::string block(const std::vector<const Stmt*>& l, std::size_t from = 0) {
    if (from >= l.size()) return skip();
    const Stmt* st = l[from];
    if (const auto* rs = dyn_cast<ReturnStmt>(st)) return ret(rs);
    std::vector<const Stmt*> rest(l.begin() + static_cast<std::ptrdiff_t>(from) + 1, l.end());
    if (hasReturn(st)) {
      if (const auto* cs = dyn_cast<CompoundStmt>(st)) {
        std::vector<const Stmt*> m(cs->body_begin(), cs->body_end());
        m.insert(m.end(), rest.begin(), rest.end());
        return block(m);
      }
      if (const auto* as = dyn_cast<AttributedStmt>(st)) {
        std::vector<const Stmt*> m{as->getSubStmt()};
        m.insert(m.end(), rest.begin(), rest.end());
        return block(m);
      }
      if (const auto* is = dyn_cast<IfStmt>(st)) {
        std::vector<const Stmt*> t = flatten(is->getThen()), e = flatten(is->getElse());
        t.insert(t.end(), rest.begin(), rest.end());
        e.insert(e.end(), rest.begin(), rest.end());
        return ifStmt(is, block(t), block(e));
      }
      throw Refused{"a return inside a loop or a switch"};
    }
    return seq({stmt(st), block(l, from + 1)});
  }

  /// A statement list inside a loop (no `return`).
  std::string list(const Stmt* s) {
    if (!s) return skip();
    if (hasReturn(s)) throw Refused{"a return inside a loop"};
    std::vector<std::string> ss;
    for (const Stmt* t : flatten(s)) ss.push_back(stmt(t));
    return seq(ss);
  }

  std::string ifStmt(const IfStmt* is, const std::string& a, const std::string& b) {
    if (is->getInit() || is->getConditionVariable() || is->isConsteval() || is->isConstexpr())
      throw Refused{"if with an initialiser, a condition variable or constexpr"};
    pure(is->getCond(), "a test");
    return "{\"s\":\"if\",\"w\":" + unum(in_.costOf(is->getCond()) + in_.branch) +
           ",\"c\":" + cond(is->getCond()) + ",\"a\":" + a + ",\"b\":" + b + "}";
  }

  std::optional<std::size_t> targetOf(const Expr* t) const {
    if (const auto* d = dyn_cast<DeclRefExpr>(t->IgnoreParens()))
      if (const auto* v = dyn_cast<VarDecl>(d->getDecl())) return tracked(v);
    return std::nullopt;
  }

  /// An expression evaluated for its effect, of weight `w`.
  std::string effect(const Expr* e, std::uint64_t w) {
    const Expr* x = e->IgnoreParenImpCasts();
    if (const auto* co = dyn_cast<BinaryOperator>(x); co && co->getOpcode() == BO_Comma)
      return seq({effect(co->getLHS(), in_.costOf(co->getLHS())),
                  effect(co->getRHS(), in_.costOf(co->getRHS()))});
    Effects f = effects(e);
    if (f.calls) throw Refused{"a call"};
    if (!f.writes) return cost(w);  // stores to memory or untracked variables only
    if (const auto* b = dyn_cast<BinaryOperator>(x); b && b->isAssignmentOp()) {
      std::optional<std::size_t> t = targetOf(b->getLHS());
      if (!t) throw Refused{"an assignment inside an expression"};
      pure(b->getRHS(), "the right-hand side of an assignment");
      QualType xt = b->getLHS()->getType();
      if (b->getOpcode() == BO_Assign) {
        if (describedByFacts(b->getRHS())) throw Refused{"a division, shift, remainder, mask or table read (not in the fragment yet)"};
        return assign(w, *t, exp(b->getRHS()));
      }
      switch (b->getOpcode()) {
        case BO_DivAssign: case BO_RemAssign: case BO_ShrAssign: case BO_AndAssign:
          throw Refused{"a division, shift, remainder or mask (not in the fragment yet)"};
        default: break;
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
      const Expr* init = vd->getInit();
      if (init) pure(init, "an initialiser");
      std::uint64_t w = (init ? in_.costOf(init) : 0) +
                        (init && vd->getType()->isIntegralOrEnumerationType() ? in_.assign : 0);
      if (std::optional<std::size_t> x = tracked(vd)) {
        if (init && describedByFacts(init))
          throw Refused{"a division, shift, remainder, mask or table read (not in the fragment yet)"};
        ss.push_back(assign(w, *x, init ? exp(init) : other()));
      }
      else
        ss.push_back(cost(w));
    }
    return seq(ss);
  }

  std::string stmt(const Stmt* st) {
    if (const auto* cs = dyn_cast<CompoundStmt>(st)) return list(cs);
    if (isa<ReturnStmt>(st)) throw Refused{"a return inside a loop"};
    if (isa<NullStmt>(st)) return skip();
    if (const auto* ds = dyn_cast<DeclStmt>(st)) return decl(ds);
    if (const auto* is = dyn_cast<IfStmt>(st)) return ifStmt(is, list(is->getThen()), list(is->getElse()));
    if (const auto* ws = dyn_cast<WhileStmt>(st)) {
      if (ws->getConditionVariable()) throw Refused{"condition variable"};
      pure(ws->getCond(), "a loop test");
      return "{\"s\":\"while\"," + loopTest(ws->getCond()) + ",\"body\":" + list(ws->getBody()) + "}";
    }
    if (const auto* fs = dyn_cast<ForStmt>(st)) {
      if (fs->getConditionVariable()) throw Refused{"condition variable"};
      if (fs->getCond()) pure(fs->getCond(), "a loop test");
      std::string init = fs->getInit() ? stmt(fs->getInit()) : skip();
      std::string inc = fs->getInc() ? effect(fs->getInc(), in_.costOf(fs->getInc())) : skip();
      return "{\"s\":\"for\",\"init\":" + init + "," + loopTest(fs->getCond()) + ",\"inc\":" + inc +
             ",\"body\":" + list(fs->getBody()) + "}";
    }
    if (const auto* as = dyn_cast<AttributedStmt>(st)) return stmt(as->getSubStmt());
    if (const auto* e = dyn_cast<Expr>(st)) {
      if (in_.isRequire && in_.isRequire(e)) return skip();
      return effect(e, in_.costOf(e));
    }
    throw Refused{std::string("statement not in the fragment (") + st->getStmtClassName() + ")"};
  }

  std::string loopTest(const Expr* c) const {
    std::vector<std::string> cs;
    if (c) conjuncts(c, cs);
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
