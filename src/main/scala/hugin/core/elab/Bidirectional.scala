package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.{Literal, Tree}
import hugin.syntax.Trees.*
import hugin.util.*

/** The bidirectional core: `infer` and `check` dispatch on the surface tree to the construct families
 *  (universes, functions, records, operators, staging); `inferS` infers with a known stage. */
trait Bidirectional:
  self: Elaborator =>
  import core.*

  /** Infers a term, its type and its stage. */
  def infer(c: Cxt, t: Tree): (Tm, Val, Stage) = t match
    case Parens(i) => infer(c, i)
    case Ident(n) => resolve(c, n, t.span)
    case VarRef("Type") if !c.scope.contains("Type") => inferMetaUniverse()
    case VarRef(n) => resolve(c, n, t.span)
    case k: Keyword => inferKeyword(k)
    case Builtin(n) => inferBuiltin(n)
    case Lit(l) => (Tm.Lit(l, Stage.S1), Val.Base(BaseType.of(l), Stage.S1), Stage.S1)
    case Apply(f, a) => inferApp(c, f, a, t.span)
    case s: Select => inferSelect(c, s)
    case Arrow(_, _, _) if endsInRel(t) => (objectArrow(c, t), Val.U0, Stage.S0)
    case Arrow(label, dom, cod) => inferArrow(c, label, dom, cod, t.span)
    case ImplicitPi(names, dom, cod) =>
      val l = levels.fresh()
      (checkImplicitPi(c, names, dom, cod, l), Val.U1(l), Stage.S1)
    case ImplicitBinder(_, _) =>
      error("E0001", "implicit binders must be followed by `->`", t.span, "expected `{A : T} -> B`")
    case LiftE(a) => inferLift(c, a)
    case SpliceE(a) => inferSplice(c, a, t.span)
    case RecordType(entries) =>
      val l = levels.fresh()
      (checkRecordType(c, entries, l), Val.U1(l), Stage.S1)
    case RecordLit(fields, false) => inferRecord(c, fields)
    case Ascribe(e, a) =>
      val (at, s, _) = inferU(c, a)
      val av = ev(c, at)
      (check(c, e, av, s), av, s)
    case Lambda(param, ann, body) => inferLambda(c, param, ann, body)
    case Infix(op, l, r) => inferInfix(c, op, l, r, t.span, None)
    case Neg(_) | Not(_) | Conj(_, _) | Disj(_, _) => inferFormulaOrNegation(c, t)
    case Wildcard() =>
      fail(
        Diagnostic.error("E0903", "cannot infer the type of `_`", t.span, "type annotations needed")
          .withNote("`_` stands for an unknown meta value or, in object code, for a wildcard")
      )
    case other => unsupported(other)

  /** Infers with a known stage: literals and `_` take the stage; other terms are moved to it. */
  def inferS(c: Cxt, t: Tree, st: Stage): (Tm, Val) = t match
    case Parens(i) => inferS(c, i, st)
    case Lit(l) => (Tm.Lit(l, st), Val.Base(BaseType.of(l), st))
    case Wildcard() if st == Stage.S0 =>
      val a = freshMeta(c, Val.U0, Stage.S0, t.span, "the type of `_`", allowUnsolved = true)
      (Tm.Wild, ev(c, a))
    case Wildcard() =>
      val a = ev(c, freshType(c, st, t.span, "the type of `_`"))
      (freshMeta(c, a, st, t.span, "`_`"), a)
    case Infix(op, l, r) if arithOps.contains(op) =>
      val (tm, ty, _) = inferInfix(c, op, l, r, t.span, Some(st))
      (tm, ty)
    case _ =>
      val (tm, ty, s) = infer(c, t)
      adjust(c, t.span, tm, ty, s, st)

  /** Checks a term against a type at a stage. */
  def check(c: Cxt, t: Tree, a: Val, st: Stage): Tm = (t, force(a)) match
    case (Parens(i), _) => check(c, i, a, st)
    case (Lambda(param, ann, body), pi @ Val.Pi(_, Icit.Expl, _, _)) => checkLambda(c, t, param, ann, body, pi, st)
    case (_, Val.Pi(x, Icit.Impl, dom, cl)) =>
      // an implicit Π is introduced by an inserted implicit lambda
      Tm.Lam(x, Icit.Impl, check(newBinder(c, x, dom, Stage.S1), t, inst(cl, Val.local(c.lvl)), st))
    case (_, Val.Lift(x)) if st == Stage.S1 =>
      // every value of `⇑A` is a quote (up to conversion): check object code under a quote
      Tm.quote(check(c, t, x, Stage.S0))
    case (Arrow(label, dom, cod), Val.U1(l)) if !endsInRel(t) => checkMetaArrow(c, label, dom, cod, l)
    case (ImplicitPi(ns, d, cod), Val.U1(l)) => checkImplicitPi(c, ns, d, cod, l)
    case (RecordType(entries), Val.U1(l)) => checkRecordType(c, entries, l)
    case (RecordLit(fields, false), rt: Val.RecTy) => checkRecord(c, t, fields, rt)
    case (Lit(l), Val.Base(b, s)) if b == BaseType.of(l) => Tm.Lit(l, s)
    case (Lit(l), other) if checkLiteral.isDefinedAt((c, l, other, t.span)) => checkLiteral((c, l, other, t.span))
    case (Wildcard(), _) => if st == Stage.S0 then Tm.Wild else freshMeta(c, a, Stage.S1, t.span, "`_`")
    case (Infix(op, l, r), ty) if arithOps.contains(op) && !ty.isInstanceOf[Val.Flex] => checkArith(c, op, l, r, ty, st, t.span)
    case (_, Val.Flex(_, _)) =>
      val (tm, ty) = inferS(c, t, st)
      val (tm2, ty2, _) = insert(c, t.span, (tm, ty, st))
      coe(c, t.span, tm2, ty2, st, a, st)
    case _ =>
      val (tm, ty, s) = insert(c, t.span, infer(c, t))
      coe(c, t.span, tm, ty, s, a, st)

  /** Literals of types other than the primitive ones (overridden for nat literals, Q2). */
  def checkLiteral: PartialFunction[(Cxt, Literal, Val, Span), Tm] = PartialFunction.empty
