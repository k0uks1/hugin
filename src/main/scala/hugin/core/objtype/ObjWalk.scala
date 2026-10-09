package hugin.core
package objtype

import hugin.util.Span
import scala.collection.mutable

/** Reads core terms of object code as [[OTerm]]s and [[OFormula]]s for [[ObjCheck]]: during elaboration
 *  (over an elaboration context, where spliced meta code is seen through its type `⇑τ`) and after staging
 *  (closed normal forms over the variables of an item). Object constants are resolved by evaluating the
 *  head of an application in the scope's environment. An argument `⟨t⟩` of a meta function whose domain
 *  is `⇑τ` is a term expected at `τ` ([[OFormula.Expect]]). */
final class ObjWalk(env: ObjEnv, scope: ObjWalk.Scope):
  import env.core.*

  private var wild = 0
  private val heads = mutable.ListBuffer.empty[(OTerm, OTy, String)]
  private val expects = mutable.ListBuffer.empty[OFormula]
  private var inHead = false

  /** The terms at constructing positions found while reading heads (arguments of meta functions). */
  def constructing: List[(OTerm, OTy, String)] = heads.toList

  /** Reads the heads of a rule. */
  def headTerms(hs: List[Tm]): List[OTerm] =
    inHead = true
    try hs.map(term(_, Span.NoSpan, scope))
    finally inHead = false

  /** Reads a formula (a body), with the expectations of arguments of meta functions in it. */
  def formulas(t: Tm): List[OFormula] =
    val fs = formula(t, Span.NoSpan, scope)
    val out = fs ++ expects.toList
    expects.clear()
    out

  /** Reads a term (object code at a type). */
  def termAt(t: Tm): OTerm = term(t, Span.NoSpan, scope)

  /** Expectations found while reading terms outside formulas. */
  def pendingExpects: List[OFormula] =
    val out = expects.toList
    expects.clear()
    out

  private def freshWild(): String =
    wild += 1
    s"${hugin.obj.Var.WildPrefix}$wild"

  private def spanOf(t: Tm, default: Span): Span = t match
    case Tm.Obj(ObjForm.Loc(sp), _) => sp
    case _ => default

  private def variable(t: Tm, s: ObjWalk.Scope): Option[String] = Tm.unloc(t) match
    case Tm.Var(ix) => s.objVar(s.lvl - ix - 1)
    case Tm.Obj(ObjForm.Named(x), Nil) => Some(x)
    case Tm.Obj(ObjForm.Wild, Nil) => Some(freshWild())
    case _ => None

  private def spine(t: Tm, args: List[(Tm, Icit)]): (Tm, List[(Tm, Icit)]) = Tm.unloc(t) match
    case Tm.App(f, a, i) => spine(f, (a, i) :: args)
    case other => (other, args)

  /** The relation an application's head refers to, and its explicit (object) arguments. */
  private def application(t: Tm, s: ObjWalk.Scope): (Option[RelInfo], List[Tm]) =
    val (f, args) = spine(t, Nil)
    val (impl, expl) = args.span(_._2 == Icit.Impl)
    val headTm = Tm.apps(f, impl)
    val info =
      try env.head(eval(s.env, headTm)).flatMap((h, as) => env.relInfo(h, as))
      catch case _: Exception => None
    f match
      case Tm.Splice(m) => metaArgs(m, s)
      case _ =>
    (info, expl.map(_._1))

  private def term(t: Tm, span: Span, s: ObjWalk.Scope): OTerm = t match
    case Tm.Obj(ObjForm.Loc(sp), List(u)) => term(u, sp, s)
    case Tm.Var(_) | Tm.Obj(ObjForm.Named(_), Nil) | Tm.Obj(ObjForm.Wild, Nil) =>
      variable(t, s).map(OTerm.Var(_, span)).getOrElse(OTerm.Code(OTy.Unknown, span))
    case Tm.Lit(l, _) => OTerm.Lit(l, span)
    case Tm.Persist(m) => OTerm.Code(metaType(m, s).map(env.oty).map(base).getOrElse(OTy.Unknown), span)
    case Tm.Arith(op, a, b, Stage.S0) => OTerm.Arith(op, term(a, span, s), term(b, span, s), span)
    case Tm.Negate(a, Stage.S0) => OTerm.Neg(term(a, span, s), span)
    case Tm.Obj(ObjForm.As, List(a, x)) => OTerm.As(term(a, span, s), variable(x, s).getOrElse(freshWild()), span)
    case Tm.Obj(ObjForm.Ascribe, List(a, ty)) => OTerm.Ascr(term(a, span, s), objType(ty, s), span)
    case Tm.Obj(ObjForm.Proj(l), List(a)) => OTerm.Proj(term(a, span, s), l, span)
    case Tm.Obj(ObjForm.With(ls), a :: es) =>
      OTerm.With(term(a, span, s), ls.zip(es).map { case ((l, lsp), e) => (l, term(e, span, s), lsp) }, span)
    case Tm.Splice(m) =>
      metaArgs(m, s)
      metaType(m, s).map(force) match
        case Some(Val.Lift(x)) => OTerm.Code(env.oty(x), span)
        case _ => OTerm.Code(OTy.Unknown, span)
    case Tm.App(_, _, _) | Tm.Global(_) =>
      val (info, args) = application(t, s)
      OTerm.App(info, args.map(a => term(a, spanOf(a, span), s)), span)
    case _ => OTerm.Code(OTy.Unknown, span)

  private def base(t: OTy): OTy = t

  private def objType(ty: Tm, s: ObjWalk.Scope): OTy =
    try env.oty(eval(s.env, ty))
    catch case _: Exception => OTy.Unknown

  private def formula(t: Tm, span: Span, s: ObjWalk.Scope): List[OFormula] = t match
    case Tm.Obj(ObjForm.Loc(sp), List(u)) => formula(u, sp, s)
    case Tm.Obj(ObjForm.And, as) => as.flatMap(formula(_, span, s))
    case Tm.Obj(ObjForm.Or, _) => List(OFormula.Disj(alternatives(t).map(formula(_, span, s)), span))
    case Tm.Obj(ObjForm.Not, List(a)) => formula(a, span, s).map(OFormula.Not(_, span))
    case Tm.Obj(ObjForm.Compare(op), List(a, b)) => List(OFormula.Cmp(op, term(a, span, s), term(b, span, s), span))
    case Tm.Obj(ObjForm.Agg(kind), List(x, a, b)) =>
      List(OFormula.Agg(variable(x, s).getOrElse(freshWild()), kind, term(a, span, s), formula(b, span, s), span))
    case Tm.Obj(ObjForm.As, List(a, x)) =>
      formula(a, span, s) match
        case List(OFormula.Atom(r, args, None, sp)) => List(OFormula.Atom(r, args, variable(x, s), sp))
        case other => other
    case Tm.Fresh(ns, b) => formula(b, span, s.fresh(ns))
    case Tm.Splice(m) =>
      metaArgs(m, s)
      Nil
    case Tm.App(_, _, _) | Tm.Global(_) =>
      application(t, s) match
        case (Some(r), args) => List(OFormula.Atom(r, args.map(a => term(a, spanOf(a, span), s)), None, span))
        case (None, args) =>
          args.foreach(a => term(a, span, s))
          Nil
    case _ => Nil

  private def alternatives(t: Tm): List[Tm] = Tm.unloc(t) match
    case Tm.Obj(ObjForm.Or, as) => as.flatMap(alternatives)
    case _ => List(t)

  /** The type of meta code (a spine of a variable or global applied to arguments), if it can be read off. */
  def typeOfMeta(t: Tm): Option[Val] = metaType(t, scope)

  private def metaType(t: Tm, s: ObjWalk.Scope): Option[Val] = Tm.unloc(t) match
    case Tm.Var(ix) => s.metaType(s.lvl - ix - 1)
    case Tm.Global(id) => Some(globals(id).ty)
    case Tm.Lit(l, Stage.S1) => Some(Val.Base(hugin.obj.BaseType.of(l), Stage.S1))
    case Tm.App(f, a, _) =>
      metaType(f, s).map(force) match
        case Some(Val.Pi(_, _, _, cl)) =>
          try Some(inst(cl, eval(s.env, a)))
          catch case _: Exception => None
        case _ => None
    case _ => None

  /** The arguments `⟨t⟩` of a meta function applied in object code, as expectations at their domains. */
  private def metaArgs(m: Tm, s: ObjWalk.Scope): Unit =
    val (f, args) = spine(m, Nil)
    val fname = Tm.unloc(f) match
      case Tm.Global(id) => globals(id).name
      case Tm.Var(ix) => s.name(s.lvl - ix - 1)
      case _ => ""
    var ty = metaType(f, s)
    var k = 0
    for (a, i) <- args do
      ty.map(force) match
        case Some(Val.Pi(_, _, dom, cl)) =>
          if i == Icit.Expl then k += 1
          (Tm.unloc(a), force(dom)) match
            case (Tm.Quote(code), Val.Lift(x)) if isData(x) =>
              val where = s"argument $k of `$fname`"
              val ot = term(code, spanOf(a, Span.NoSpan), s)
              val tp = env.oty(x)
              if inHead then heads += ((ot, tp, where)) else expects += OFormula.Expect(ot, tp, where, ot.span)
            case _ =>
          ty =
            try Some(inst(cl, eval(s.env, a)))
            catch case _: Exception => None
        case _ => ty = None

  private def isData(x: Val): Boolean = force(x) match
    case Val.PropT | Val.U0 | Val.Pi(_, _, _, _) => false
    case _ => true

object ObjWalk:
  /** The variables in scope, by level: `objVar` names the object variables (of a rule, of `fresh`),
   *  `metaType` gives the types of meta variables, `env` evaluates heads. */
  final case class Scope(lvl: Int, env: List[Val], objVar: Int => Option[String], metaType: Int => Option[Val], name: Int => String):
    def fresh(ns: List[String]): Scope =
      val base = lvl
      Scope(
        lvl + ns.length,
        (0 until ns.length).reverse.map(i => Val.local(base + i)).toList ++ env,
        l => if l >= base then Some(ns(l - base)) else objVar(l),
        l => if l >= base then None else metaType(l),
        l => if l >= base then ns(l - base) else name(l)
      )

  /** The scope of a staged item: its variables (innermost first, as `Tm.Var` indices count). */
  def staged(names: List[String], base: List[Val]): Scope =
    val n = names.length
    Scope(n, (0 until n).reverse.map(Val.local).toList ++ base, l => Some(names(n - l - 1)), _ => None, l => names(n - l - 1))
