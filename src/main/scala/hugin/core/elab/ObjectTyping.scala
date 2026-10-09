package hugin.core
package elab

import hugin.core.objtype.*
import hugin.util.diagnostics.Problem

/** Object typing inside the elaboration (reference: object/types): at the end of each scope of object
 *  code, its core terms are read ([[ObjWalk]]) and checked ([[ObjCheck]]) against the object types of the
 *  constants and of the meta code they splice: a rule or query, a clause of a formula function, a piece
 *  of object code `⟨t⟩` of a meta definition or clause (at its type `⇑τ`). A functor's parameter types
 *  are abstract in its body. Variable types found by meets solve the unknown types of the variables (and
 *  with them implicit type arguments). Staged items are checked again by the handover where they involve
 *  meta code ([[handover.Handover]]). */
trait ObjectTyping:
  self: Elaborator =>
  import core.*

  /** The object constants and edges of the context `c`. */
  def objEnv(c: Cxt): ObjEnv = ObjEnv(core, contextLocals(c))

  private def contextLocals(c: Cxt): ObjEnv.Locals = new ObjEnv.Locals:
    def typeOf(lvl: Int, projs: List[String]): Option[Val] =
      if lvl >= c.lvl then None
      else
        var ty = c.binder(lvl).ty
        var v = Val.local(lvl)
        var ok = true
        for p <- projs if ok do
          force(ty) match
            case rt: Val.RecTy =>
              fieldTypes(rt, l => proj(v, l)).find(_._1 == p) match
                case Some((_, t)) =>
                  ty = t
                  v = proj(v, p)
                case None => ok = false
            case _ => ok = false
        Option.when(ok)(ty)
    def name(lvl: Int): String = if lvl < c.lvl then c.binder(lvl).name else s"#$lvl"
    def isMemberType(lvl: Int, projs: List[String]): Boolean =
      projs.isEmpty && lvl < c.lvl && c.binder(lvl).origin == BinderOrigin.Member && force(c.binder(lvl).ty) == Val.Lift(Val.U0)
    def relationHeads: List[OHead] =
      (0 until c.lvl).toList.filter { l =>
        val b = c.binder(l)
        b.origin == BinderOrigin.Member && (force(b.ty) match
          case Val.Lift(t) => isFactConstantType(t) || isObjectConstantType(t) && force(t) != Val.U0
          case _ => false
        )
      }.map(OHead.L(_, Nil))
    def edges: List[(Val, Val)] = state.localEdges

  /** The scope of the walker over the context `c`: its object variables are the stage-0 binders. */
  def walkScope(c: Cxt): ObjWalk.Scope =
    ObjWalk.Scope(
      c.lvl,
      c.env,
      l => Option.when(l < c.lvl && c.binder(l).stage == Stage.S0)(c.binder(l).name),
      l => Option.when(l < c.lvl && c.binder(l).stage == Stage.S1)(c.binder(l).ty),
      l => if l < c.lvl then c.binder(l).name else s"#$l"
    )

  /** Checks a rule or query (`heads` empty) over `c`, whose object variables are `vars`; reports every
   *  problem and fails (silently) if there is one. Unknown types of the variables are solved with their
   *  types where these are known object types. */
  def checkObjectItem(c: Cxt, vars: List[(Name, Tm)], heads: List[Tm], body: List[Tm]): Unit =
    val env = objEnv(c)
    val walk = ObjWalk(env, walkScope(c))
    val hs = walk.headTerms(heads)
    val fs = body.flatMap(walk.formulas) ++ walk.pendingExpects
    val (problems, gamma) = ObjCheck(ObjTypes(env), hs, fs, walk.constructing).run()
    reportAll(problems)
    for (x, tyTm) <- vars; t <- gamma.get(x); v <- asValue(t) do
      try undoOnFailure(unify(c.lvl, ev(c, tyTm), v))
      catch case _: UnifyError => ()

  /** Checks the object code `⟨t⟩` in the meta code `tm` of type `ty` (a definition's or a clause's
   *  right-hand side); fails at the first problem. */
  def checkObjectFragments(c: Cxt, tm: Tm, ty: Val): Unit = (Tm.unloc(tm), force(ty)) match
    case (Tm.Lam(x, _, b), Val.Pi(_, _, d, cl)) =>
      checkObjectFragments(bind(c, x, d, stageOfType(d)), b, inst(cl, Val.local(c.lvl)))
    case (Tm.Let(x, _, d, b), _) =>
      checkObjectFragments(c, b, ty) // the body's code; definitions in where blocks are checked on their own
    case (Tm.Quote(t), Val.Lift(a)) => checkFragment(c, t, a)
    case (Tm.Rec(fields), rt: Val.RecTy) =>
      val v = ev(c, tm)
      val tys = fieldTypes(rt, l => proj(v, l)).toMap
      for (l, f) <- fields; fty <- tys.get(l) do checkObjectFragments(c, f, fty)
    case (Tm.App(_, _, _), _) => checkArguments(c, tm)
    case _ =>

  /** The object code among the arguments of a meta function's application, at the function's domains. */
  private def checkArguments(c: Cxt, tm: Tm): Unit =
    def spine(t: Tm, acc: List[Tm]): (Tm, List[Tm]) = Tm.unloc(t) match
      case Tm.App(f, a, _) => spine(f, a :: acc)
      case other => (other, acc)
    val (f, args) = spine(tm, Nil)
    var ty = ObjWalk(objEnv(c), walkScope(c)).typeOfMeta(f)
    for a <- args do
      ty.map(force) match
        case Some(Val.Pi(_, _, d, cl)) =>
          checkObjectFragments(c, a, d)
          ty = Some(inst(cl, ev(c, a)))
        case _ => ty = None

  private def checkFragment(c: Cxt, t: Tm, a: Val): Unit =
    val env = objEnv(c)
    val walk = ObjWalk(env, walkScope(c))
    val types = ObjTypes(env)
    val problems = force(a) match
      // an atom (of type `rel`) is a formula too
      case Val.PropT | Val.RelT => ObjCheck(types, Nil, walk.formulas(t)).run()._1
      case Val.U0 | Val.Pi(_, _, _, _) => Nil
      case other =>
        val ot = walk.termAt(t)
        ObjCheck(types, Nil, walk.pendingExpects, List((ot, env.oty(other), "object code of this type"))).run()._1
    problems.headOption.foreach(p => fail(p))

  private def reportAll(problems: List[Problem]): Unit =
    if problems.nonEmpty then
      problems.foreach { p =>
        val d = p.toDiagnostic
        reporter.report(if d.origin.isEmpty then d.withOrigin(state.origin) else d)
      }
      throw ElabError(problems.head.toDiagnostic, silent = true)

  /** A closed value for an object type, to solve an unknown type with. */
  private def asValue(t: OTy): Option[Val] = t match
    case OTy.Base(b) => Some(Val.Base(b, Stage.S0))
    case OTy.Con(OHead.G(id), Nil) => Some(Val.Rigid(Head.Glob(id), Nil))
    case OTy.Fact(OHead.G(id), Nil) => Some(Val.FactTy(Val.Rigid(Head.Glob(id), Nil)))
    case _ => None

  /** Meta code `m` checked against `⇑x` through object code (`$m` under the quote cancels): its type `⇑τ`
   *  must be a subtype of `⇑x`, as if `m` were coerced at the meta level. */
  def passedCode(c: Cxt, span: hugin.util.Span, m: Tm, x: Val): Unit =
    ObjWalk(objEnv(c), walkScope(c)).typeOfMeta(m).map(force) match
      case Some(lifted @ Val.Lift(_)) => coe(c, span, m, lifted, Stage.S1, Val.Lift(x), Stage.S1)
      case _ =>

  /** `⇑a ≤ ⇑b` at the meta level: object subtyping between known object types (reference: meta/staging). */
  def liftSubtype(c: Cxt, a: Val, b: Val): Boolean =
    val env = objEnv(c)
    val (x, y) = (env.oty(a), env.oty(b))
    !x.vague && !y.vague && ObjTypes(env).isSub(x, y)
