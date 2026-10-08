package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.util.*

/** Lambdas, applications and the insertion of implicit applications (elaboration-zoo `04-implicit-args`):
 *  an inferred term whose type starts with implicit Π binders is applied to fresh metas for them. */
trait Applications:
  self: Elaborator =>
  import core.*

  /** Inserts implicit applications for all leading implicit Π binders of the type. */
  def insertAll(c: Cxt, span: Span, r: (Tm, Val, Stage)): (Tm, Val, Stage) =
    var (t, ty, st) = r
    var more = true
    while more do
      force(ty) match
        case Val.Pi(x, Icit.Impl, a, cl) =>
          val m = freshMeta(c, a, Stage.S1, span, s"the implicit argument `$x`")
          t = Tm.App(t, m, Icit.Impl)
          ty = inst(cl, ev(c, m))
        case _ => more = false
    (t, ty, st)

  /** As [[insertAll]], unless the term is an implicit lambda. */
  def insert(c: Cxt, span: Span, r: (Tm, Val, Stage)): (Tm, Val, Stage) = r._1 match
    case Tm.Lam(_, Icit.Impl, _) => r
    case _ => insertAll(c, span, r)

  /** A lambda with an inferred type (always meta: the object level has no functions). */
  def inferLambda(c: Cxt, param: Tree, ann: Option[Tree], body: Tree): (Tm, Val, Stage) =
    val name = paramName(param)
    val dom = ann match
      case Some(a) => checkType(c, a, Stage.S1)
      case None => freshType(c, Stage.S1, param.span, s"the type of `$name`")
    val dv = ev(c, dom)
    val (bt, bty) = inferS(bind(c, name, dv, Stage.S1), body, Stage.S1)
    (Tm.Lam(name, Icit.Expl, bt), Val.Pi(name, Icit.Expl, dv, Closure(c.env, quote(c.lvl + 1, bty))), Stage.S1)

  def checkLambda(c: Cxt, t: Tree, param: Tree, ann: Option[Tree], body: Tree, pi: Val.Pi, st: Stage): Tm =
    if st == Stage.S0 then
      fail(
        Diagnostic.error("E0908", "object-level functions cannot be defined", t.span, "a function at the object level")
          .withNote("the object level is first order; functions are meta-level code (formula functions, functors)")
      )
    val name = paramName(param)
    ann.foreach { an =>
      val at = checkType(c, an, Stage.S1)
      unifyAt(c, an.span, pi.dom, ev(c, at))
    }
    Tm.Lam(name, Icit.Expl, check(bind(c, name, pi.dom, Stage.S1), body, inst(pi.cl, Val.local(c.lvl)), st))

  def inferApp(c: Cxt, f: Tree, a: Tree, span: Span): (Tm, Val, Stage) =
    val (ft, fty, fs) = objectFunction(insertAll(c, f.span, infer(c, f)))
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, cl) =>
        val at = check(c, a, dom, fs)
        (Tm.App(ft, at, Icit.Expl), inst(cl, ev(c, at)), fs)
      case Val.Flex(_, _) =>
        val dom = ev(c, freshType(c, fs, a.span, "the type of an argument"))
        val cod = freshType(bind(c, "x", dom, fs), fs, span, "the type of an application")
        unifyAt(c, f.span, Val.Pi("x", Icit.Expl, dom, Closure(c.env, cod)), fty)
        val at = check(c, a, dom, fs)
        (Tm.App(ft, at, Icit.Expl), eval(ev(c, at) :: c.env, cod), fs)
      case other => notAFunction(c, f, a, other)

  /** Meta code of an object function type `⇑(A -> B)` (a relation or constructor passed around at the
   *  meta level) is applied at the object level: it is spliced. */
  private def objectFunction(r: (Tm, Val, Stage)): (Tm, Val, Stage) = force(r._2) match
    case Val.Lift(x) =>
      force(x) match
        case p: Val.Pi => (Tm.splice(r._1), p, Stage.S0)
        case _ => r
    case _ => r

  private def notAFunction(c: Cxt, f: Tree, a: Tree, ty: Val): Nothing =
    val why = ty match
      case Val.RelT | Val.PropT => "it is already a complete atom: too many arguments"
      case _ => s"its type `${show(c, ty)}` is not a function type"
    fail(
      Diagnostic.error("E0905", "not a function", f.span, "applied to an argument here")
        .withLabel(a.span, "argument")
        .withNote(s"`${TreeOps.headName(f).map(_.name).getOrElse("this")}` cannot be applied: $why")
    )
