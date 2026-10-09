package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.{Apply, RecordLit}
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
          val what = Tm.unloc(r._1) match
            case Tm.Global(id) if globals(id).kind.isInstanceOf[GlobalKind.Family] => s"type argument `$x` of family `${globals(id).name}`"
            case _ => s"the implicit argument `$x`"
          val m = freshMeta(c, a, Stage.S1, span, what)
          insertedImplicit(c, span, x, m)
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
    val cb = bind(c, name, dv, Stage.S1, site = Some(Site(param.span, "parameter")))
    recordLocalDeclaration(cb, c.lvl)
    val (bt, bty) = inferS(cb, body, Stage.S1)
    (Tm.Lam(name, Icit.Expl, bt), Val.Pi(name, Icit.Expl, dv, Closure(c.env, quote(c.lvl + 1, bty))), Stage.S1)

  def checkLambda(c: Cxt, t: Tree, param: Tree, ann: Option[Tree], body: Tree, pi: Val.Pi, st: Stage): Tm =
    if st == Stage.S0 then
      fail(TypeProblem.ObjectFunction(t.span))
    val name = paramName(param)
    ann.foreach { an =>
      val at = checkType(c, an, Stage.S1)
      unifyAt(c, an.span, pi.dom, ev(c, at))
    }
    val cb = bind(c, name, pi.dom, Stage.S1, site = Some(Site(param.span, "parameter")))
    recordLocalDeclaration(cb, c.lvl)
    Tm.Lam(name, Icit.Expl, check(cb, body, inst(pi.cl, Val.local(c.lvl)), st))

  def inferApp(c: Cxt, f: Tree, a: Tree, span: Span): (Tm, Val, Stage) =
    val (ft, fty, fs) = objectFunction(insertAll(c, f.span, infer(c, f)))
    (a, namedColumns(fty)) match
      case (rl: RecordLit, Some(cols)) if fs == Stage.S0 =>
        (namedPattern(c, f, ft, cols, rl), cols.foldLeft(fty)((t, _) => objectCodomain(t)), Stage.S0)
      case _ => inferPositionalApp(c, f, a, span, ft, fty, fs)

  /** A record passed for a signature with requirements records them when evaluated ([[Tm.Require]]). */
  private def withRequirements(dom: Val, span: Span, t: Tm): Tm = force(dom) match
    case Val.RecTy(_, _, _, reqs, _) if reqs.nonEmpty => Tm.Require(reqs, span, t)
    case _ => t

  /** The application of a functor (a function returning a module) records its frame for the module
   *  instances it creates ([[Tm.Trace]]). */
  private def functorApplication(f: Tree, span: Span, t: Tm, resTy: Val): Tm = force(resTy) match
    case _: Val.RecTy =>
      Tm.Trace(TraceFrame(s"in application of `${hugin.syntax.Printer.show(TreeOps.flattenApp(f)._1)}`", span), t)
    case _ => t

  /** The number of columns an object relation or constructor of type `ty` still takes (if any). */
  def missingColumns(ty: Val): Option[Int] =
    def go(t: Val, n: Int): Int = force(t) match
      case Val.Pi(_, _, d, cl) if stageOfType(d) == Stage.S0 => go(inst(cl, Val.Wild), n + 1)
      case _ => n
    Option.when(isFactConstantType(ty))(go(ty, 0)).filter(_ > 0)

  /** The object constant (or family of them) that the object term `t` applies: the head of its spine, also
   *  through the splice of a family's application (`$(node ?A) L R`). */
  def objectHead(t: Tm): Option[Int] =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case Tm.Splice(f) => head(f)
      case other => other
    head(t) match
      case Tm.Global(id) => Some(id)
      case _ => None

  /** E0207: the relation or constructor `head` (elaborated in `t`) applied to `found` instead of
   *  `expected` arguments. */
  def objectArity(head: Tree, t: Tm, expected: Int, found: Int, span: Span): Nothing =
    val declared = objectHead(t).map(globals(_).span).getOrElse(Span.NoSpan)
    fail(ElabProblem.ObjectArity(hugin.syntax.Printer.show(head), expected, found, span, declared))

  /** The codomain of an object arrow (object arrows are not dependent). */
  private def objectCodomain(ty: Val): Val = force(ty) match
    case Val.Pi(_, _, _, cl) => inst(cl, Val.Wild)
    case other => other

  private def inferPositionalApp(c: Cxt, f: Tree, a: Tree, span: Span, ft: Tm, fty: Val, fs: Stage): (Tm, Val, Stage) =
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, cl) =>
        val at = withRequirements(dom, span, check(c, a, dom, fs))
        val resTy = inst(cl, ev(c, at))
        (functorApplication(f, span, Tm.App(ft, at, Icit.Expl), resTy), resTy, fs)
      // object syntax (a projection `E.loc`, a variable, a comparison, …) is never a function, even while
      // its type is still unknown: applying it is E0905, not an application to be solved by unification
      case Val.Flex(_, _) if isObjectSyntax(ft) => notAFunction(c, f, a, fty, ft)
      case Val.Flex(_, _) =>
        val dom = ev(c, freshType(c, fs, a.span, "the type of an argument"))
        val cod = freshType(bind(c, "x", dom, fs), fs, span, "the type of an application")
        unifyAt(c, f.span, Val.Pi("x", Icit.Expl, dom, Closure(c.env, cod)), fty)
        val at = check(c, a, dom, fs)
        (Tm.App(ft, at, Icit.Expl), eval(ev(c, at) :: c.env, cod), fs)
      case other => notAFunction(c, f, a, other, ft)

  private def isObjectSyntax(t: Tm): Boolean = Tm.unloc(t) match
    case Tm.Obj(_, _) => true
    case _ => false

  /** Meta code of an object function type `⇑(A -> B)` (a relation or constructor passed around at the
   *  meta level) is applied at the object level: it is spliced. */
  private def objectFunction(r: (Tm, Val, Stage)): (Tm, Val, Stage) = force(r._2) match
    case Val.Lift(x) =>
      force(x) match
        case p: Val.Pi => (Tm.splice(r._1), p, Stage.S0)
        case _ => r
    case _ => r

  private def notAFunction(c: Cxt, f: Tree, a: Tree, ty: Val, ft: Tm): Nothing =
    requireDeclared(ft)
    if force(ty) == Val.RelT then
      val (head, args) = TreeOps.flattenApp(Apply(f, a)(f.span.to(a.span)))
      objectArity(head, ft, args.length - 1, args.length, f.span.to(a.span))
    val why = ty match
      case _ if isObjectSyntax(ft) => "it is an object-level value, not a relation or constructor"
      case Val.RelT | Val.PropT => "it is already a complete atom: too many arguments"
      case _ => s"its type `${show(c, ty)}` is not a function type"
    fail(TypeProblem.NotAFunction(TreeOps.headName(f).map(_.name).getOrElse(hugin.syntax.Printer.show(f)), why, f.span, a.span))
