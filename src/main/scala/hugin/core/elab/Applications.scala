package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.{Apply, NamedArg, RecordLit}
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

  /** The head of `f {x := e}… a₁ … aₙ` if it is a meta constant (a constructor, function, definition or
   *  postulate, not a family) applied to positional arguments, after named implicit arguments that each
   *  name a different one of its leading implicit binders (#186 P5). */
  def expectedTypeHead(c: Cxt, t: Tree): Option[Tree] =
    val (head, args) = TreeOps.flattenApp(t)
    val (named, positional) = args.span(_.isInstanceOf[NamedArg])
    head match
      case id @ hugin.syntax.Trees.Ident(n)
          if positional.nonEmpty && !positional.exists(_.isInstanceOf[NamedArg]) && c.scope.get(n).isEmpty &&
            !state.bodyDeclared(n) && !state.unelaborated(n) =>
        lookupGlobal(n).map(sharedAt(_, state.stage)).filter(g => globals(g).stage == Stage.S1 && !isFamily(g)).flatMap { g =>
          val leading = telescope(globals(g).ty)._1.takeWhile(_._2 == Icit.Impl).map(_._1)
          val names = named.collect { case a: NamedArg => a.name }
          Option.when(names.distinct.length == names.length && names.forall(leading.contains))(id)
        }
      // a resolved constant in generated code (the rule names of the judgment notation, [[Judgments]])
      case ref @ hugin.syntax.Trees.SymRef(g, _) if positional.nonEmpty && named.isEmpty && globals(g).stage == Stage.S1 && !isFamily(g) =>
        Some(ref)
      case _ => None

  /** An application `f {x := e}… a₁ … aₙ` of a meta constant checked against `expected` (#186 P5): the
   *  result type of `f`, after its leading implicit arguments (fresh unknowns) and the `n` explicit ones, is
   *  unified with the expected type *before* the arguments are checked, so that they are checked against
   *  types that the expected type determines. Lean 4 propagates an expected type so to an application
   *  whose result does not depend on its explicit arguments (`ElabAppArgs.propagateExpectedType`), and
   *  Agda checks a constructor application by taking the parameters from the target type
   *  (`checkConstructorApplication`). A derivation `fire M (ppos refl E pnil) H` of `std/semantics` is so
   *  checked with its program and rule known, which none of its arguments determines alone. Only when the
   *  result type does not depend on the explicit arguments and is a family applied (where checking against
   *  the expected type is unification, not a coercion), and only if unification succeeds: otherwise it is
   *  undone, and the arguments are checked as without the expected type. So it adds only solutions that
   *  unifying the application's type with the expected type adds anyway, earlier. Then the named implicit
   *  arguments are checked against their binders, and the explicit ones in order, as an application is
   *  elaborated otherwise. */
  def checkAppWithExpected(c: Cxt, t: Tree, head: Tree, expected: Val): (Tm, Val, Stage) =
    val (_, args) = TreeOps.flattenApp(t)
    val (named, positional) = args.span(_.isInstanceOf[NamedArg])
    val namedArgs = named.collect { case a: NamedArg => a }
    val (ht, hty, hs) = infer(c, head)
    // the head is recorded for tooling as an application without the expected type records it: with its
    // implicit arguments inserted (`ident {int}`), or as inferred if an implicit argument is named
    if namedArgs.nonEmpty then recordTyped(c, head.span, ht, hty, hs, checked = false)
    // the leading implicit arguments: unknowns, also those given by name (solved by their arguments below)
    var ft = ht
    var fty = hty
    val implicits = List.newBuilder[(Name, Val, Val)]
    var more = true
    while more do
      force(fty) match
        case Val.Pi(x, Icit.Impl, a, cl) =>
          val m = freshMeta(c, a, Stage.S1, head.span, s"the implicit argument `$x`")
          if !namedArgs.exists(_.name == x) then insertedImplicit(c, head.span, x, m)
          val mv = ev(c, m)
          implicits += ((x, a, mv))
          ft = Tm.App(ft, m, Icit.Impl)
          fty = inst(cl, mv)
        case _ => more = false
    if namedArgs.isEmpty then recordTyped(c, head.span, ft, fty, hs, checked = false)
    // the result type after the explicit arguments (bound to fresh variables), if they are contiguous
    val n = positional.length
    def after(ty: Val, k: Int): Option[Val] =
      if k == n then Some(ty)
      else
        force(ty) match
          case Val.Pi(_, Icit.Expl, _, cl) => after(inst(cl, Val.local(c.lvl + k)), k + 1)
          case _ => None
    after(fty, 0).foreach { res =>
      val body = quote(c.lvl + n, res)
      val independent = (0 until n).forall(i => !occurs(i, body))
      val familyApp = force(res) match
        case Val.Rigid(Head.Glob(f), _) => isFamily(f)
        case _ => false
      if independent && familyApp then
        try undoOnFailure(unify(c.lvl, res, expected))
        catch case _: UnifyError => ()
    }
    val bound = implicits.result()
    namedArgs.foreach { a =>
      val (_, dom, mv) = bound.find(_._1 == a.name).get
      val at = core.anonymously(check(c, a.value, dom, Stage.S1))
      unifyAt(c, a.value.span, mv, ev(c, at))
    }
    var fs = hs
    var f: Tree = named.foldLeft(head: Tree)((g, a) => Apply(g, a)(g.span.to(a.span)))
    positional.zipWithIndex.foreach { (a, i) =>
      if i > 0 then
        val r = insertAll(c, f.span, (ft, fty, fs))
        ft = r._1; fty = r._2; fs = r._3
      val span = f.span.to(a.span)
      val r = inferPositionalApp(c, f, a, span, ft, fty, fs)
      ft = r._1; fty = r._2; fs = r._3
      f = Apply(f, a)(span)
    }
    (ft, fty, fs)

  def inferApp(c: Cxt, f: Tree, a: Tree, span: Span): (Tm, Val, Stage) = a match
    case n: NamedArg => inferNamedApp(c, f, n, span)
    case _ => inferPlainApp(c, f, a, span)

  /** `f {x := e}` (reference: meta/functions): the leading implicit arguments of `f` up to the one named
   *  `x` are inserted, and `e` is checked as that one. The implicit arguments after it stay: the next
   *  explicit argument (or the expected type) inserts them, and a further `{y := e'}` may give one. */
  private def inferNamedApp(c: Cxt, f: Tree, n: NamedArg, span: Span): (Tm, Val, Stage) =
    val name = n.name
    var (t, ty, st) = infer(c, f)
    f match
      case _: hugin.syntax.Trees.Ident | _: hugin.syntax.Trees.VarRef | _: hugin.syntax.Trees.Select =>
        recordTyped(c, f.span, t, ty, st, checked = false)
      case _ =>
    val available = List.newBuilder[Name]
    var done = false
    while !done do
      force(ty) match
        case Val.Pi(x, Icit.Impl, a, cl) if x == name =>
          val at = core.anonymously(check(c, n.value, a, Stage.S1))
          t = Tm.App(t, at, Icit.Impl)
          ty = inst(cl, ev(c, at))
          done = true
        case Val.Pi(x, Icit.Impl, a, cl) =>
          available += x
          val m = freshMeta(c, a, Stage.S1, f.span, s"the implicit argument `$x`")
          insertedImplicit(c, f.span, x, m)
          t = Tm.App(t, m, Icit.Impl)
          ty = inst(cl, ev(c, m))
        case _ =>
          val fn = TreeOps.headName(f).map(_.name).getOrElse(hugin.syntax.Printer.show(f))
          fail(TypeProblem.NoImplicitNamed(name, fn, available.result(), n.nameSpan))
    (t, ty, st)

  private def inferPlainApp(c: Cxt, f: Tree, a: Tree, span: Span): (Tm, Val, Stage) =
    val head = insertAll(c, f.span, infer(c, f))
    // the head of an application is inferred, not checked: its type is recorded here (for tooling)
    f match
      case _: hugin.syntax.Trees.Ident | _: hugin.syntax.Trees.VarRef | _: hugin.syntax.Trees.Select =>
        recordTyped(c, f.span, head._1, head._2, head._3, checked = false)
      case _ =>
    val (ft, fty, fs) = objectFunction(head)
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

  private[elab] def inferPositionalApp(c: Cxt, f: Tree, a: Tree, span: Span, ft: Tm, fty: Val, fs: Stage): (Tm, Val, Stage) =
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, cl) =>
        // the argument's instances are anonymous ([[Modules.argument]]): checking it may evaluate it
        val (at, av) = core.anonymously {
          val at = withRequirements(dom, span, check(c, a, dom, fs))
          (at, ev(c, at))
        }
        val resTy = inst(cl, av)
        (functorApplication(f, span, Tm.App(ft, at, Icit.Expl), resTy), resTy, fs)
      // object syntax (a projection `E.loc`, a variable, a comparison, …) is never a function, even while
      // its type is still unknown: applying it is E0905, not an application to be solved by unification
      case Val.Flex(_, _) if isObjectSyntax(ft) => notAFunction(c, f, a, fty, ft)
      case Val.Flex(_, _) =>
        val dom = ev(c, freshType(c, fs, a.span, "the type of an argument"))
        val cod = freshType(bind(c, "x", dom, fs), fs, span, "the type of an application")
        unifyAt(c, f.span, Val.Pi("x", Icit.Expl, dom, Closure(c.env, cod)), fty)
        val (at, av) = core.anonymously {
          val at = check(c, a, dom, fs)
          (at, ev(c, at))
        }
        (Tm.App(ft, at, Icit.Expl), eval(av :: c.env, cod), fs)
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
