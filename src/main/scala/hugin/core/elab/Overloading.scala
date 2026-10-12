package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Operators bound to meta functions (reference: lexical-structure, operators bound to meta functions):
 *  `%infix + plus.` makes the symbol `+` denote the meta function `plus` of the file, so that `a + b` at
 *  the meta level is `plus a b`. The symbols are `+ - * / ^ ≡` (`≡` also spelled `==`); their precedence is
 *  the table's, so a binding never changes how a file parses.
 *
 *  *Scope.* A binding travels with its function: it is in effect in a file wherever the function's name
 *  denotes the function there (it is declared in the file, opened by `%use`, or the prelude's), as an
 *  Agda operator is its name. So `%use "std/nat".` brings `+` for `nat`, and `%use "std/nat" (minus).`
 *  only `-`.
 *
 *  *Overloading*, type-directed and without classes, as Idris 2 resolves an overloaded name: several
 *  bindings of one symbol may be in scope (`+` for `nat` from `std/nat`, for `int` from `std/int`); the
 *  binding is chosen by the types, and it is an error if several fit (E0932) or none does (E0933). Idris
 *  elaborates each alternative and keeps those that succeed, after pruning them by the expected type's
 *  head (`TTImp.Elab.Ambiguity`); here the candidates are compared by the heads of their types alone,
 *  without elaborating anything twice: first their results against the expected type, then, if several
 *  remain, their first explicit domain against the type of the operand, which is inferred once and then
 *  used as the argument. Each operand is elaborated exactly once, so nested operators cost time linear in
 *  their number, and nothing is undone. A head that is not known (an unsolved type, a type variable, a
 *  stuck type-level application) fits every candidate.
 *
 *  *Built-in meanings.* The arithmetic operators keep the meanings they have without bindings: the
 *  successor `e + k` on a nat-like type (also before any binding), the operations of `std/int` on the meta
 *  `int`, and the primitive operations on meta base types. A binding that fits is preferred; the built-in
 *  meaning applies when none fits the type. Object code (stage 0) never uses bindings. */
trait Overloading:
  self: Elaborator =>
  import core.*

  /** The symbols that `%infix op f.` binds. */
  val bindableOperators: Set[String] = Set("+", "-", "*", "/", "^", "≡")

  /** The bindings of the files this file may import, by symbol. */
  private lazy val importedOperators: Map[String, List[Int]] =
    file.imports.values.toList.flatMap(_.operators).distinct.groupMap(_._1)(_._2)

  /** Whether `id` may be bound to an operator: a meta constant applied to at least two explicit arguments. */
  private def bindable(id: Int): Boolean =
    val g = globals(id)
    g.stage == Stage.S1 && !g.pending && telescope(g.ty)._1.count(_._2 == Icit.Expl) >= 2

  /** The file's own bindings whose functions were elaborated (in source order). */
  def ownOperators: List[(String, Int)] =
    for (op, n) <- state.operatorNames; id <- scope.get(n) if bindable(id) yield (op, id)

  /** The meta functions that the symbol `op` denotes here: the file's own bindings, and those of other
   *  files whose functions are in scope by their names. */
  def visibleOperators(op: String): List[Int] =
    val own = state.operatorNames.collect { case (`op`, n) => n }.flatMap(scope.get).filter(bindable)
    val imported = importedOperators.getOrElse(op, Nil).filter(id => lookupGlobal(globals(id).name).contains(id))
    (own ++ imported).distinct

  /** Whether `a op b` at the meta level is resolved here rather than by the built-in operators: `op` has
   *  a binding in scope, or it has no built-in meaning (`≡`). */
  def overloaded(op: String): Boolean =
    bindableOperators(op) && (op == "≡" || visibleOperators(op).nonEmpty)

  // ------------------------------------------------------------------ the heads of types

  /** The head of a type, as far as overloading compares types: `None` if it is not known. */
  private enum Shape:
    case Global(id: Int)
    case Base(b: BaseType, st: Stage)
    case Universe, Function, Code, Record, Formula

    /** A variable of the context (a type parameter): rigid, so only a binding generic there fits it. */
    case Variable

  /** The head of a type of the context being elaborated, whose variables are rigid ([[Shape.Variable]]). */
  private def shape(v: Val): Option[Shape] = force(v) match
    case Val.Rigid(Head.Local(_), _) => Some(Shape.Variable)
    case other => bindingShape(other)

  /** The head of a type in a binding's signature, whose variables are its own binders: generic. */
  private def bindingShape(v: Val): Option[Shape] = force(v) match
    case Val.Rigid(Head.Glob(id), _) =>
      kindOf(id) match
        // a stuck type-level application may still reduce
        case _: GlobalKind.Function | _: GlobalKind.Opaque | _: GlobalKind.Definition => None
        case _ => Some(Shape.Global(id))
    case Val.Base(b, st) => Some(Shape.Base(b, st))
    case Val.U0 | Val.U1(_) => Some(Shape.Universe)
    case _: Val.Pi => Some(Shape.Function)
    case _: Val.Lift => Some(Shape.Code)
    case _: Val.RecTy => Some(Shape.Record)
    case Val.RelT | Val.PropT => Some(Shape.Formula)
    case _ => None

  private def fits(a: Option[Shape], b: Option[Shape]): Boolean = a.isEmpty || b.isEmpty || a == b

  /** The heads of the two explicit domains of a bound function and of its result (after the implicit
   *  arguments that follow them). */
  private final case class Signature(first: Option[Shape], second: Option[Shape], result: Option[Shape])

  private def signature(id: Int): Signature =
    var ty = globals(id).ty
    var l = 0
    val doms = scala.collection.mutable.ListBuffer.empty[Option[Shape]]
    var result: Option[Shape] = None
    var more = true
    while more do
      force(ty) match
        case Val.Pi(_, i, a, cl) if i == Icit.Impl || doms.length < 2 =>
          if i == Icit.Expl then doms += bindingShape(a)
          ty = inst(cl, Val.local(l))
          l += 1
        case other =>
          result = bindingShape(other)
          more = false
    Signature(doms.headOption.flatten, doms.lift(1).flatten, result)

  private def candidate(id: Int): OperatorCandidate = OperatorCandidate(globals(id).name, show(Cxt.empty, globals(id).ty))

  private def candidates(ids: List[Int]): List[OperatorCandidate] = ids.map(candidate)

  // ------------------------------------------------------------------ resolution

  /** The outcome of resolving `a op b`: a binding, applied (with the operand inferred to choose it, if
   *  one was), or the built-in meaning (likewise). */
  private enum Resolved:
    case Binding(id: Int, operand: Option[(Boolean, Tm, Val)])
    case Builtin(operand: Option[(Tm, Val, Stage)])

  /** Chooses the meaning of `a op b` at the meta level, with the expected type if known. */
  private def resolveOperator(c: Cxt, t: Infix, expected: Option[Val], st: Option[Stage]): Resolved =
    val op = t.op
    val all = visibleOperators(op)
    val builtin = op != "≡"
    def builtinFor(ty: Val): Boolean = builtin && isMetaPrim(ty).isDefined
    val exp = expected.flatMap(shape)
    val byResult = exp.fold(all)(e => all.filter(id => fits(signature(id).result, Some(e))))
    def noneFits(operand: Option[Val]): Nothing =
      fail(OperatorProblem.NoneFits(op, candidates(all), operand.map(show(c, _)), expected.map(show(c, _)), t.opSpan))
    if all.isEmpty then
      if builtin then Resolved.Builtin(None) else noneFits(None)
    else if exp.isDefined && byResult.length == 1 then Resolved.Binding(byResult.head, None)
    else if exp.isDefined && byResult.isEmpty then
      if builtinFor(expected.get) then Resolved.Builtin(None) else noneFits(None)
    else
      // the operand decides: inferred once, and passed on to what it chooses
      val (first, second, swapped) = order(t.lhs, t.rhs)
      val (ft, fty, fs) = st match
        case Some(s) =>
          val (a, b) = inferS(c, first, s)
          (a, b, s)
        case None => infer(c, first)
      if fs != Stage.S1 then Resolved.Builtin(Some((ft, fty, fs)))
      // `e + k` on a nat-like type is the successor (reference: meta/families)
      else if op == "+" && !swapped && natType(fty).isDefined && successorCount(second).isDefined then
        Resolved.Builtin(Some((ft, fty, fs)))
      else
        val (it, ity, _) = insert(c, first.span, (ft, fty, fs))
        val s = shape(ity)
        // an integer literal next to an operand of unknown type makes it an `int`, as without bindings
        // (reference: meta/functions, literals)
        if force(ity).isInstanceOf[Val.Flex] && builtin && isIntLit(second) then return Resolved.Builtin(Some((ft, fty, fs)))
        val byOperand = byResult.filter { id =>
          val sig = signature(id)
          fits(if swapped then sig.second else sig.first, s)
        }
        byOperand match
          case List(id) => Resolved.Binding(id, Some((swapped, it, ity)))
          case Nil if builtinFor(ity) => Resolved.Builtin(Some((ft, fty, fs)))
          case Nil => noneFits(Some(ity))
          case several =>
            fail(OperatorProblem.Ambiguous(op, candidates(several), s.map(_ => show(c, ity)), t.opSpan))

  /** `a op b` checked against `a` at the meta level, if `op` is [[overloaded]]. */
  def checkOperator(c: Cxt, t: Infix, a: Val): Tm =
    resolveOperator(c, t, Some(a), Some(Stage.S1)) match
      case Resolved.Binding(id, operand) =>
        val (tm, ty) = applyBinding(c, id, t, operand)
        coe(c, t.span, tm, ty, Stage.S1, a, Stage.S1)
      case Resolved.Builtin(None) if !force(a).isInstanceOf[Val.Flex] => checkArith(c, t.op, t.lhs, t.rhs, a, Stage.S1, t.span)
      case Resolved.Builtin(operand) =>
        val (tm, ty, s) = insert(c, t.span, inferBuiltin(c, t, Some(Stage.S1), operand))
        coe(c, t.span, tm, ty, s, a, Stage.S1)

  /** `a op b` inferred, at stage `st` if known, if `op` is [[overloaded]]. */
  def inferOperator(c: Cxt, t: Infix, st: Option[Stage]): (Tm, Val, Stage) =
    resolveOperator(c, t, None, st) match
      case Resolved.Binding(id, operand) =>
        val (tm, ty) = applyBinding(c, id, t, operand)
        (tm, ty, Stage.S1)
      case Resolved.Builtin(operand) => inferBuiltin(c, t, st, operand)

  private def inferBuiltin(c: Cxt, t: Infix, st: Option[Stage], operand: Option[(Tm, Val, Stage)]): (Tm, Val, Stage) =
    if t.op == "≡" then fail(OperatorProblem.NoneFits(t.op, Nil, None, None, t.opSpan))
    inferInfix(c, t.op, t.lhs, t.rhs, t.span, st, operand)

  /** `f a b` for the binding `f` of `a op b`, the operand already inferred if one was. The operator's
   *  position refers to `f` (hover, definition). */
  private def applyBinding(c: Cxt, id: Int, t: Infix, operand: Option[(Boolean, Tm, Val)]): (Tm, Val) =
    val g = globals(id)
    // a function whose clauses have a syntax error: its uses are not elaborated
    if state.unelaborated(g.name) && scope.get(g.name).contains(id) then
      state.used += id
      throw ElabError(ElabProblem.UnresolvedName(g.name, t.opSpan, None, false).toDiagnostic, silent = true)
    state.used += id
    recordUse(t.opSpan, id)
    val (ht, hty, _) = globalRef(id)
    recordTyped(c, t.opSpan, ht, hty, Stage.S1, checked = false)
    def argument(f: (Tm, Val), arg: Tree, known: Option[(Tm, Val)]): (Tm, Val) =
      val (ft, fty, _) = insertAll(c, t.opSpan, (f._1, f._2, Stage.S1))
      force(fty) match
        case Val.Pi(_, Icit.Expl, dom, cl) =>
          val (at, av) = core.anonymously {
            val at = known match
              case Some((tm, ty)) => coe(c, arg.span, tm, ty, Stage.S1, dom, Stage.S1)
              case None => check(c, arg, dom, Stage.S1)
            (at, ev(c, at))
          }
          (Tm.App(ft, at, Icit.Expl), inst(cl, av))
        case other => throw Impossible(s"the binding ${g.name} of ${t.op} takes no explicit argument at ${show(c, other)}")
    val left = argument((ht, hty), t.lhs, operand.collect { case (false, tm, ty) => (tm, ty) })
    argument(left, t.rhs, operand.collect { case (true, tm, ty) => (tm, ty) })

  // ------------------------------------------------------------------ overloaded opened names

  /** The head of an application (or a name alone) if it is a name that `%use` items open for several meta
   *  constants ([[overloadedName]]) and nothing nearer binds it: with its candidates and their `%use`s. */
  def overloadedHead(c: Cxt, t: Tree): Option[(Ident, List[(Int, Span)])] =
    def head(t: Tree): Tree = t match
      case Apply(f, _) => head(f)
      case other => other
    if state.opened.isEmpty then None
    else
      head(t) match
        case id @ Ident(n) if !c.scope.contains(n) && !state.bodyDeclared(n) => overloadedName(n).map(id -> _)
        case _ => None

  /** The head of the type of `id` after `k` explicit arguments and the implicit arguments around them:
   *  `None` if `id` takes fewer than `k` explicit arguments (its type ends in a known head that is not a
   *  function), else the head (unknown if the type stops at an unknown head, which may still be one). */
  private def resultAfter(id: Int, k: Int): Option[Option[Shape]] =
    var ty = globals(id).ty
    var l = 0
    var left = k
    var out: Option[Option[Shape]] = None
    var more = true
    while more do
      force(ty) match
        case Val.Pi(_, i, _, cl) if i == Icit.Impl || left > 0 =>
          if i == Icit.Expl then left -= 1
          ty = inst(cl, Val.local(l))
          l += 1
        case other =>
          val s = bindingShape(other)
          // meta code of an object function (`⇑(A -> rel)`) is applied too (spliced)
          out = if left == 0 then Some(s) else if s.isEmpty || s.contains(Shape.Code) then Some(None) else None
          more = false
    out

  /** The head of the first explicit domain of `id`'s type. */
  private def firstDomain(id: Int): Option[Shape] =
    var ty = globals(id).ty
    var l = 0
    while true do
      force(ty) match
        case Val.Pi(_, Icit.Impl, _, cl) =>
          ty = inst(cl, Val.local(l))
          l += 1
        case Val.Pi(_, _, a, _) => return bindingShape(a)
        case _ => return None
    None

  /** A use of an overloaded opened name ([[overloadedHead]]), `n` or `n a₁ … aₖ`, with the expected type
   *  if known (#186 P9e): the candidate is chosen as an operator's binding is (P2b), by the heads of the
   *  types alone. First the head of each candidate's result after the `k` explicit arguments is compared
   *  with the expected type's (a candidate that takes fewer explicit arguments never fits); if several
   *  remain, the first argument is inferred, once, and the head of its type compared with each one's first
   *  explicit domain. It is an error if several fit (E0932) or none does (E0933). The result is the
   *  application with the chosen constant at its head, still to be elaborated (`Left`), or, if the first
   *  argument was inferred to choose, elaborated with that argument (`Right`). The name's position refers
   *  to the chosen constant (hover, definition). */
  def resolveOpened(c: Cxt, t: Tree, expected: Option[Val]): Either[Tree, (Tm, Val, Stage)] =
    val (head, all) = overloadedHead(c, t).getOrElse(throw Impossible(s"not an overloaded name: $t"))
    val n = head.name
    val (_, args) = TreeOps.flattenApp(t)
    val positional = args.filterNot(_.isInstanceOf[NamedArg])
    val ids = all.map(_._1)
    val uses = all.map(_._2)
    val exp = expected.flatMap(shape)
    val byResult = ids.filter(id => resultAfter(id, positional.length).exists(r => fits(r, exp)))
    def noneFits(operand: Option[Val]): Nothing =
      fail(OperatorProblem.NoNameFits(
        n,
        candidates(ids),
        operand.map(show(c, _)),
        expected.map(show(c, _)),
        positional.length,
        head.span,
        uses
      ))
    def ambiguous(fitting: List[Int], operand: Option[String]): Nothing =
      fail(OperatorProblem.AmbiguousName(n, candidates(fitting), operand, head.span, uses))
    def choose(id: Int): Tree =
      state.used += id
      recordUse(head.span, id)
      SymRef(id, n)(head.span)
    byResult match
      case List(id) =>
        val ref = choose(id)
        Left(args.foldLeft(ref: Tree)((f, a) => Apply(f, a)(f.span.to(a.span))))
      case Nil => noneFits(None)
      case several =>
        positional.headOption match
          case None => ambiguous(several, None)
          case Some(first) =>
            // the first argument decides: inferred once, and passed on to what it chooses
            val (ft, fty) = inferS(c, first, Stage.S1)
            val (at, aty, _) = insert(c, first.span, (ft, fty, Stage.S1))
            val s = shape(aty)
            several.filter(id => fits(firstDomain(id), s)) match
              case List(id) => Right(applyOpened(c, choose(id), args, at, aty))
              case Nil => noneFits(Some(aty))
              case more => ambiguous(more, s.map(_ => show(c, aty)))

  /** `f {x := e}… a₁ … aₖ` for the chosen constant `f`, with `a₁` already elaborated as `(at, aty)`. */
  private def applyOpened(c: Cxt, ref: Tree, args: List[Tree], at: Tm, aty: Val): (Tm, Val, Stage) =
    val (named, positional) = args.span(_.isInstanceOf[NamedArg])
    val f0 = named.foldLeft(ref)((f, a) => Apply(f, a)(f.span.to(a.span)))
    var (ft, fty, fs) = insertAll(c, f0.span, infer(c, f0))
    recordTyped(c, ref.span, ft, fty, fs, checked = false)
    val first = positional.head
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, cl) =>
        val (a, av) = core.anonymously {
          val a = coe(c, first.span, at, aty, Stage.S1, dom, Stage.S1)
          (a, ev(c, a))
        }
        ft = Tm.App(ft, a, Icit.Expl)
        fty = inst(cl, av)
      case other => throw Impossible(s"the chosen ${hugin.syntax.Printer.show(ref)} takes no explicit argument at ${show(c, other)}")
    var f: Tree = Apply(f0, first)(f0.span.to(first.span))
    positional.tail.foreach { a =>
      val r = insertAll(c, f.span, (ft, fty, fs))
      val span = f.span.to(a.span)
      val r2 = inferPositionalApp(c, f, a, span, r._1, r._2, r._3)
      ft = r2._1; fty = r2._2; fs = r2._3
      f = Apply(f, a)(span)
    }
    (ft, fty, fs)

  // ------------------------------------------------------------------ patterns

  /** `p op q` in a pattern, for a binding of `op` in scope: the constructor it denotes applied to `p` and
   *  `q`, chosen by the expected type (Agda's and Haskell's infix constructors in patterns). A binding to
   *  a function is not a pattern: a pattern is built from constructors. */
  def operatorPattern(t: Infix, expected: Option[Val]): Tree =
    val all = visibleOperators(t.op)
    val exp = expected.flatMap(shape)
    val ctors = all.filter(id => isConstructor(id) && fits(signature(id).result, exp))
    ctors match
      case List(id) =>
        recordUse(t.opSpan, id)
        state.used += id
        val head = SymRef(id, globals(id).name)(t.opSpan)
        Apply(Apply(head, t.lhs)(t.lhs.span.to(t.opSpan)), t.rhs)(t.span)
      case Nil => fail(OperatorProblem.NotAPattern(t.op, all.map(globals(_).name), t.opSpan))
      case several => fail(OperatorProblem.Ambiguous(t.op, candidates(several), None, t.opSpan))

  // ------------------------------------------------------------------ the directive

  /** `%infix op f.` (once the declarations are elaborated): `f` must be a meta constant of the file applied
   *  to two explicit arguments. A name whose declaration failed is not reported again. */
  def elabOperatorBinding(op: String, opSpan: Span, f: Ident): Unit =
    scope.get(f.name) match
      case Some(id) =>
        recordUse(f.span, id)
        val g = globals(id)
        if g.stage != Stage.S1 then fail(DirectiveProblem.NotBindable(op, f.name, "an object constant", f.span))
        if !bindable(id) then fail(DirectiveProblem.NotBindable(op, f.name, "it takes fewer than two explicit arguments", f.span))
        recordUse(opSpan, id)
      case None if state.declaredHere(f.name) || state.erroneous(f.name) => // its declaration failed (reported there)
      case None =>
        // a name of another file (opened by `%use`, or of the prelude)
        resolve(Cxt.empty, f.name, f.span)
        fail(DirectiveProblem.NotBindable(op, f.name, "not declared in this file", f.span))
