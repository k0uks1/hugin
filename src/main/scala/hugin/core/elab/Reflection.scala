package hugin.core
package elab

import hugin.obj.{ArithOp, CmpOp}
import hugin.syntax.{AggKind, Literal, Printer, Tree}
import hugin.syntax.Trees.*
import hugin.util.*

/** Reflection (reference: reflection): reflective data turned back into object code. The data must be closed (it
 *  is evaluated during elaboration); it becomes surface syntax whose object constants are already
 *  resolved ([[SymRef]]) and which is elaborated and checked like hand-written code, so reflected code is
 *  re-checked by the core and then by the object level (typing, stratification, termination).
 *
 *  - An item `$e.` with `e` of type `Rule`, `Item`, `List Rule` or `Module` (`List Item`) stands for the
 *    rules and queries `e` evaluates to.
 *  - In object code, a meta value of type `Formula` or `Term` (with or without `$`) stands for the formula
 *    or term; its variables are the item's variables of the same names.
 *
 *  Generated syntax has the positions of the quoted syntax the data was reified from (data built with
 *  the constructors directly has the position of the reflecting item or splice), and its diagnostics
 *  note the reflection ("in code reflected by `$rules`"). The variable an aggregate binds gets a fresh
 *  name (`V#1`). */
trait Reflection:
  self: Elaborator =>
  import core.*

  /** How variables are generated: as rule variables (`VarRef`, bound by the generated item) or as the
   *  variables of the enclosing item's context `c` (an expression). */
  private final case class Target(c: Option[Cxt], fallback: Span):
    private var counter = 0
    def fresh(hint: Name): Name =
      counter += 1
      s"$hint#$counter"

  /** `$e.` (also `$f a₁ … aₙ.` for `$(f a₁ … aₙ).`): if `e` has the type of reflected items, elaborates
   *  the items it evaluates to and returns true. */
  def elabSpliceItem(r: Rule): Boolean =
    spliced(r).flatMap(e => tentatively(spliceKind(e)).map((e, _))) match
      case Some((e, k)) =>
        elabSplice(r, e, k)
        true
      case None => false

  /** Whether `r` has the shape of an item `$e.` whose `e` has the type of reflected items. */
  def isSpliceItem(r: Rule): Boolean = spliced(r).exists(e => tentatively(spliceKind(e)).isDefined)

  private def spliced(r: Rule): Option[Tree] = r match
    case Rule(None, List(head), None) if reflectiveGlobals.isDefined =>
      hugin.syntax.TreeOps.flattenApp(head) match
        case (SpliceE(f), args) => Some(args.foldLeft(f)((g, a) => Apply(g, a)(g.span.to(a.span))))
        case _ => None
    case _ => None

  private def spliceKind(e: Tree): Option[RKind] = e match
    case Parens(i) => spliceKind(i)
    // a quote is reflected items (errors in it are reported when it is elaborated)
    case _: Quote => Some(RKind.List(RKind.Item))
    case _ =>
      try
        reflectiveKind(splicedData(e)._2).filter {
          case RKind.Rule | RKind.Item | RKind.List(RKind.Rule) | RKind.List(RKind.Item) => true
          case _ => false
        }
      catch case _: ElabError => None

  /** The data of `$e.` and its type: inferred; a quote (or a list that has no type of its own) is
   *  checked against `module`. */
  private def splicedData(e: Tree): (Tm, Val) =
    def inferred = insert(Cxt.empty, e.span, infer(Cxt.empty, e)) match
      case (tm, ty, _) => (tm, ty)
    def asModule =
      val ty = listOf(eval(Nil, kindType(RKind.Item)))
      (check(Cxt.empty, e, ty, Stage.S1), ty)
    e match
      case Parens(i) => splicedData(i)
      case _: Quote => asModule
      case _: ListLit =>
        try undoOnFailure(inferred)
        catch case _: ElabError => asModule
      case _ => inferred

  private def elabSplice(r: Rule, e: Tree, k: RKind): Unit =
    val (tm, _) = splicedData(e)
    val frame = TraceFrame(s"in code reflected by `$$${Printer.show(e)}`", r.span)
    val closed = zonk(Nil, 0, tm)
    recordPart(ModulePart.Data(closed, k, frame, directive = false))
    items ++= elabReflected(closed, k, frame, r.span)

  /** The items that the closed data `tm` of kind `k` describes, elaborated at `span` in the frame `frame`
   *  (the splice or directive that reflects them). */
  def elabReflected(tm: Tm, k: RKind, frame: TraceFrame, span: Span): List[CoreItem] =
    reflectItems(eval(Nil, tm), k, Target(None, span)).map(g => elabGenerated(g, Origin(List(frame))))

  /** A generated rule or query (without warnings for its variables); its diagnostics note `origin`. */
  def elabGenerated(g: Item, origin: Origin): CoreItem =
    val item = inOrigin(origin) {
      g match
        case rule: Rule => ruleItem(Cxt.empty, rule, lint = false)
        case q: Query => queryItem(Cxt.empty, q)
        case other => throw Impossible(s"reflected $other")
    }
    withOrigin(item, origin)

  /** The elements of a closed list value. */
  def listValues(v: Val, span: Span): List[Val] = elements(v, span, Target(None, span)).map(_._1)

  /** Object code for the meta value `tm : Formula` or `Term` in `c`, elaborated against `expected`
   *  (`prop` for a formula); for a term without an expected type, inferred. */
  def reflectCode(c: Cxt, tm: Tm, k: RKind, span: Span, expected: Option[Val]): (Tm, Val) =
    val frame = TraceFrame(s"in code reflected here", span)
    val target = Target(Some(c), span)
    val tree = k match
      case RKind.Formula => formula(ev(c, tm), span, Nil, target)
      case _ => term(ev(c, tm), span, Nil, target)
    inFrame(frame) {
      (k, expected) match
        case (_, Some(ty)) => (check(c, tree, ty, Stage.S0), ty)
        case (RKind.Formula, None) => (check(c, tree, Val.PropT, Stage.S0), Val.PropT)
        case (_, None) => inferS(c, tree, Stage.S0)
    }

  private def inFrame[A](frame: TraceFrame)(f: => A): A = inOrigin(Origin(List(frame)))(f)

  private def inOrigin[A](o: Origin)(f: => A): A =
    try f
    catch
      case e: ElabError if e.diag.origin.isEmpty && !o.isEmpty => throw ElabError(e.diag.withOrigin(o), e.unresolved, e.silent)

  private def withOrigin(item: CoreItem, o: Origin): CoreItem = item match
    case r: CoreItem.RuleItem => r.copy(origin = o)
    case q: CoreItem.QueryItem => q.copy(origin = o)
    case other => other

  // ---------------------------------------------------------------- data to syntax

  /** The value without its positions, and the innermost position (or `sp`). Positions in another file
   *  than `sp`'s (the syntax of a directive of the prelude or of an imported file) are not used: code is
   *  shown where it is generated, at the data it came from or at the reflecting item. */
  private def peel(v: Val, sp: Span): (Val, Span) = force(v) match
    case Val.Obj(ObjForm.Loc(s), List(x)) => peel(x, if s.exists && (!sp.exists || s.source.path == sp.source.path) then s else sp)
    case other => (other, sp)

  private lazy val ctorNames: Map[Int, Name] = reflectiveGlobals.get.ctors.map(_.swap)

  /** A constructor application of reflective data: the constructor's name, explicit arguments, position. */
  private def ctorApp(v: Val, sp: Span, t: Target): (Name, List[Val], Span) =
    val (w, s) = peel(v, sp)
    w match
      case Val.Rigid(Head.Glob(id), spine) if ctorNames.contains(id) =>
        (ctorNames(id), spine.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }, s)
      case other => notClosed(other, s, t)

  private def notClosed(v: Val, s: Span, t: Target): Nothing =
    fail(ReflectionProblem.NotClosed(showValPlain(t.c.map(_.names).getOrElse(Nil), v), s))

  private def malformed(what: String, s: Span): Nothing = fail(ReflectionProblem.MalformedData(what, s))

  /** The elements of a list, with a loop down its spine (a module can have thousands of items, issue #88). */
  private def elements(v: Val, sp: Span, t: Target): List[(Val, Span)] =
    val out = List.newBuilder[(Val, Span)]
    var cur = v
    var at = sp
    var more = true
    while more do
      ctorApp(cur, at, t) match
        case ("nil", Nil, _) => more = false
        case ("cons", List(x, xs), s) =>
          out += ((x, s))
          cur = xs
          at = s
        case (_, _, s) => malformed("not a list", s)
    out.result()

  /** The rules and queries that the closed value `v` of kind `k` (`rule`, `item` or a `list` of them)
   *  describes, as syntax at `span` (where the data has no positions of its own). */
  def reflectedItems(v: Val, k: RKind, span: Span): List[Item] = reflectItems(v, k, Target(None, span))

  private def reflectItems(v: Val, k: RKind, t: Target): List[Item] = k match
    case RKind.List(e) => elements(v, t.fallback, t).flatMap((x, s) => reflectItems(x, e, t.copy(fallback = s)))
    case RKind.Rule => List(rule(v, t.fallback, t))
    case _ =>
      ctorApp(v, t.fallback, t) match
        case ("irule", List(r), s) => List(rule(r, s, t))
        case ("inamed", List(n, r), s) =>
          literal(n, s, t) match
            case Literal.StrL(name) if name.nonEmpty =>
              val rl = rule(r, s, t)
              List(Rule(Some(Ident(name)(s)), rl.heads, rl.body)(rl.span))
            case _ => malformed("a rule name that is not a name", s)
        case ("ierror", List(m), s) => fail(DirectiveProblem.Rejected(message(m, s, t), t.fallback))
        case ("irelation", List(sym, cols), s) =>
          declareRelation(sym, cols, s, t)
          Nil
        case ("iquery", List(fs), s) => List(Query(conj(elements(fs, s, t).map((f, fs2) => formula(f, fs2, Nil, t))).getOrElse(malformed(
            "an empty query",
            s
          )))(t.fallback))
        case (_, _, s) => malformed("not an item", s)

  /** `irelation S cols`: declares the derived constant `S` (pending since `derive` created it) as the
   *  relation over the columns `cols` (each a column of an object constant, with its label and type). */
  private def declareRelation(sym: Val, cols: Val, s: Span, t: Target): Unit =
    val id = symbolId(sym, s, t)
    val columns = elements(cols, s, t).map { (c, cs) =>
      ctorApp(c, cs, t) match
        case ("colof", List(of, k), s2) => (symbolId(of, s2, t), index(k, s2, t))
        case (_, _, s2) => malformed("not a column", s2)
    }
    declareDerived(id, columns, t.fallback).foreach(malformed(_, s))

  private def symbolId(v: Val, s: Span, t: Target): Int = peel(v, s)._1 match
    case Val.Quote(x) =>
      peel(x, s)._1 match
        case Val.Rigid(Head.Glob(id), Nil) => id
        case other => notClosed(other, s, t)
    case other => notClosed(other, s, t)

  private def rule(v: Val, sp: Span, t: Target): Rule = ctorApp(v, sp, t) match
    case ("horn", List(hs, bs), s) =>
      val heads = elements(hs, s, t).map((h, s2) => formula(h, s2, Nil, t))
      if heads.isEmpty then malformed("a rule without heads", s)
      Rule(None, heads, conj(elements(bs, s, t).map((b, s2) => formula(b, s2, Nil, t))))(t.fallback)
    case (_, _, s) => malformed("not a rule", s)

  private def conj(fs: List[Tree]): Option[Tree] = fs.reduceLeftOption((a, b) => Conj(a, b)(a.span.to(b.span)))

  private def formula(v: Val, sp: Span, names: List[Name], t: Target): Tree = ctorApp(v, sp, t) match
    case ("fatom", List(sym, ts), s) => application(sym, ts, s, names, t)
    case ("fcmp", List(op, a, b), s) => Infix(cmpOp(op, s, t).show, term(a, s, names, t), term(b, s, names, t))(s, s)
    case ("fnot", List(f), s) => Not(formula(f, s, names, t))(s)
    case ("fconj", List(f, g), s) => Conj(formula(f, s, names, t), formula(g, s, names, t))(s)
    case ("fdisj", List(f, g), s) => Disj(formula(f, s, names, t), formula(g, s, names, t))(s)
    case ("fagg", List(k, x, tm, f), s) =>
      val v = t.fresh("V")
      val agg = Agg(aggKind(k, s, t), term(tm, s, v :: names, t), formula(f, s, v :: names, t))(s)
      Infix("=", term(x, s, names, t), agg)(s, s)
    case (_, _, s) => malformed("not a formula", s)

  private def term(v: Val, sp: Span, names: List[Name], t: Target): Tree = ctorApp(v, sp, t) match
    case ("tvar", List(x), s) =>
      literal(x, s, t) match
        case Literal.StrL(n) if n.nonEmpty => variable(n, s, t)
        case _ => malformed("a variable without a name", s)
    case ("tbound", List(i), s) => names.lift(index(i, s, t)).map(variable(_, s, t)).getOrElse(malformed("a dangling bound variable", s))
    case ("twild", Nil, s) => Wildcard()(s)
    case ("tint" | "tfloat" | "tstr", List(l), s) => Lit(literal(l, s, t))(s)
    case ("tapp", List(sym, ts), s) => application(sym, ts, s, names, t)
    case ("tarith", List(op, a, b), s) => Infix(arithOp(op, s, t).show, term(a, s, names, t), term(b, s, names, t))(s, s)
    case ("tneg", List(a), s) => Neg(term(a, s, names, t))(s)
    case (_, _, s) => malformed("not a term", s)

  private def variable(n: Name, s: Span, t: Target): Tree =
    variablesUsed.foreach(_ += n)
    t.c match
      case Some(c) if !c.scope.contains(n) => NamedVar(n)(s)
      case _ => VarRef(n)(s)

  private var variablesUsed: Option[scala.collection.mutable.Set[Name]] = None

  /** Runs `f`, adding the names of the object variables that code reflected by it uses to `used`. */
  def reflectingVariables[A](used: scala.collection.mutable.Set[Name])(f: => A): A =
    val saved = variablesUsed
    variablesUsed = Some(used)
    try f
    finally variablesUsed = saved

  private def application(sym: Val, ts: Val, s: Span, names: List[Name], t: Target): Tree =
    val head: Tree = peel(sym, s)._1 match
      case Val.Quote(x) =>
        peel(x, s)._1 match
          case Val.Rigid(Head.Glob(id), Nil) if globals(id).pending =>
            malformed(s"`${globals(id).name}` is not declared (a constant from `derive` is declared by an item `irelation`)", s)
          case Val.Rigid(Head.Glob(id), Nil) => SymRef(id, globals(id).name)(s)
          case other => notClosed(other, s, t)
      case other => notClosed(other, s, t)
    elements(ts, s, t).foldLeft(head)((f, a) => Apply(f, term(a._1, a._2, names, t))(s))

  private def message(v: Val, s: Span, t: Target): String = literal(v, s, t) match
    case Literal.StrL(m) => m
    case other => other.show

  private def literal(v: Val, s: Span, t: Target): Literal = peel(v, s)._1 match
    case Val.Lit(l, _) => l
    case other => notClosed(other, s, t)

  private def index(v: Val, s: Span, t: Target): Int = ctorApp(v, s, t) match
    case ("izero", Nil, _) => 0
    case ("isuc", List(i), s2) => index(i, s2, t) + 1
    case (_, _, s2) => malformed("not an index", s2)

  private def enumCtor(v: Val, s: Span, t: Target): Name = ctorApp(v, s, t)._1

  private def cmpOp(v: Val, s: Span, t: Target): CmpOp =
    val n = enumCtor(v, s, t)
    cmpCtor.find(_._2 == n).map(_._1).getOrElse(malformed("not a comparison", s))

  private def arithOp(v: Val, s: Span, t: Target): ArithOp =
    val n = enumCtor(v, s, t)
    arithCtor.find(_._2 == n).map(_._1).getOrElse(malformed("not an arithmetic operator", s))

  private def aggKind(v: Val, s: Span, t: Target): AggKind =
    val n = enumCtor(v, s, t)
    aggCtor.find(_._2 == n).map(_._1).getOrElse(malformed("not an aggregate", s))
