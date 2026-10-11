package hugin.core
package elab

import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Quoted syntax as terms (reference: reflection): the data a quote `'( … )` denotes where a reflective
 *  type is expected, the implicit quotes of a directive's arguments, the meta values in the rules of a
 *  file that a module-wide directive reifies, and the meta lists `[ē]`, `e :: es`. */
trait QuoteTerms:
  self: Elaborator =>
  import core.*

  // ---------------------------------------------------------------- implicit quotes

  /** The arguments of directives (by identity): at a parameter of a reflective type (other than a list),
   *  an argument is object syntax, read as if it were quoted (`%input edge.`, `%terminates N (r N).`). */
  private val implicitlyQuoted = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Tree, java.lang.Boolean]())

  def quoteImplicitly(t: Tree): Tree =
    implicitlyQuoted.add(t)
    t

  /** The kind `t` is implicitly quoted at, if it is a directive's argument expected of type `ty`. A
   *  declaration or a reference to a constant is a name: other arguments there are elaborated as they are
   *  (so that `%input 3.` is a mismatch of types). */
  def implicitQuote(t: Tree, ty: Val): Option[RKind] =
    if t.isInstanceOf[Quote] || !implicitlyQuoted.contains(t) then None
    else if quotedIndex(ty).isDefined then Some(RKind.Term) // a term of a known type
    else
      reflectiveKind(ty).filter {
        case RKind.List(_) => false
        case RKind.Decl | RKind.Sym => nameLike(t)
        case _ => true
      }

  private def nameLike(t: Tree): Boolean = t match
    case Parens(i) => nameLike(i)
    case _: Ident | _: Select | _: RuleRef | _: SpliceE => true
    case _ => false

  // ---------------------------------------------------------------- expressions

  /** The quote `t` (or implicitly quoted syntax) checked against the reflective type of kind `k`: its
   *  data. */
  def reify(c: Cxt, t: Tree, k: RKind, at: Option[Val] = None): Tm =
    val q = t match
      case qt: Quote => quotedContent(c, qt, k)
      case _ => quoted(c, t, k, Nil)
    val data = reifyQ(c, q)
    // the rules of the file a module-wide directive reifies were checked as rules
    if !reifyingRules then checkQuoted(c, q, k, at)
    data

  /** E0919: a quote where the expected type `a` is not reflective (or not known). */
  def quoteWithoutType(c: Cxt, qt: Tree, a: Option[Val]): Nothing =
    val shown = a.map(force).collect { case v if !v.isInstanceOf[Val.Flex] => show(c, v) }
    fail(ReflectionProblem.QuoteWithoutType(shown, qt.span))

  private def reifyQ(c: Cxt, q: Q): Tm = q match
    case h @ Q.Hole(x, RKind.Term, _) => termHole(c, x, h)
    case Q.Hole(x, k, _) => check(c, x, ev(c, kindType(k)), Stage.S1)
    case Q.EntryHole(x, k, sp) => entryHole(c, x, k, sp)
    case Q.SeqHole(_, _, sp) => fail(ReflectionProblem.MisplacedSequenceHole(sp))
    case Q.HigherOrder(f, args, k, sp) =>
      val r = reflective(sp)
      val fty = args.foldRight(kindType(k))((_, acc) => Tm.Pi("_", Icit.Expl, Tm.Global(r.term), acc))
      args.foldLeft(check(c, f, eval(Nil, fty), Stage.S1))((acc, a) => Tm.App(acc, reifyQ(c, a), Icit.Expl))
    case Q.Con(n, args, located, sp) =>
      val t = con(n, args.map(reifyQ(c, _))*)
      if located then Tm.loc(sp, t) else t
    case Q.QList(elems, k, _) =>
      listData(
        kindType(k),
        elems.map {
          case Q.SeqHole(x, k2, _) => Right(check(c, x, ev(c, kindType(RKind.List(k2))), Stage.S1))
          case e => Left(reifyQ(c, e))
        }
      )
    case Q.Var(n, sp) => Tm.loc(sp, con("tvar", Tm.Lit(Literal.StrL(n), Stage.S1)))
    case Q.Bound(i, sp) => Tm.loc(sp, con("tbound", indexData(i)))
    case Q.Wild(sp) => Tm.loc(sp, con("twild"))
    case Q.QLit(l, _) => Tm.Lit(l, Stage.S1)
    case Q.SymC(id, sp) => Tm.loc(sp, Tm.Quote(Tm.Global(id)))
    case Q.SymTm(tm, sp) => Tm.loc(sp, tm)
    case Q.Raw(tm, _) => tm

  /** A hole `$x` at a term: `x` of type `term`, or a meta value of a base or shared type, as its
   *  reification (`T.reify`, `tint`, …; [[Liftings.reifyCode]]). */
  private def termHole(c: Cxt, x: Tree, hole: Q): Tm =
    val term = ev(c, kindType(RKind.Term))
    val inferred =
      try Some(undoOnFailure(insert(c, x.span, infer(c, x))))
      catch case _: ElabError => None
    inferred.foreach((tm, ty, _) => recordHole(c, hole, tm, ty))
    inferred match
      case Some((tm, ty, Stage.S1)) if reflectiveKind(ty).isEmpty && reifyCode(c, tm, ty).isDefined => reifyCode(c, tm, ty).get
      case Some((tm, ty, s)) => coe(c, x.span, tm, ty, s, term, Stage.S1)
      case None => check(c, x, term, Stage.S1)

  /** A whole entry `$x` of kind `k` (a rule or an item): `x` of that kind, or a formula (the fact `x`), or
   *  for an item a rule. */
  private def entryHole(c: Cxt, x: Tree, k: RKind, sp: Span): Tm =
    val inferred =
      try Some(undoOnFailure(insert(c, x.span, infer(c, x))))
      catch case _: ElabError => None
    def fact(f: Tm) = con("horn", listData(kindType(RKind.Formula), List(Left(f))), listData(kindType(RKind.Formula), Nil))
    inferred match
      case Some((tm, ty, Stage.S1)) if quotedIndex(ty).isDefined && k != RKind.Term =>
        // a typed atom: the fact it describes
        val f = coe(c, x.span, tm, ty, Stage.S1, ev(c, kindType(RKind.Formula)), Stage.S1)
        if k == RKind.Rule then Tm.loc(sp, fact(f)) else con("irule", Tm.loc(sp, fact(f)))
      case Some((tm, ty, Stage.S1)) =>
        (reflectiveKind(ty), k) match
          case (Some(RKind.Formula), RKind.Rule) => Tm.loc(sp, fact(tm))
          case (Some(RKind.Formula), _) => con("irule", Tm.loc(sp, fact(tm)))
          case (Some(RKind.Rule), RKind.Item) => con("irule", tm)
          case _ => coe(c, x.span, tm, ty, Stage.S1, ev(c, kindType(k)), Stage.S1)
      case _ => check(c, x, ev(c, kindType(k)), Stage.S1)

  // ---------------------------------------------------------------- meta values in reified rules (#79)

  /** Whether the rules of the file are being reified for a module-wide directive: their meta subterms
   *  are evaluated, and their values become data ([[metaValue]]). */
  private var reifyingSource = false

  def reifyingRules: Boolean = reifyingSource

  def reifyingFile[A](f: => A): A =
    val saved = reifyingSource
    reifyingSource = true
    try f
    finally reifyingSource = saved

  /** Whether `t` (a term or formula of a rule of the file being reified) is meta code: an application
   *  whose head is not an object constant (nor a hole), such as a meta constant used as object code. */
  def metaValueAt(c: Cxt, t: Tree): Boolean = reifyingSource && (TreeOps.flattenApp(t)._1 match
    case h @ (_: Ident | _: Select) => symbolOf(c, h).isEmpty && !TreeOps.headName(h).exists(n => state.erroneous(n.name))
    case _ => false
  )

  /** The closed meta term `t` of the file, evaluated: data of kind `k` (a term or formula) if it has that
   *  type; for a term, a base value as a literal and object code as its syntax. */
  def metaValue(c: Cxt, t: Tree, k: RKind): Q =
    val notSyntax = ReflectionProblem.NotObjectSyntax(kindName(k), t.span)
    val (tm, ty, _) =
      try
        undoOnFailure {
          val r = insert(c, t.span, infer(c, t))
          settleLiterals() // the value is computed now: its literals take their types (reference: meta/functions)
          r
        }
      catch case _: ElabError => fail(notSyntax)
    val v = eval(c.env, zonk(c.env, c.lvl, tm))
    if reflectiveKind(ty).contains(k) then Q.Raw(quote(c.lvl, v), t.span)
    else if k == RKind.Term then termData(v).map(d => Q.Raw(Tm.loc(t.span, d), t.span)).getOrElse(fail(notSyntax))
    else fail(notSyntax)

  /** A value used as an object term as `term` data: literals (also persisted), object constants applied
   *  to such terms (implicit arguments dropped; a value of a shared type is its object constructors, as
   *  its `reify` gives), object arithmetic. */
  private def termData(v: Val): Option[Tm] = force(v) match
    case Val.Lit(l, _) =>
      val ctor = l match
        case Literal.IntL(_) => "tint"
        case Literal.FloatL(_) => "tfloat"
        case Literal.StrL(_) => "tstr"
      Some(con(ctor, Tm.Lit(l, Stage.S1)))
    case Val.Persist(x) => termData(x)
    case Val.Quote(x) => termData(x)
    case Val.Obj(ObjForm.Loc(_), List(x)) => termData(x)
    case Val.Rigid(Head.Glob(id), spine) if isObjectConstant(sharedAt(id, Stage.S0)) && spine.forall(_.isInstanceOf[Elim.EApp]) =>
      val args = spine.reverse.collect { case Elim.EApp(a, Icit.Expl) => termData(a) }
      Option.when(args.forall(_.isDefined))(
        con("tapp", Tm.Quote(Tm.Global(sharedAt(id, Stage.S0))), listData(kindType(RKind.Term), args.map(a => Left(a.get))))
      )
    case Val.Arith(op, a, b, Stage.S0) =>
      for x <- termData(a); y <- termData(b) yield con("tarith", con(arithCtor(op)), x, y)
    case Val.Negate(a, Stage.S0) => termData(a).map(con("tneg", _))
    case _ => None

  // ---------------------------------------------------------------- meta lists

  /** `[ē]` or `e :: es` against `ty` (a list type, or unknown). */
  def checkList(c: Cxt, t: Tree, ty: Val): Tm =
    val r = reflective(t.span)
    val elem = listElement(ty).getOrElse {
      val m = ev(c, freshType(c, Stage.S1, t.span, "the type of the list's elements"))
      unifyAt(c, t.span, ty, listOf(m))
      m
    }
    val elemTm = quote(c.lvl, elem)
    t match
      case ListLit(es) =>
        listData(elemTm, es.map(e => Left(check(c, e, elem, Stage.S1))))
      case ConsE(h, tl) =>
        Tm.App(
          Tm.App(Tm.App(Tm.Global(r.cons), elemTm, Icit.Impl), check(c, h, elem, Stage.S1), Icit.Expl),
          check(c, tl, listOf(elem), Stage.S1),
          Icit.Expl
        )
      case other => unsupported(other)

  /** A list with an inferred element type. */
  def inferList(c: Cxt, t: Tree): (Tm, Val, Stage) =
    reflective(t.span)
    val m = ev(c, freshType(c, Stage.S1, t.span, "the type of the list's elements"))
    (checkList(c, t, listOf(m)), listOf(m), Stage.S1)
