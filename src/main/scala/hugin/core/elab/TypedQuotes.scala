package hugin.core
package elab

import hugin.core.objtype.*
import hugin.syntax.AggKind
import hugin.util.Span

/** Typed reflection (reference: reflection): `quoted A`, a `term` with the object type `A` as a phantom
 *  index, and the object typing of quotes. The content of a quote is read once ([[Q]]); that reading is
 *  checked as object code ([[ObjCheck]]) where the quote is written, with its holes at their types (a
 *  hole of type `quoted A` at `A`, a `term` at an unknown type, a value of a base or shared type at the
 *  type it lifts to), and is the data the quote denotes. Holes of quoted patterns at a column of a known
 *  type bind `quoted` terms ([[QuotedPatterns]]). The index is not checked when data is taken apart:
 *  reflected data is elaborated again in any case. */
trait TypedQuotes:
  self: Elaborator =>
  import core.*

  /** The object type `A` of `quoted A`. */
  def quotedIndex(ty: Val): Option[Val] = typed("quoted").flatMap { q =>
    forceData(ty) match
      case Val.Rigid(Head.Glob(id), List(Elim.EApp(a, _))) if id == q => Some(a)
      case _ => None
  }

  /** `quoted`, `qterm` and `raw` of the prelude (or of the file, without the prelude). */
  def typedGlobal(n: Name): Option[Int] = typed(n)

  private def typed(n: Name): Option[Int] = file.parent.get(n).orElse(if file.parent.isEmpty then scope.get(n) else None)

  /** `raw {A} t`: the term of `t : quoted A`. */
  def rawTerm(c: Cxt, a: Val, t: Tm): Tm =
    Tm.App(Tm.App(Tm.Global(typed("raw").get), quote(c.lvl, a), Icit.Impl), t, Icit.Expl)

  /** `qterm {A} d`: data as a term of type `A`. */
  def qtermOf(c: Cxt, a: Val, d: Tm): Tm =
    Tm.App(Tm.App(Tm.Global(typed("qterm").get), quote(c.lvl, a), Icit.Impl), d, Icit.Expl)

  /** The coercions of `quoted`: to `term` (forgetting the index), and covariantly in the index. */
  def coeQuoted(c: Cxt, t: Tm, a: Val, a2: Val): Option[Option[Tm]] =
    (quotedIndex(a), quotedIndex(a2)) match
      case (Some(x), _) if reflectiveKind(a2).contains(RKind.Term) => Some(Some(rawTerm(c, x, t)))
      case (Some(x), Some(y)) =>
        try undoOnFailure(unify(c.lvl, x, y))
        catch case e: UnifyError => if !liftSubtype(c, x, y) then throw e
        Some(None)
      case _ => None

  // ---------------------------------------------------------------- the types of holes

  private val holeTypes = java.util.IdentityHashMap[Q, OTy]()

  /** The holes whose value is a `quoted A` of a known type, by the name of the meta variable they refer
   *  to: the occurrences of one such hole in the body of a quoted rule are one object variable. */
  private val quotedHoles = java.util.IdentityHashMap[Q, String]()

  /** Records the object type of the hole `q` (from the type `ty` of its meta value). */
  def recordHole(c: Cxt, q: Q, tm: Tm, ty: Val): Unit =
    val env = objEnv(c)
    val t = quotedIndex(ty) match
      case Some(a) =>
        val o = env.oty(a)
        holeVariable(c, q).filter(_ => !o.vague).foreach(n => quotedHoles.put(q, n))
        o
      case None if reflectiveKind(ty).isDefined => OTy.Unknown
      case None =>
        try undoOnFailure(liftCode(c, tm, ty)).map((_, o) => env.oty(o)).getOrElse(OTy.Unknown)
        catch case _: ElabError => OTy.Unknown
    holeTypes.put(q, t)

  /** The name of the meta variable a hole `$X` refers to (in the context of its quote). */
  private def holeVariable(c: Cxt, q: Q): Option[String] =
    import hugin.syntax.Trees.{Parens, VarRef}
    def go(t: hugin.syntax.Tree): Option[String] = t match
      case Parens(i) => go(i)
      case VarRef(n) => Some(n)
      case _ => None
    q match
      case Q.Hole(t, _, _) => go(t)
      case _ => None

  // ---------------------------------------------------------------- checking a quote

  /** Checks the quoted content `q` of kind `k` in `c` (at the object type `at` for a quoted term); fails at
   *  the first problem. */
  def checkQuoted(c: Cxt, q: Q, k: RKind, at: Option[Val] = None): Unit =
    val env = objEnv(c)
    val reader = QuoteReader(c, env)
    val problems = k match
      case RKind.Term =>
        val t = reader.term(q, Nil)
        ObjCheck(ObjTypes(env), Nil, Nil, List((t, at.map(env.oty).getOrElse(OTy.Unknown), "the quoted term"))).run()._1
      case RKind.Formula => ObjCheck(ObjTypes(env), Nil, reader.body(q)).run()._1
      case RKind.Rule | RKind.Item => reader.entry(q)
      case RKind.List(RKind.Rule | RKind.Item) =>
        q match
          case Q.QList(es, _, _) => es.flatMap(reader.entry)
          case _ => Nil
      case _ => Nil
    problems.headOption.foreach(p => fail(p))

  /** Reads analysed quote content as object code for [[ObjCheck]]. */
  private final class QuoteReader(c: Cxt, env: ObjEnv):
    private var wild = 0
    private val types = ObjTypes(env)

    /** The typed holes that occur more than once in the body of the scope being read: they are read as
     *  one variable `$X`, bounded by the hole's type (reference: reflection). */
    private var shared: Set[String] = Set.empty
    private var bounds: List[OFormula] = Nil

    private def children(q: Q): List[Q] = q match
      case Q.Con(_, args, _, _) => args
      case Q.QList(es, _, _) => es
      case Q.HigherOrder(_, args, _, _) => args
      case _ => Nil

    private def typedHoles(q: Q): List[String] =
      Option(quotedHoles.get(q)).toList ++ children(q).flatMap(typedHoles)

    /** Reads the body `qs` of a scope with the typed holes it repeats as variables. */
    private def scoped(qs: List[Q])(read: => List[OFormula]): List[OFormula] =
      val saved = (shared, bounds)
      shared = qs.flatMap(typedHoles).groupBy(identity).collect { case (n, os) if os.length > 1 => n }.toSet
      bounds = Nil
      try
        val fs = read
        fs ++ bounds.reverse
      finally
        shared = saved._1
        bounds = saved._2

    private def fresh(prefix: String): String =
      wild += 1
      s"$prefix#q$wild"

    private def relation(q: Q): Option[RelInfo] = q match
      case Q.SymC(id, _) => env.relInfo(OHead.G(id), Nil)
      case Q.SymTm(tm, _) =>
        try env.head(ev(c, tm)).flatMap((h, as) => env.relInfo(h, as))
        catch case _: Exception => None
      case _ => None

    private def elems(q: Q): List[Q] = q match
      case Q.QList(es, _, _) => es
      case _ => Nil

    /** A formula as the body of a scope. */
    def body(q: Q): List[OFormula] = scoped(List(q))(formulas(q, Nil))

    def entry(q: Q): List[hugin.util.diagnostics.Problem] = q match
      case Q.Con("irule" | "inamed", args, _, _) => args.lastOption.toList.flatMap(entry)
      case Q.Con("iquery", List(body), _, _) =>
        ObjCheck(types, Nil, scoped(List(body))(elems(body).flatMap(formulas(_, Nil)))).run()._1
      case Q.Con("horn", List(hs, body), _, _) =>
        val heads = elems(hs).flatMap(h => headTerm(h))
        ObjCheck(types, heads, scoped(List(body))(elems(body).flatMap(formulas(_, Nil)))).run()._1
      case _ => Nil

    private def headTerm(q: Q): Option[OTerm] =
      val saved = shared
      shared = Set.empty // a hole in a head may hold a term: it keeps its type there
      try
        q match
          case Q.Con("fatom", List(sym, args), _, sp) => Some(OTerm.App(relation(sym), elems(args).map(term(_, Nil)), sp))
          case _ => None
      finally shared = saved

    def term(q: Q, bound: List[String]): OTerm = q match
      case Q.Var(n, sp) => OTerm.Var(n, sp)
      case Q.Wild(sp) => OTerm.Var(fresh(hugin.obj.Var.WildPrefix), sp)
      case Q.Bound(i, sp) => OTerm.Var(bound.lift(i).getOrElse(fresh("#bound")), sp)
      case Q.Con("tint" | "tfloat" | "tstr", List(Q.QLit(l, _)), _, sp) => OTerm.Lit(l, sp)
      case Q.Con("tapp", List(sym, args), _, sp) => OTerm.App(relation(sym), elems(args).map(term(_, bound)), sp)
      case Q.Con("tarith", List(Q.Con(op, _, _, _), a, b), _, sp) =>
        arithOp(op).map(o => OTerm.Arith(o, term(a, bound), term(b, bound), sp)).getOrElse(OTerm.Code(OTy.Unknown, sp))
      case Q.Con("tneg", List(a), _, sp) => OTerm.Neg(term(a, bound), sp)
      case h @ Q.Hole(_, _, sp) =>
        val ty = Option(holeTypes.get(h)).getOrElse(OTy.Unknown)
        Option(quotedHoles.get(h)).filter(shared) match
          case Some(n) =>
            val v = OTerm.Var(s"$$$n", sp)
            if !bounds.exists { case OFormula.Expect(OTerm.Var(m, _), _, _, _) => m == s"$$$n"; case _ => false } then
              bounds = OFormula.Expect(v, ty, s"the type of `$$$n`", sp) :: bounds
            v
          case None => OTerm.Code(ty, sp)
      case other => OTerm.Code(OTy.Unknown, spanOf(other))

    def formulas(q: Q, bound: List[String]): List[OFormula] = q match
      case Q.Con("fatom", List(sym, args), _, sp) =>
        relation(sym).map(r => OFormula.Atom(r, elems(args).map(term(_, bound)), None, sp)).toList
      case Q.Con("fcmp", List(Q.Con(op, _, _, _), l, r), _, sp) =>
        cmpOp(op).map(o => OFormula.Cmp(o, term(l, bound), term(r, bound), sp)).toList
      case Q.Con("fnot", List(a), _, sp) => formulas(a, bound).map(OFormula.Not(_, sp))
      case Q.Con("fconj", List(a, b), _, _) => formulas(a, bound) ++ formulas(b, bound)
      case Q.Con("fdisj", List(a, b), _, sp) => List(OFormula.Disj(List(formulas(a, bound), formulas(b, bound)), sp))
      case Q.Con("fagg", List(Q.Con(op, _, _, _), x, t, body), _, sp) =>
        val res = term(x, bound) match
          case OTerm.Var(n, _) => n
          case _ => fresh("#agg")
        val inner = fresh("#bound") :: bound
        aggKind(op).map(k => OFormula.Agg(res, k, term(t, inner), formulas(body, inner), sp)).toList
      case _ => Nil

    private def spanOf(q: Q): Span = q match
      case Q.Con(_, _, _, s) => s
      case Q.Hole(_, _, s) => s
      case Q.HigherOrder(_, _, _, s) => s
      case Q.Raw(_, s) => s
      case _ => Span.NoSpan

  private def arithOp(ctor: String) = arithCtor.collectFirst { case (op, n) if n == ctor => op }
  private def cmpOp(ctor: String) = cmpCtor.collectFirst { case (op, n) if n == ctor => op }
  private def aggKind(ctor: String): Option[AggKind] = aggCtor.collectFirst { case (k, n) if n == ctor => k }
