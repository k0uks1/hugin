package hugin.core
package elab

import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Patterns of clauses: uppercase variables, `_`, constructors applied to patterns, nat literals. */
enum Pat:
  /** A pattern variable; `implicitBinder` for the name of an implicit binder of the function's type,
   *  which is in scope unless a pattern variable shadows it. */
  case PVar(name: Name, span: Span, implicitBinder: Boolean = false)
  case PWild(span: Span)
  case PCon(ctor: Int, args: List[Pat], span: Span)
  case PLit(n: Long, span: Span)

  /** A value of a type without constructors (a reference to an object constant, a meta literal): `key` is
   *  its closed normal form, as [[hugin.core.Matching.atomKey]] computes it. Only quoted patterns produce
   *  it (reference: reflection). */
  case PAtom(key: Tm, span: Span)

/** One clause `f p̄ = e.` (or a definition `f X̄ = e.` of a declared function), with its `where` block. */
final case class SurfaceClause(name: Ident, pats: List[Tree], rhs: Tree, span: Span, where: List[Item] = Nil)

trait Patterns:
  self: Elaborator =>
  import core.*

  /** The clause of an item, if it is one: `f p̄ = e.`, or `f X̄ = e.` for a declared meta constant. */
  def surfaceClause(item: Item): Option[SurfaceClause] = item match
    case Clause(lhs, rhs, where) =>
      TreeOps.flattenApp(lhs) match
        case (f: Ident, args) => Some(SurfaceClause(f, args, rhs, item.span, where))
        case (other, _) => fail(ClauseProblem.ClauseWithoutName(other.span))
    case d: Def if state.functionNames(d.name.name) =>
      val pats = d.params.map {
        case Param.VarParam(v) => v
        case Param.Typed(_, _, sp) => fail(ClauseProblem.TypedPattern(sp))
        case Param.Malformed(t) => syntaxError(t.span)
      }
      Some(SurfaceClause(d.name, pats, d.rhs, d.span))
    case _ => None

  /** A surface pattern, with the type it matches if that is known and closed: object syntax where a
   *  reflective type is expected is a quoted pattern ([[QuotedPatterns]]); list syntax is the prelude's
   *  `List`. */
  def pattern(t: Tree, expected: Option[Val] = None): Pat =
    expected.flatMap(reflectiveKind) match
      case Some(k) if k != RKind.Decl && k != RKind.Measure && quotedSyntax(t, k) => quotedPattern(t, k)
      case _ => plainPattern(t, expected)

  private def plainPattern(t: Tree, expected: Option[Val]): Pat = t match
    case Parens(i) => pattern(i, expected)
    case VarRef(n) => Pat.PVar(n, t.span)
    case Wildcard() => Pat.PWild(t.span)
    case Lit(Literal.IntL(n)) if n >= 0 => Pat.PLit(n, t.span)
    case ListLit(_) | ConsE(_, _) => listPattern(t, expected.flatMap(listElement))
    case _ =>
      TreeOps.flattenApp(t) match
        case (id @ Ident(n), args) =>
          val c = constructorNamed(n, id.span)
          val types = constructorArgTypes(c, expected)
          if types.length != args.length then
            fail(ClauseProblem.PatternArity(n, types.length, args.length, t.span))
          Pat.PCon(c, args.zip(types).map(pattern(_, _)), t.span)
        case _ =>
          fail(ClauseProblem.InvalidPattern(t.span))

  /** `[p̄]` or `p :: ps`, with the element type if known. */
  def listPattern(t: Tree, elem: Option[Val]): Pat =
    val r = reflective(t.span)
    val listTy = elem.map(listOf)
    t match
      case Parens(i) => listPattern(i, elem)
      case ListLit(es) =>
        es.foldRight(Pat.PCon(r.snil, Nil, t.span)) { (e, acc) => Pat.PCon(r.scons, List(pattern(e, elem), acc), t.span) }
      case ConsE(h, tl) => Pat.PCon(r.scons, List(pattern(h, elem), pattern(tl, listTy)), t.span)
      case other => pattern(other, listTy)

  /** The types of the explicit arguments of constructor `c` matched against `expected`, where they are
   *  closed: the implicit arguments are taken from the expected type (`scons : A -> seq A -> seq A`
   *  against `seq formula`). */
  private def constructorArgTypes(c: Int, expected: Option[Val]): List[Option[Val]] =
    val (_, result) = telescope(globals(c).ty)
    val known: Map[Int, Val] = (expected.map(forceData), forceData(result)) match
      case (Some(Val.Rigid(Head.Glob(f), esp)), Val.Rigid(Head.Glob(g), rsp)) if f == g && esp.length == rsp.length =>
        rsp.zip(esp).collect { case (Elim.EApp(Val.Rigid(Head.Local(l), Nil), _), Elim.EApp(v, _)) => l -> v }.toMap
      case _ => Map.empty
    var ty = globals(c).ty
    var l = 0
    val out = scala.collection.mutable.ListBuffer.empty[Option[Val]]
    var more = true
    while more do
      force(ty) match
        case Val.Pi(_, i, a, cl) =>
          if i == Icit.Expl then out += closedType(a, l)
          ty = inst(cl, known.getOrElse(l, Val.local(l)))
          l += 1
        case _ => more = false
    out.toList

  /** `a` (over `l` variables) if it does not depend on them. */
  def closedType(a: Val, l: Int): Option[Val] =
    Option.when(!Tm.exists(quote(l, a)) { case Tm.Var(_) => true; case _ => false })(a)

  private def constructorNamed(n: Name, span: Span): Int =
    lookupGlobal(n).filter(isConstructor) match
      case Some(c) => c
      case None =>
        val what = lookupGlobal(n).map(id => s"`$n` is not a constructor").getOrElse(s"unresolved name `$n`")
        fail(ClauseProblem.NotAConstructor(what, span))
