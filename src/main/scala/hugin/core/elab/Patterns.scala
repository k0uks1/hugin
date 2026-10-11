package hugin.core
package elab

import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Patterns of clauses: uppercase variables, `_`, constructors applied to patterns, nat literals and
 *  successor patterns `p + k`. */
enum Pat:
  /** A pattern variable; `implicitBinder` for the name of an implicit binder of the function's type,
   *  which is in scope unless a pattern variable shadows it. */
  case PVar(name: Name, span: Span, implicitBinder: Boolean = false)
  case PWild(span: Span)

  /** A constructor applied to patterns for its explicit arguments; `implicits` are patterns for some of its
   *  implicit arguments, by the names of their binders (`vcons {N := K} X XS`). */
  case PCon(ctor: Int, args: List[Pat], span: Span, implicits: List[(Name, Pat)] = Nil)
  case PLit(n: BigInt, span: Span)

  /** `p + k` (`k ≥ 1`) against a nat-like type: the successor applied `k` times to `p`. */
  case PSucc(p: Pat, k: BigInt, span: Span)

  /** A value of a type without constructors (a reference to an object constant, a meta literal): `key` is
   *  its closed normal form, as [[hugin.core.Matching.atomKey]] computes it. Only quoted patterns produce
   *  it (reference: reflection). */
  case PAtom(key: Tm, span: Span)

  /** `()`, Agda's absurd pattern: matches nothing, and is allowed only at a position none of whose
   *  constructors can occur (reference: meta/clauses). */
  case PAbsurd(span: Span)

/** A pattern against a nat-like family in numeral form ([[Patterns.natForm]]). */
enum NatPattern:
  case Literal(k: BigInt, span: Span)

  /** `p + j`, where `p` is not a literal, a successor or the constant (`j = 0`: the pattern itself). */
  case Offset(p: Pat, j: BigInt)

  def plus(i: BigInt): NatPattern = this match
    case Literal(k, span) => Literal(k + i, span)
    case Offset(p, j) => Offset(p, j + i)

/** One clause `f p̄ = e.` (or a definition `f X̄ = e.` of a declared function), with its `where` block; an
 *  absurd clause `f p̄.` has the right-hand side [[Absent]]. */
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
    case d: Def if state.functionNames(d.name.name) => Some(defClause(d))
    case _ => None

  /** `f X̄ = e.` as a clause of the declared function `f`. */
  def defClause(d: Def): SurfaceClause =
    val pats = d.params.map {
      case Param.VarParam(v) => v
      case Param.Typed(_, _, sp) => fail(ClauseProblem.TypedPattern(sp))
      case Param.Malformed(t) => syntaxError(t.span)
    }
    SurfaceClause(d.name, pats, d.rhs, d.span)

  /** A surface pattern, with the type it matches if that is known and closed: a quote `'( … )` is a
   *  quoted pattern ([[QuotedPatterns]]), which needs a reflective type; list syntax is the prelude's
   *  meta `list`. */
  def pattern(t: Tree, expected: Option[Val] = None): Pat = t match
    case q: Quote =>
      expected.flatMap(reflectiveKind) match
        case Some(k) => quotedPattern(q, k)
        case None => quoteWithoutType(Cxt.empty, q, expected)
    case _ => plainPattern(t, expected)

  private def plainPattern(t: Tree, expected: Option[Val]): Pat = t match
    case Parens(i) => pattern(i, expected)
    case VarRef(n) => Pat.PVar(n, t.span)
    case Wildcard() => Pat.PWild(t.span)
    case Absurd() => Pat.PAbsurd(t.span)
    // against the meta `int`: `ofNat k` for `k ≥ 0`, `negSucc (k - 1)` for `-k` (reference: std/int)
    case Lit(Literal.IntL(n)) if intExpected(expected) => intPattern(BigInt(n), t.span)
    case BigLit(n) if intExpected(expected) => intPattern(n, t.span)
    case Neg(BigLit(n)) if intExpected(expected) => intPattern(-n, t.span)
    case Lit(Literal.IntL(n)) if n >= 0 => Pat.PLit(BigInt(n), t.span)
    case BigLit(n) => Pat.PLit(n, t.span)
    case Infix("+", p, k) if successorCount(k).isDefined => Pat.PSucc(pattern(p, expected), BigInt(successorCount(k).get), t.span)
    case ListLit(_) | ConsE(_, _) => listPattern(t, expected.flatMap(listElement))
    case _ =>
      TreeOps.flattenApp(t) match
        case (h @ (_: Ident | _: SymRef), allArgs) =>
          val (c, n) = h match
            case SymRef(id, n) if isConstructor(id) => (id, n) // a generated pattern ([[DerivedFunctions]])
            case _ =>
              val c = constructorNamed(nameOf(h), h.span)
              recordUse(h.span, c)
              (c, nameOf(h))
          val (named, args) = allArgs.partitionMap {
            case na: NamedArg => Left(na)
            case a => Right(a)
          }
          val binders = constructorBinderTypes(c, expected)
          val types = binders.collect { case (_, Icit.Expl, a) => a }
          if types.length != args.length then
            fail(ClauseProblem.PatternArity(n, types.length, args.length, t.span))
          // `{N := p}`: a pattern for the implicit argument `N` of the constructor (reference: meta/clauses)
          val implicitNames = binders.collect { case (x, Icit.Impl, _) => x }
          val implicits = named.foldLeft(List.empty[(Name, Pat)]) { (acc, na) =>
            val x = na.name
            if acc.exists(_._1 == x) then fail(ClauseProblem.ImplicitPatternTwice(x, na.nameSpan))
            binders.collectFirst { case (`x`, Icit.Impl, a) => a } match
              case Some(a) => acc :+ (x -> pattern(na.value, a))
              case None => fail(TypeProblem.NoImplicitNamed(x, n, implicitNames, na.nameSpan))
          }
          Pat.PCon(c, args.zip(types).map(pattern(_, _)), t.span, implicits)
        case _ =>
          fail(ClauseProblem.InvalidPattern(t.span))

  private def intExpected(expected: Option[Val]): Boolean = metaInt != null && expected.exists(a => isMetaInt(force(a)))

  /** The integer `n` as a pattern of constructors of the meta `int`, over a numeral pattern. */
  private def intPattern(n: BigInt, span: Span): Pat =
    val m = metaInt.nn
    if n >= 0 then Pat.PCon(m.ofNat, List(Pat.PLit(n, span)), span)
    else Pat.PCon(m.negSucc, List(Pat.PLit(-n - 1, span)), span)

  /** A pattern against the nat-like family with the constant `z` and the successor `s`, as a numeral or as
   *  a pattern with the successor applied `j` times (reference: meta/clauses): `3` and `suc (suc (suc
   *  zero))` are the literal 3, `P + 2` and `suc (suc P)` are `P` with the offset 2. */
  def natForm(pat: Pat, z: Int, s: Int): NatPattern = pat match
    case Pat.PLit(k, span) => NatPattern.Literal(k, span)
    case Pat.PCon(`z`, Nil, span, _) => NatPattern.Literal(BigInt(0), span)
    case Pat.PCon(`s`, List(q), _, _) => natForm(q, z, s).plus(1)
    case Pat.PSucc(q, k, _) => natForm(q, z, s).plus(k)
    case other => NatPattern.Offset(other, BigInt(0))

  /** `[p̄]` or `p :: ps`, with the element type if known. */
  def listPattern(t: Tree, elem: Option[Val]): Pat =
    val r = reflective(t.span)
    val listTy = elem.map(listOf)
    t match
      case Parens(i) => listPattern(i, elem)
      case ListLit(es) =>
        es.foldRight(Pat.PCon(r.nil, Nil, t.span)) { (e, acc) => Pat.PCon(r.cons, List(pattern(e, elem), acc), t.span) }
      case ConsE(h, tl) => Pat.PCon(r.cons, List(pattern(h, elem), pattern(tl, listTy)), t.span)
      case other => pattern(other, listTy)

  /** The binders of constructor `c` matched against `expected`, with their types where they are closed:
   *  the implicit arguments are taken from the expected type (`cons : A -> list A -> list A` against
   *  `list formula`). */
  private def constructorBinderTypes(c: Int, expected: Option[Val]): List[(Name, Icit, Option[Val])] =
    val (_, result) = telescope(globals(c).ty)
    val known: Map[Int, Val] = (expected.map(forceData), forceData(result)) match
      case (Some(Val.Rigid(Head.Glob(f), esp)), Val.Rigid(Head.Glob(g), rsp)) if f == g && esp.length == rsp.length =>
        rsp.zip(esp).collect { case (Elim.EApp(Val.Rigid(Head.Local(l), Nil), _), Elim.EApp(v, _)) => l -> v }.toMap
      case _ => Map.empty
    var ty = globals(c).ty
    var l = 0
    val out = scala.collection.mutable.ListBuffer.empty[(Name, Icit, Option[Val])]
    var more = true
    while more do
      force(ty) match
        case Val.Pi(x, i, a, cl) =>
          out += ((x, i, closedType(a, l)))
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
