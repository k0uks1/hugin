package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

import hugin.obj.typing.TypeOps

/** Section 7.1: projections `X.l` and updates `(X with {...})` on a closed type with members c1..cn
 *  are expanded into one copy of the rule per member; copy i adds `(ci Z̄ as X)`. */
final class Records extends MiniPhase:
  def phaseName = "records"
  def description = "expand projections and updates (Section 7.1)"

  def start(using Context): MiniPhase.Transformer = Expander(TypeOps(ctx.unit.prog.nn))

  private def projected(t: Term, acc: mutable.LinkedHashSet[String]): Unit = t match
    case Term.Proj(Term.Var(x), _) => acc += x
    case Term.With(Term.Var(x), fs) => acc += x; fs.foreach(f => projected(f._2, acc))
    case Term.App(_, as) => as.foreach(projected(_, acc))
    case Term.As(y, _) => projected(y, acc)
    case Term.Ascr(y, _) => projected(y, acc)
    case Term.Arith(_, l, r) => projected(l, acc); projected(r, acc)
    case Term.Neg(y) => projected(y, acc)
    case _ =>

  private def projectedF(f: Formula, acc: mutable.LinkedHashSet[String]): Unit = f match
    case Formula.Atom(_, as, _) => as.foreach(projected(_, acc))
    case Formula.Cmp(_, l, r) => projected(l, acc); projected(r, acc)
    case Formula.Not(a) => projectedF(a, acc)
    case Formula.Agg(_, _, t, b) => projected(t, acc); b.foreach(projectedF(_, acc))
    case Formula.Disj(alts) => alts.flatten.foreach(projectedF(_, acc))

  private def zName(x: String, c: RelSym, k: Int): String =
    s"$x.${c.cols(k).label.getOrElse((k + 1).toString)}"

  /** Rewrites projections/updates of the variables in `choice` (var → chosen member). */
  private def rw(t: Term, choice: Map[String, RelSym]): Term = t match
    case p @ Term.Proj(Term.Var(x), l) if choice.contains(x) =>
      val c = choice(x)
      Term.Var(zName(x, c, c.labelIndex(l).get))(p.span)
    case w @ Term.With(Term.Var(x), fs) if choice.contains(x) =>
      val c = choice(x)
      val args = c.cols.indices.map { k =>
        fs.find(f => c.cols(k).label.contains(f._1)) match
          case Some((_, h, _)) => rw(h, choice)
          case None => Term.Var(zName(x, c, k))(w.span)
      }.toList
      Term.App(RelRef.Sym(c), args)(w.span)
    case a @ Term.App(r, as) => Term.App(r, as.map(rw(_, choice)))(a.span)
    case a @ Term.As(y, v) => Term.As(rw(y, choice), v)(a.span)
    case a @ Term.Ascr(y, tp) => Term.Ascr(rw(y, choice), tp)(a.span)
    case a @ Term.Arith(op, l, r) => Term.Arith(op, rw(l, choice), rw(r, choice))(a.span)
    case n @ Term.Neg(y) => Term.Neg(rw(y, choice))(n.span)
    case other => other

  private def guardFor(x: String, c: RelSym, span: Span): Formula =
    Formula.Atom(RelRef.Sym(c), c.cols.indices.map(k => Term.Var(zName(x, c, k))(span): Term).toList, Some(x))(span)

  /** Rewrites a body; guards are added to the innermost body that mentions the projection. */
  private def rwBody(b: List[Formula], choice: Map[String, RelSym], span: Span): List[Formula] =
    val here = mutable.LinkedHashSet.empty[String]
    b.foreach {
      case Formula.Agg(_, _, _, _) | Formula.Disj(_) =>
      case f => projectedF(f, here)
    }
    val rewritten = b.map {
      case a @ Formula.Atom(r, as, v) => Formula.Atom(r, as.map(rw(_, choice)), v)(a.span)
      case c @ Formula.Cmp(op, l, r) => Formula.Cmp(op, rw(l, choice), rw(r, choice))(c.span)
      case n @ Formula.Not(a) => Formula.Not(Formula.Atom(a.rel, a.args.map(rw(_, choice)), a.as)(a.span))(n.span)
      case g @ Formula.Agg(res, k, t, ib) =>
        val inner = rwBody(ib, choice, g.span)
        val termVars = mutable.LinkedHashSet.empty[String]
        projected(t, termVars)
        val extra = termVars.toList.filter(x =>
          choice.contains(x) && !inner.exists {
            case Formula.Atom(_, _, Some(`x`)) => true
            case _ => false
          }
        ).map(x => guardFor(x, choice(x), g.span))
        Formula.Agg(res, k, rw(t, choice), inner ++ extra)(g.span)
      case d @ Formula.Disj(alts) => Formula.Disj(alts.map(rwBody(_, choice, d.span)))(d.span)
    }
    rewritten ++ here.toList.filter(choice.contains).map(x => guardFor(x, choice(x), span))

  private def expand(
      ops: TypeOps,
      heads: List[Term],
      body: List[Formula],
      gamma: Map[String, OType],
      span: Span
  ): List[(List[Term], List[Formula], Map[String, OType])] =
    val vs = mutable.LinkedHashSet.empty[String]
    heads.foreach(projected(_, vs))
    body.foreach(projectedF(_, vs))
    if vs.isEmpty then return List((heads, body, gamma))
    val choices = vs.toList.foldLeft(List(Map.empty[String, RelSym])) { (acc, x) =>
      val ms = gamma.get(x).map(t => ops.members(t).toList.sortBy(_.id)).getOrElse(Nil)
      for m <- acc; c <- ms yield m + (x -> c)
    }
    choices.map { ch =>
      val headVarsProj = mutable.LinkedHashSet.empty[String]
      heads.foreach(projected(_, headVarsProj))
      val hs = heads.map(rw(_, ch))
      var b = rwBody(body, ch, span)
      // projections occurring only in heads need their guard in the top-level body
      for
        x <- headVarsProj if ch.contains(x) && !b.exists {
          case Formula.Atom(_, _, Some(`x`)) => true
          case _ => false
        }
      do b = b :+ guardFor(x, ch(x), span)
      val g2 =
        gamma ++ ch.flatMap((x, c) => c.cols.indices.map(k => zName(x, c, k) -> c.cols(k).tpe)) ++ ch.map((x, c) => x -> OType.Fact(c, Nil))
      (hs, b, g2)
    }

  /** A traversal, with the type operations of the program being transformed. */
  private final class Expander(ops: TypeOps) extends MiniPhase.Transformer:
    override def transformRule(r: Rule)(using Context): List[Rule] =
      val g = Option(ctx.unit.varTypes.get(r)).getOrElse(Map.empty)
      expand(ops, r.heads, r.body, g, r.span).map { (hs, b, g2) =>
        val nr = r.withParts(heads = hs, body = b)
        ctx.unit.varTypes.put(nr, g2)
        nr
      }

    override def transformQuery(q: Query)(using Context): Query =
      val g = Option(ctx.unit.varTypes.get(q)).getOrElse(Map.empty)
      expand(ops, Nil, q.body, g, q.span) match
        case List((_, b, g2)) => val nq = q.withBody(b); ctx.unit.varTypes.put(nq, g2); nq
        case many =>
          // alternatives of a query are kept as one top-level disjunction, expanded when lowering
          val nq = q.withBody(List(Formula.Disj(many.map(_._2))(q.span)))
          ctx.unit.varTypes.put(nq, many.map(_._3).reduce(_ ++ _))
          nq
