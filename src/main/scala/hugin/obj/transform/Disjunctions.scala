package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*

/** Section 7.2: split disjunctions (and multi-head rules) into several rules. */
final class Disjunctions extends MiniPhase:
  def phaseName = "disjunction"
  def description = "split disjunctions and multiple heads (Section 7.2)"

  private def split(body: List[Formula]): List[List[Formula]] =
    val idx = body.indexWhere(_.isInstanceOf[Formula.Disj])
    if idx < 0 then List(body)
    else
      val Formula.Disj(alts) = body(idx): @unchecked
      alts.flatMap(alt => split(body.take(idx) ++ alt ++ body.drop(idx + 1)))

  private def checkNested(body: List[Formula], report: Diagnostic => Unit): Boolean =
    body.forall {
      case g @ Formula.Agg(_, _, _, b) =>
        val inner = b.exists(_.isInstanceOf[Formula.Disj])
        if inner then
          report(Diagnostic.error(
            "E0202",
            "disjunction inside an aggregate is not supported",
            g.span,
            "this aggregate's body contains a disjunction"
          )
            .withHelp("define a helper relation with one rule per alternative and aggregate over it"))
        !inner && checkNested(b, report)
      case _ => true
    }

  override def transformRule(r: Rule)(using Context): List[Rule] =
    if !checkNested(r.body, d => ctx.report(Diag.rule(r)(d))) then return Nil
    val g = ctx.unit.varTypes.get(r)
    for h <- r.heads; b <- split(r.body) yield
      val nr = r.withParts(heads = List(h), body = b)
      if g != null then ctx.unit.varTypes.put(nr, g)
      nr

  override def transformQuery(q: Query)(using Context): Query =
    if !checkNested(q.body, d => ctx.report(Diag.query(q)(d))) then q.withBody(Nil)
    else
      split(q.body) match
        case List(b) => q.withBody(b)
        case alts =>
          val nq = q.withBody(List(Formula.Disj(alts)(q.span)))
          val g = ctx.unit.varTypes.get(q)
          if g != null then ctx.unit.varTypes.put(nq, g)
          nq
