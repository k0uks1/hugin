package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*
import hugin.obj.typing.Moding
import scala.collection.mutable

/** Section 7.2: split disjunctions (and multi-head rules) into several rules.
 *
 *  A disjunction inside an aggregate cannot be split, since that would split the aggregate. It is lifted
 *  into an auxiliary relation `aux(ī, ō)` with one rule per alternative:
 *  - the inputs `ī` are the variables of the disjunction bound before it (in canonical order);
 *  - the outputs `ō` are the variables every alternative binds; a variable bound by only some
 *    alternatives is existential within its alternative;
 *  - if there are inputs, `aux` gets the mode `+…+-…-`, so that the demand transformation (Section 7.3)
 *    supplies the input bindings that arise at the call site; the demand is built only from formulas
 *    that do not depend on the calling rule's head (`DemandPhase.auxDemand`, issue #1, F1).
 *  The aggregate then ranges over the distinct bindings of `ō` (and its other variables), as for a
 *  relation atom. See issue #1, item B4.
 */
final class Disjunctions extends MiniPhase:
  def phaseName = "disjunction"
  def description = "split disjunctions and multiple heads; lift disjunctions in aggregates (Section 7.2)"

  private val auxRules = mutable.ArrayBuffer.empty[Rule]
  private val auxRels = mutable.ArrayBuffer.empty[RelSym]

  override def prepare(using Context): Unit =
    auxRules.clear()
    auxRels.clear()

  override def finish(using Context): Unit =
    val p = ctx.unit.prog.nn
    p.rules = p.rules ++ auxRules
    p.rels = p.rels ++ auxRels

  private def split(body: List[Formula]): List[List[Formula]] =
    val idx = body.indexWhere(_.isInstanceOf[Formula.Disj])
    if idx < 0 then List(body)
    else
      val Formula.Disj(alts) = body(idx): @unchecked
      alts.flatMap(alt => split(body.take(idx) ++ alt ++ body.drop(idx + 1)))

  /** The context of the item being transformed. */
  private final case class Item(name: String, span: Span, origin: Origin, expansions: List[Expansion], types: Map[String, OType])

  private def hasDisj(b: List[Formula]): Boolean = b.exists {
    case _: Formula.Disj => true
    case Formula.Agg(_, _, _, ib) => hasDisj(ib)
    case _ => false
  }

  /** Lifts disjunctions out of the aggregates of `body`, which is evaluated with `bound` already bound. */
  private def liftBody(body: List[Formula], bound: Set[String], item: Item)(using Context): List[Formula] =
    if !body.exists { case Formula.Agg(_, _, _, ib) => hasDisj(ib); case _ => false } then return body
    // walk in canonical order to know what is bound before each aggregate; keep the original order
    val boundBefore = mutable.HashMap.empty[Formula, Set[String]]
    Moding.canonical(body, bound).foreach { (ordered, _) =>
      ordered.foldLeft(bound) { (b, f) =>
        boundBefore(f) = b
        Moding.step(f, b).getOrElse(b)
      }
    }
    body.map {
      case g @ Formula.Agg(res, k, t, ib) if hasDisj(ib) =>
        Formula.Agg(res, k, t, liftInAggregate(ib, boundBefore.getOrElse(g, bound), item))(g.span)
      case f => f
    }

  /** Replaces each disjunction of an aggregate body by an atom of a fresh auxiliary relation. */
  private def liftInAggregate(body: List[Formula], bound: Set[String], item: Item)(using Context): List[Formula] =
    val boundBefore = mutable.HashMap.empty[Formula, Set[String]]
    Moding.canonical(body, bound).foreach { (ordered, _) =>
      ordered.foldLeft(bound) { (b, f) =>
        boundBefore(f) = b
        Moding.step(f, b).getOrElse(b)
      }
    }
    body.map {
      case d @ Formula.Disj(alts) =>
        val b = boundBefore.getOrElse(d, bound)
        val altVars = alts.map(_.flatMap(allVars).toSet)
        val inputs = altVars.foldLeft(Set.empty[String])(_ ++ _).intersect(b).toList.sorted
        val results = alts.map(alt => Moding.canonical(alt, inputs.toSet).map(_._2).getOrElse(inputs.toSet))
        // an empty disjunction (a formula function without clauses) is false and binds nothing
        val outputs = (results.reduceOption(_ intersect _).getOrElse(Set.empty) -- inputs).toList.sorted
        lift(d, inputs, outputs, item)
      case g @ Formula.Agg(res, k, t, ib) if hasDisj(ib) =>
        Formula.Agg(res, k, t, liftInAggregate(ib, boundBefore.getOrElse(g, bound), item))(g.span)
      case f => f
    }

  private def allVars(f: Formula): Set[String] = f match
    case Formula.Atom(_, as, v) => as.flatMap(Moding.vars).toSet ++ v
    case Formula.Cmp(_, l, r) => Moding.vars(l) ++ Moding.vars(r)
    case Formula.Not(a) => allVars(a)
    case Formula.Agg(res, _, t, b) => Moding.vars(t) ++ b.flatMap(allVars) + res
    case Formula.Disj(alts) => alts.flatten.flatMap(allVars).toSet
    case _ => Set.empty

  private def lift(d: Formula.Disj, inputs: List[String], outputs: List[String], item: Item)(using Context): Formula =
    val aux = RelSym(s"${item.name}^or${auxRels.length + 1}", RelKind.Auxiliary("disjunction inside an aggregate"), d.span, item.origin)
    val params = inputs ++ outputs
    aux.cols = params.map(v => Column(None, item.types.getOrElse(v, OType.Err))).toVector
    if inputs.nonEmpty then
      ctx.unit.facts = ctx.unit.facts.updated(aux)(_.copy(modes = List((Mode(params.map(inputs.contains).toVector), d.span))))
    auxRels += aux
    def args = params.map(v => Term.Var(v)(d.span): Term)
    for alt <- d.alts do
      val rule = Rule(None, List(Term.App(RelRef.Sym(aux), args)(d.span)), alt)(item.span, item.origin, item.expansions)
      ctx.unit.varTypes.put(rule, item.types)
      auxRules ++= transformRule(rule)
    Formula.Atom(RelRef.Sym(aux), args, None)(d.span)

  private def headName(r: Rule): String = r.heads.headOption match
    case Some(Term.App(RelRef.Sym(c), _)) => c.name
    case _ => "rule"

  /** Variables bound by the head in every mode of the head relation. */
  private def headInputs(r: Rule)(using facts: ProgramFacts): Set[String] = r.heads
    .collect {
      case h @ Term.App(RelRef.Sym(c), _) if facts.hasModes(c) =>
        facts.modes(c).map((m, _) => Moding.headInputVars(h, m)).reduce(_ intersect _)
    }
    .foldLeft(Set.empty[String])(_ ++ _)

  override def transformRule(r: Rule)(using Context): List[Rule] =
    val g = Option(ctx.unit.varTypes.get(r)).getOrElse(Map.empty)
    val body = liftBody(r.body, headInputs(r), Item(headName(r), r.span, r.origin, r.expansions, g))
    for h <- r.heads; b <- split(body) yield
      val nr = r.withParts(heads = List(h), body = b)
      ctx.unit.varTypes.put(nr, g)
      nr

  override def transformQuery(q: Query)(using Context): Query =
    val g = Option(ctx.unit.varTypes.get(q)).getOrElse(Map.empty)
    val body = liftBody(q.body, Set.empty, Item("query", q.span, q.origin, q.expansions, g))
    split(body) match
      case List(b) =>
        val nq = q.withBody(b)
        ctx.unit.varTypes.put(nq, g)
        nq
      case alts =>
        val nq = q.withBody(List(Formula.Disj(alts)(q.span)))
        ctx.unit.varTypes.put(nq, g)
        nq
