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
 *  - each rule of `aux` is its alternative after the *context* of the call: the formulas before the
 *    aggregate (in canonical order), which bind the inputs. Only the formulas that do not mention a
 *    relation depending on the calling rule's head are kept, if they still bind the inputs (issue #1, F1):
 *    then `aux` does not depend on the caller and the aggregate's negative edge closes no cycle; otherwise
 *    the whole prefix is used (and a cycle through the aggregate is reported, E0601). The kept formulas
 *    hold wherever the prefix holds, so for every binding of the inputs at the call `aux` has exactly
 *    the alternatives' answers.
 *  The aggregate then ranges over the distinct bindings of `ō` (and its other variables), as for a
 *  relation atom. See issue #1, item B4.
 */
final class Disjunctions extends MiniPhase:
  def phaseName = "disjunction"
  def description = "split disjunctions and multiple heads; lift disjunctions in aggregates (Section 7.2)"

  def start(using Context): MiniPhase.Transformer = Traversal()

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

  private def allVars(f: Formula): Set[String] = f match
    case Formula.Atom(_, as, v) => as.flatMap(Moding.vars).toSet ++ v
    case Formula.Cmp(_, l, r) => Moding.vars(l) ++ Moding.vars(r)
    case Formula.Not(a) => allVars(a)
    case Formula.Agg(res, _, t, b) => Moding.vars(t) ++ b.flatMap(allVars) + res
    case Formula.Disj(alts) => alts.flatten.flatMap(allVars).toSet

  private def headName(r: Rule): String = r.heads.headOption match
    case Some(Term.App(RelRef.Sym(c), _)) => c.name
    case _ => "rule"

  /** A traversal: the auxiliary relations and their rules, added to the program at the end. */
  private final class Traversal extends MiniPhase.Transformer:
    private val auxRules = mutable.ArrayBuffer.empty[Rule]
    private val auxRels = mutable.ArrayBuffer.empty[RelSym]
    private var dependents: Option[Map[RelSym, Set[RelSym]]] = None

    /** The relations that depend on `h` (in the program before the lifting). */
    private def dependentsOf(h: RelSym)(using Context): Set[RelSym] =
      val all = dependents.getOrElse {
        val es = hugin.obj.check.DepGraph.edges(ctx.unit.prog.nn)
        val pred = es.groupBy(_.to).view.mapValues(_.map(_.from)).toMap
        val m = es.map(_.to).distinct.map { c =>
          val seen = mutable.HashSet(c)
          val todo = mutable.Stack(c)
          while todo.nonEmpty do pred.getOrElse(todo.pop(), Nil).foreach(x => if seen.add(x) then todo.push(x))
          c -> seen.toSet
        }.toMap
        dependents = Some(m)
        m
      }
      all.getOrElse(h, Set(h))

    /** The context of a lifted disjunction: the formulas of `prefix` that mention no relation of
     *  `excluded`, if they bind `inputs`; otherwise the whole prefix. */
    private def context(prefix: List[Formula], inputs: Set[String], excluded: Set[RelSym]): List[Formula] =
      val (kept, bound) = prefix.foldLeft((Vector.empty[Formula], Set.empty[String])) { case ((ks, b), f) =>
        if hugin.obj.check.DepGraph.occurrences(List(f), bound = b).exists(o => excluded(o._1)) then (ks, b)
        else
          Moding.step(f, b) match
            case Right(b2) => (ks :+ f, b2)
            case Left(_) => (ks, b)
      }
      if inputs.subsetOf(bound) then kept.toList else prefix

    override def finish(using Context): Unit =
      val p = ctx.unit.prog.nn
      p.rules = p.rules ++ auxRules
      p.rels = p.rels ++ auxRels

    /** Each formula of `body` (evaluated with `bound` bound) with the formulas before it in canonical
     *  order and the variables bound then. */
    private def prefixes(body: List[Formula], bound: Set[String]): Map[Formula, (List[Formula], Set[String])] =
      val out = mutable.HashMap.empty[Formula, (List[Formula], Set[String])]
      Moding.canonical(body, bound).foreach { (ordered, _) =>
        ordered.foldLeft((List.empty[Formula], bound)) { case ((pre, b), f) =>
          out(f) = (pre, b)
          (pre :+ f, Moding.step(f, b).getOrElse(b))
        }
      }
      out.toMap

    /** Lifts disjunctions out of the aggregates of `body`; `excluded` are the relations that depend on the
     *  head of the rule (none for a query). */
    private def liftBody(body: List[Formula], excluded: Set[RelSym], item: Item)(using Context): List[Formula] =
      if !body.exists { case Formula.Agg(_, _, _, ib) => hasDisj(ib); case _ => false } then return body
      // walk in canonical order to know what comes before each aggregate; keep the original order
      val before = prefixes(body, Set.empty)
      body.map {
        case g @ Formula.Agg(res, k, t, ib) if hasDisj(ib) =>
          val (pre, b) = before.getOrElse(g, (Nil, Set.empty[String]))
          Formula.Agg(res, k, t, liftInAggregate(ib, pre, b, excluded, item))(g.span)
        case f => f
      }

    /** Replaces each disjunction of an aggregate body (after the formulas `outer`, which bind `bound`) by
     *  an atom of a fresh auxiliary relation. */
    private def liftInAggregate(body: List[Formula], outer: List[Formula], bound: Set[String], excluded: Set[RelSym], item: Item)(
        using Context
    ): List[Formula] =
      val before = prefixes(body, bound)
      body.map {
        case d @ Formula.Disj(alts) =>
          val (pre, b) = before.getOrElse(d, (Nil, bound))
          val altVars = alts.map(_.flatMap(allVars).toSet)
          val inputs = altVars.foldLeft(Set.empty[String])(_ ++ _).intersect(b).toList.sorted
          val results = alts.map(alt => Moding.canonical(alt, inputs.toSet).map(_._2).getOrElse(inputs.toSet))
          // an empty disjunction (a formula function without clauses) is false and binds nothing
          val outputs = (results.reduceOption(_ intersect _).getOrElse(Set.empty) -- inputs).toList.sorted
          val ctxt = if inputs.isEmpty then Nil else context(outer ++ pre, inputs.toSet, excluded)
          lift(d, inputs, outputs, ctxt, item)
        case g @ Formula.Agg(res, k, t, ib) if hasDisj(ib) =>
          val (pre, b) = before.getOrElse(g, (Nil, bound))
          Formula.Agg(res, k, t, liftInAggregate(ib, outer ++ pre, b, excluded, item))(g.span)
        case f => f
      }

    private def lift(d: Formula.Disj, inputs: List[String], outputs: List[String], context: List[Formula], item: Item)(using
        Context
    ): Formula =
      val aux = RelSym(s"${item.name}^or${auxRels.length + 1}", RelKind.Auxiliary("disjunction inside an aggregate"), d.span, item.origin)
      val params = inputs ++ outputs
      aux.cols = params.map(v => Column(None, item.types.getOrElse(v, OType.Err))).toVector
      auxRels += aux
      def args = params.map(v => Term.Var(v)(d.span): Term)
      for alt <- d.alts do
        val rule = Rule(None, List(Term.App(RelRef.Sym(aux), args)(d.span)), context ++ alt)(item.span, item.origin, item.expansions)
        ctx.unit.varTypes.put(rule, item.types)
        auxRules ++= transformRule(rule)
      Formula.Atom(RelRef.Sym(aux), args, None)(d.span)

    override def transformRule(r: Rule)(using Context): List[Rule] =
      val g = Option(ctx.unit.varTypes.get(r)).getOrElse(Map.empty)
      val heads = r.heads.collect { case Term.App(RelRef.Sym(c), _) => c }
      val body = liftBody(r.body, heads.flatMap(dependentsOf).toSet, Item(headName(r), r.span, r.origin, r.expansions, g))
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
