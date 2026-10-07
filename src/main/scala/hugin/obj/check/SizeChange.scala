package hugin.obj
package check

import scala.collection.mutable

import hugin.obj.typing.Moding

/** Direction (A) of the termination check, *descent along derivations* (docs/REDESIGN.md §4.2,
 *  docs/NOTES.md "Termination"): the size-change principle of Lee, Jones and Ben-Amram (POPL 2001) applied
 *  to derivation chains of a recursive component.
 *
 *  For every rule `H :- …, B, …` of the component and every body atom `B` of the component there is a
 *  *size-change graph* from the arguments of `B` (the premise) to the arguments of `H` (the conclusion):
 *  an arc `i → j` says how argument `j` of the conclusion relates to argument `i` of the premise —
 *  equal, not larger / strictly smaller (structurally: a proper subterm; integers: by the interval
 *  reasoning of [[Arithmetic]], strictly smaller only above a lower bound the body establishes), or not
 *  smaller / strictly larger (integers below an upper bound). The component is accepted if every
 *  idempotent graph `p → p` of the composition closure has a strict arc `i → i`, or equates every
 *  argument (the chain returns to the same fact). Then no derivation chain of distinct facts is infinite,
 *  and the component's fixed point is finite (König's lemma, see the notes). */
object SizeChange:
  // arc labels: equal; non-strict / strict decrease; non-strict / strict increase
  private inline val Eq = 0
  private inline val DownWeak = 1
  private inline val DownStrict = 2
  private inline val UpWeak = 3
  private inline val UpStrict = 4

  private def isDown(l: Int) = l == DownWeak || l == DownStrict
  private def isUp(l: Int) = l == UpWeak || l == UpStrict
  private def strict(l: Int) = l == DownStrict || l == UpStrict

  /** The label of a premise-to-conclusion path through two arcs, or -1 if the path says nothing. A
   *  decrease followed by an increase has no direction, so decreasing and increasing arguments never
   *  combine into one thread (they are ordered differently). */
  private def seq(a: Int, b: Int): Int =
    if a == Eq then b
    else if b == Eq then a
    else if isDown(a) && isDown(b) then (if a == DownStrict || b == DownStrict then DownStrict else DownWeak)
    else if isUp(a) && isUp(b) then (if a == UpStrict || b == UpStrict then UpStrict else UpWeak)
    else -1

  final case class Arc(from: Int, to: Int, label: Int)

  /** A size-change graph, normalised: the weak arcs implied by an `Eq` or a strict arc of the same
   *  direction and positions are dropped. */
  final case class Graph(arcs: Set[Arc]):
    def andThen(o: Graph): Graph =
      val byFrom = o.arcs.groupBy(_.from)
      Graph.of(for
        a <- arcs.iterator
        b <- byFrom.getOrElse(a.to, Set.empty).iterator
        l = seq(a.label, b.label)
        if l >= 0
      yield Arc(a.from, b.to, l))

    def idempotent: Boolean = andThen(this) == this

    /** An idempotent self-graph is harmless if it decreases (or increases) an argument strictly, or keeps
     *  every argument equal: then the facts at both ends of a segment are the same fact. */
    def descends(arity: Int): Boolean =
      arcs.exists(a => a.from == a.to && strict(a.label)) || (0 until arity).forall(i => arcs(Arc(i, i, Eq)))

  object Graph:
    def of(arcs: IterableOnce[Arc]): Graph =
      val all = arcs.iterator.toSet
      Graph(all.filterNot(a =>
        (a.label == DownWeak && (all(a.copy(label = Eq)) || all(a.copy(label = DownStrict)))) ||
          (a.label == UpWeak && (all(a.copy(label = Eq)) || all(a.copy(label = UpStrict))))
      ))

  /** One recursive step: the rule `rule` concludes a fact of `to` from the premise `atom` of `from`. */
  final case class Step(rule: Rule, atom: Formula.Atom, from: RelSym, to: RelSym, graph: Graph, why: List[String], hints: List[Hint])

  /** An integer argument that decreases (or increases) from the premise to the conclusion without a
   *  bound in that direction: a guard would make the step strict. */
  final case class Hint(rule: Rule, head: Term, premise: Term, up: Boolean)

  /** A chain of steps through the component, with its composed graph. */
  final case class Chain(from: RelSym, to: RelSym, graph: Graph, steps: List[Step])

  /** A cycle whose idempotent graph has no strict self-arc; `None` for `steps` if the closure grew too large. */
  final case class Failure(rel: RelSym, chain: Option[Chain])

  private val MaxGraphs = 4000

  /** The size-change graph of every recursive step of the component. */
  def steps(comp: List[RelSym], rules: Vector[Rule]): Vector[Step] =
    val inC = comp.toSet
    rules.flatMap { r =>
      r.heads.headOption match
        case Some(Term.App(RelRef.Sym(p), hs)) if inC(p) =>
          lazy val arith = Arithmetic(r.body)
          lazy val outside = Constructive.finiteVars(r.body, inC)
          r.body.collect { case a @ Formula.Atom(RelRef.Sym(q), ss, _) if inC(q) => (a, q, ss) }.map { (a, q, ss) =>
            val arcs = List.newBuilder[Arc]
            val why = List.newBuilder[String]
            val hints = List.newBuilder[Hint]
            for (s, i) <- keys(q, ss); (h, j) <- keys(p, hs) do
              val (sInt, hInt) =
                (q.cols.lift(i).exists(c => Termination.isInt(c.tpe)), p.cols.lift(j).exists(c => Termination.isInt(c.tpe)))
              if sInt && hInt then
                val (l, w, hint) = numeric(s, h, arith, outside)
                if l >= 0 then arcs += Arc(i, j, l)
                w.foreach(why += _)
                hint.foreach(up => hints += Hint(r, h, s, up))
              else if !sInt && !hInt then
                if unwrap(s) == unwrap(h) || equated(r.body, s, h) then arcs += Arc(i, j, Eq)
                else
                  Decrease.structurallySmaller(s, h, r.body).foreach { w =>
                    arcs += Arc(i, j, DownStrict)
                    why += w
                  }
            Step(r, a, q, p, Graph.of(arcs.result()), why.result(), hints.result())
          }
        case _ => Nil
    }

  /** The arguments with their positions, without a bound column: its values are not invented (they are
   *  kept finite per key by evaluation, docs/REDESIGN.md §5.2), so they take no part in size change. */
  private def keys(r: RelSym, args: List[Term]): List[(Term, Int)] =
    val all = args.zipWithIndex
    if r.boundColumn.isDefined then all.init else all

  private def unwrap(t: Term): Term = t match
    case Term.As(x, _) => unwrap(x)
    case Term.Ascr(x, _) => unwrap(x)
    case _ => t

  private def equated(body: List[Formula], a: Term, b: Term): Boolean = body.exists {
    case Formula.Cmp(CmpOp.Eq, l, r) => (l == a && r == b) || (l == b && r == a)
    case _ => false
  }

  /** The arc label from premise argument `s` to conclusion argument `h` (integers), its justification if
   *  strict, and whether a decrease (false) or increase (true) lacks a bound. */
  private def numeric(s: Term, h: Term, arith: Arithmetic, outside: Set[String]): (Int, Option[String], Option[Boolean]) =
    def sh(t: Term) = ObjPrinter.term(t)
    val d = arith.difference(s, h) // premise - conclusion
    val ih = arith(h)
    val finite = Moding.vars(h).subsetOf(outside)
    def bound(lo: Boolean): Option[String] =
      if finite then
        Some(if Moding.vars(h).isEmpty then s"`${sh(h)}` is constant" else s"`${sh(h)}` is bound by relations outside the component")
      else if lo then ih.lo.map(b => s"`${sh(h)}` >= $b")
      else ih.hi.map(b => s"`${sh(h)}` <= $b")
    if unwrap(s) == unwrap(h) || (d.lo.contains(0) && d.hi.contains(0)) then (Eq, None, None)
    else
      val smaller = Decrease.numericSmaller(s, h, arith)
      if smaller.isDefined then
        bound(lo = true) match
          case Some(b) => (DownStrict, Some(s"`${sh(h)}` < `${sh(s)}` (${smaller.get}; $b)"), None)
          case None => (DownWeak, None, Some(false))
      else if d.lo.exists(_ >= 0) then (DownWeak, None, None)
      else if d.hi.exists(_ <= -1) then
        bound(lo = false) match
          case Some(b) => (UpStrict, Some(s"`${sh(h)}` > `${sh(s)}` (`${sh(h)} - ${ObjPrinter.arg(s)}` ${(-d).show}; $b)"), None)
          case None => (UpWeak, None, Some(true))
      else if d.hi.exists(_ <= 0) then (UpWeak, None, None)
      else (-1, None, None)

  /** Checks the component: the explanation, or a cycle without descent. */
  def check(comp: List[RelSym], rules: Vector[Rule]): Either[Failure, List[String]] =
    val base = steps(comp, rules)
    val byFrom = base.groupBy(_.from)
    // insertion-ordered: the reported cycle must not depend on identity hash codes
    val seen = mutable.LinkedHashMap.empty[(RelSym, RelSym, Graph), Chain]
    val work = mutable.Queue.from(base.map(s => Chain(s.from, s.to, s.graph, List(s))))
    while work.nonEmpty && seen.size <= MaxGraphs do
      val c = work.dequeue()
      val key = (c.from, c.to, c.graph)
      if !seen.contains(key) then
        seen(key) = c
        for s <- byFrom.getOrElse(c.to, Vector.empty) do work.enqueue(Chain(c.from, s.to, c.graph.andThen(s.graph), c.steps :+ s))
    if seen.size > MaxGraphs then Left(Failure(comp.head, None))
    else
      seen.valuesIterator.filter(c => c.from == c.to && c.graph.idempotent && !c.graph.descends(c.from.arity))
        .minByOption(_.steps.length) match
        case Some(c) => Left(Failure(c.from, Some(c)))
        case None =>
          val lines = base.toList.map { s =>
            val why = if s.why.isEmpty then "no decrease (every cycle through it decreases elsewhere)" else s.why.mkString("; ")
            s"  rule at ${s.rule.span.show}: premise `${ObjPrinter.formula(s.atom)}`: $why"
          }
          Right(
            "  descent along derivations: every cycle of derivation steps makes an argument strictly smaller (or larger, below a bound)" :: lines
          )
