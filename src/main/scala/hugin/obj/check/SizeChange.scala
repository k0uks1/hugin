package hugin.obj
package check

import scala.collection.mutable

import hugin.obj.typing.Moding

/** Direction (A) of the termination check, *descent along derivations* (reference: object/termination,
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
 *  and the component's fixed point is finite (König's lemma, see the notes).
 *
 *  That criterion is decided without the full closure (issue #65): [[check]] keeps, per pair of
 *  relations, only the *weakest* graphs (an antichain; see [[Graph.weakerThan]]) and tests every kept
 *  graph `p → p` with the local criterion of Ben-Amram and Lee ([[Graph.descendsLocally]]), which is
 *  equivalent to the idempotent one on the full closure; the argument is in [[check]]. */
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

  /** Whether label `a` implies label `b` (the same facts or more). */
  private def implies(a: Int, b: Int): Boolean =
    a == b || (b == DownWeak && (a == Eq || a == DownStrict)) || (b == UpWeak && (a == Eq || a == UpStrict))

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
     *  every argument equal: then the facts at both ends of a segment are the same fact. This is the test
     *  of Lee, Jones and Ben-Amram on the full closure; [[check]] decides it by [[descendsLocally]]. */
    def descends(arity: Int): Boolean =
      arcs.exists(a => a.from == a.to && strict(a.label)) || (0 until arity).forall(i => arcs(Arc(i, i, Eq)))

    /** `this` says at most what `o` says: every arc of `this` is implied by an arc of `o` between the
     *  same arguments (`=` implies `≥` and `≤`, a strict arc the weak one of its direction). Composition
     *  is monotone in this order (`seq` is monotone in both labels, and a missing arc is the bottom). */
    def weakerThan(o: Graph): Boolean = arcs.forall(a => o.arcs.exists(b => b.from == a.from && b.to == a.to && implies(b.label, a.label)))

    /** The local criterion of Ben-Amram and Lee for a self-graph `p → p` (see [[check]]): a strict arc
     *  lies on a cycle of arcs of its own direction (`=` belongs to both), or every argument lies on a
     *  cycle of `=` arcs. For an idempotent graph this is [[descends]]; in general it holds iff it holds
     *  for the idempotent power of the graph. */
    def descendsLocally(arity: Int): Boolean =
      def onCycle(a: Arc, along: Int => Boolean): Boolean =
        val next = arcs.iterator.filter(b => along(b.label)).toList.groupMap(_.from)(_.to)
        val seen = mutable.Set(a.to)
        val todo = mutable.Stack(a.to)
        while todo.nonEmpty && !seen(a.from) do
          for k <- next.getOrElse(todo.pop(), Nil) if seen.add(k) do todo.push(k)
        seen(a.from)
      def down(l: Int) = l == Eq || isDown(l)
      def up(l: Int) = l == Eq || isUp(l)
      arcs.exists(a => strict(a.label) && onCycle(a, if isDown(a.label) then down else up)) ||
      (0 until arity).forall(i => arcs.exists(a => a.from == i && a.label == Eq && onCycle(a, _ == Eq)))

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

  /** A cycle whose graph fails the criterion (see [[check]]). */
  final case class Failure(rel: RelSym, chain: Chain)

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
   *  kept finite per key by evaluation, reference: object/bound-columns), so they take no part in size change. */
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

  /** Checks the component: the explanation, or a cycle without descent.
   *
   *  *The closure.* A work list composes chains with the base steps (Agda's `completionStep` with the
   *  original calls), but a chain is kept only if no kept chain between the same relations has a graph
   *  [[Graph.weakerThan]] its own, and keeping it drops the kept chains it is weaker than (Ben-Amram and
   *  Lee, *Program termination analysis in polynomial time*, TOPLAS 29(1), 2007, who use this
   *  subsumption for their SCT baseline; Agda's `Agda.Utils.Favorites`, used by
   *  `Agda.Termination.CallMatrix.CMSet`, keeps the same "least informative" matrices). Every graph `X`
   *  of the full closure has a kept graph `Y ⊑ X`: by induction on the steps `b₁ … bₙ` of `X`, `Y'` kept
   *  for `b₁ … bₙ₋₁` was once inserted, so `Y'; bₙ` was queued and is dominated by a kept graph, and
   *  `Y'; bₙ ⊑ b₁ … bₙ` by monotonicity (a dropped graph is replaced by a weaker one; `⊑` is
   *  transitive). The loop ends: each insertion adds a graph to the upward closure of the kept set, which
   *  never shrinks, and there are finitely many graphs over the component's arguments. No cap is needed.
   *
   *  *The criterion.* Subsumption is unsound with the idempotent test itself: the weaker `Y` that
   *  replaces a bad idempotent `X` need not be idempotent, and the antichain may hold no idempotent bad
   *  graph at all. Fogarty and Vardi (*Büchi complementation and size-change termination*, LMCS 8(1:13),
   *  2012, Section 4.1, after their TACAS 2010 proof) state the remedy of Ben-Amram and Lee: replace the
   *  search for a strict self-arc in idempotent graphs by a search, in *every* graph `p → p`, for a
   *  strongly connected set of its arcs through a strict arc ([[Graph.descendsLocally]]; here a cycle
   *  stays in one direction, since a decrease followed by an increase composes to nothing, and the
   *  second alternative, every argument equal, becomes every argument on a cycle of `=` arcs). With
   *  `G^e` the idempotent power of `G` (a power `G^k`, `k ≥ 1`, with `G^k; G^k = G^k`):
   *
   *  1. local(G) iff descends(G^e). A cycle of `m` arcs through a strict arc at `x` gives a strict
   *     `x → x` in `G^(m·k)` for every `k`, and `G^e = G^(e·m)`; conversely a strict `x → x` in
   *     `G^e` is a closed walk of `G` in one direction through a strict arc, so that arc lies on a cycle.
   *     Likewise every argument has a closed walk of `=` arcs of length `e` iff each lies on an `=` cycle
   *     (`G^e = G^(e·d·t)` for every period `d` and `t`, and long multiples of `d` are closed walk lengths).
   *  2. Hence the full closure passes the idempotent test iff all its self-graphs pass local: an
   *     idempotent graph is its own power, and `G^e` is in the closure with `G`.
   *  3. local is upward closed in `⊑`: a strict arc or `=` arc of `Y` is implied only by an arc of the same
   *     kind in `X`, so `Y`'s cycles are cycles of `X`.
   *
   *  So if the full closure has a bad `X`, the kept `Y ⊑ X` fails local by 3; and the kept graphs belong
   *  to the full closure, so if they all pass, so does the full closure by 2. Any graph that fails local
   *  is a counterexample by 2, so the search stops at the first one: the work list is breadth-first, so
   *  this is a shortest chain that fails among those inserted (an idempotent one if there is one of that
   *  length, as the idempotent test reports). The verdict is the one of the full closure. (Agda checks
   *  only the idempotent matrices of its favourites, with a relaxed idempotency; this check does not.) */
  def check(comp: List[RelSym], rules: Vector[Rule]): Either[Failure, List[String]] =
    val base = steps(comp, rules)
    closure(base, stop = true)._2 match
      case Some(c) => Left(Failure(c.from, c))
      case None =>
        val lines = base.toList.map { s =>
          val why = if s.why.isEmpty then "no decrease (every cycle through it decreases elsewhere)" else s.why.mkString("; ")
          s"  rule at ${s.rule.span.show}: premise `${ObjPrinter.formula(s.atom)}`: $why"
        }
        Right(
          "  descent along derivations: every cycle of derivation steps makes an argument strictly smaller (or larger, below a bound)" :: lines
        )

  /** The weakest chains of the composition closure of `base`, per pair of relations (see [[check]]), in a
   *  deterministic order, and a shortest inserted self-chain that fails the local criterion. With `stop`,
   *  the search ends after the first length at which one fails. */
  def closure(base: Vector[Step], stop: Boolean = false): (Vector[Chain], Option[Chain]) =
    val byFrom = base.groupBy(_.from)
    // insertion-ordered: the reported cycle must not depend on identity hash codes
    val kept = mutable.LinkedHashMap.empty[(RelSym, RelSym), mutable.ArrayBuffer[Chain]]
    val work = mutable.Queue.from(base.map(s => Chain(s.from, s.to, s.graph, List(s))))
    val failing = mutable.ArrayBuffer.empty[Chain]
    def done = stop && failing.nonEmpty && work.head.steps.lengthCompare(failing.head.steps.length) > 0
    while work.nonEmpty && !done do
      val c = work.dequeue()
      val here = kept.getOrElseUpdate((c.from, c.to), mutable.ArrayBuffer.empty)
      if !here.exists(_.graph.weakerThan(c.graph)) then
        here.filterInPlace(k => !c.graph.weakerThan(k.graph))
        here += c
        if c.from == c.to && !c.graph.descendsLocally(c.from.arity) then failing += c
        for s <- byFrom.getOrElse(c.to, Vector.empty) do work.enqueue(Chain(c.from, s.to, c.graph.andThen(s.graph), c.steps :+ s))
    (kept.valuesIterator.flatten.toVector, failing.find(_.graph.idempotent).orElse(failing.headOption))
