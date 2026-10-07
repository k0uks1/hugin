package hugin.obj
package check

import hugin.obj.typing.Moding

/** A recursive component under analysis: its relations `comp`, its rules, all rules of the program and
 *  the dependency edges, with the queries about finiteness and dependencies the checks share. */
final class RecursiveComponent(
    val facts: ProgramFacts,
    val comp: List[RelSym],
    val rules: Vector[Rule],
    val allRules: Vector[Rule],
    val es: List[DepEdge]
):
  import Termination.*

  val inC: Set[RelSym] = comp.toSet

  /** The shortest cycle through `c` inside the component (for diagnostics). */
  def cycle(c: RelSym): Option[List[RelSym]] =
    val succ = es.filter(e => inC(e.from) && inC(e.to)).groupMap(_.from)(_.to)
    val prev = scala.collection.mutable.LinkedHashMap.empty[RelSym, RelSym]
    var frontier = List(c)
    var found = false
    while frontier.nonEmpty && !found do
      frontier = frontier.flatMap { x =>
        succ.getOrElse(x, Nil).distinct.filter { y =>
          if y == c then
            if !found then prev(c) = x
            found = true
            false
          else if prev.contains(y) then false
          else
            prev(y) = x
            true
        }
      }
    if !found then None
    else
      var path = List(c)
      var x = prev(c)
      while x != c do
        path = x :: path
        x = prev(x)
      Some(c :: path)

  /** Variables of `body` with finitely many values whatever the facts of the component: bound by positive
   *  atoms of finite sources outside the component ([[Constructive.finiteVars]]), occurring in a column of `finite` of an
   *  atom of the component, or equal to a term over such variables. */
  def finiteSources(body: List[Formula], finite: Set[(RelSym, Int)]): Set[String] =
    var vars = Constructive.finiteVars(body, inC) ++ body.collect {
      case Formula.Atom(RelRef.Sym(x), as, _) if inC(x) =>
        as.zipWithIndex.collect { case (a, k) if finite((x, k)) => Moding.vars(a) }.flatten.toSet
    }.flatten.toSet
    var changed = true
    while changed do
      changed = false
      body.foreach {
        case Formula.Cmp(CmpOp.Eq, l, r) =>
          for (a, b) <- List((l, r), (r, l)) do
            a match
              case Term.Var(x) if !vars(x) && Moding.vars(b).subsetOf(vars) =>
                vars += x
                changed = true
              case _ =>
        case _ =>
      }
    vars

  /** The columns of unmeasured plain relations of the component whose values come from a finite set over
   *  the whole evaluation (a least fixed point): every rule of the relation puts into the column a term
   *  over variables of [[finiteSources]] (given the columns found so far). A column value is a function
   *  of the valuation of those variables, each of which ranges over a finite set. */
  def finiteColumns(measured: RelSym => Boolean): Set[(RelSym, Int)] =
    val byHead = rules.groupBy(headRel).collect {
      case (Some(u), rs) if inC(u) && u.kind == RelKind.Plain && !measured(u) => u -> rs
    }
    var finite = Set.empty[(RelSym, Int)]
    var changed = true
    while changed do
      changed = false
      for (u, rs) <- byHead; k <- 0 until u.arity if !finite((u, k)) do
        val ok = rs.forall { r =>
          r.heads match
            case List(Term.App(_, hs)) => hs.lift(k).exists(h => Moding.vars(h).subsetOf(finiteSources(r.body, finite)))
            case _ => false
        }
        if ok then
          finite += ((u, k))
          changed = true
    finite

  /** Positive atoms of finite sources outside the component bind their variables to finitely many values
   *  (see [[Constructive.finiteVars]]). */
  def boundOutside(body: List[Formula]): Set[String] = Constructive.finiteVars(body, inC)

  /** A measured relation that `d` depends on inside the component, not counting dependencies through
   *  demand relations, with the path. */
  def readsAnswers(d: RelSym, measured: RelSym => Boolean, demand: RelSym => Boolean): Option[List[RelSym]] =
    val succ = es.filter(e => inC(e.from) && inC(e.to)).groupMap(_.from)(_.to)
    val prev = scala.collection.mutable.HashMap(d -> d)
    var frontier = List(d)
    var hit: Option[RelSym] = None
    while frontier.nonEmpty && hit.isEmpty do
      frontier =
        for
          x <- frontier
          y <- succ.getOrElse(x, Nil).distinct
          if !prev.contains(y)
        yield
          prev(y) = x
          if measured(y) && hit.isEmpty then hit = Some(y)
          y
      frontier = frontier.filterNot(y => demand(y) || measured(y))
    hit.map { m =>
      var path = List(m)
      while path.head != d do path = prev(path.head) :: path
      path
    }

  /** Rules of relations without a measure (other than demand relations of measured ones) must not be
   *  constructive: their facts consist of existing terms. With `answers`, in a demand-driven component, the
   *  answers of measured relations count as finite sources (there are finitely many demands, see
   *  [[DemandDriven.check]]), so `d0 (some N) :- e L, len L N` constructs terms from a finite set. */
  def unmeasuredConstructive(ctx: MeasureCtx, allowed: RelSym => Boolean, answers: Boolean = false): Option[TerminationFailure] =
    val grows: RelSym => Boolean = x => inC(x) && !(answers && ctx.measuredAnywhere(x))
    rules.iterator.collectFirst(Function.unlift { r =>
      headRel(r).filterNot(allowed).flatMap(h =>
        Constructive.constructive(r, grows).map((why, sp) =>
          TerminationFailure(
            s"constructive rule for `${h.name}`, which has no measure",
            sp,
            why,
            Some(r),
            ctx.measures.keys.headOption.flatMap(ctx.directive),
            notes = List(s"`${h.name}` is in the recursive component ${showComponent(comp)}"),
            helps = List(s"give `${h.name}` a `%terminates` measure with the same shape, or mark it `%partial ${h.name}.`")
          )
        )
      )
    })
