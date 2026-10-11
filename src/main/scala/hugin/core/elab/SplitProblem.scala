package hugin.core
package elab

/** The context of one branch of a case tree under construction: a variable per level (the function's
 *  arguments, then the arguments of the constructors matched so far). Matching and index unification
 *  *solve* variables: `values(l)` is then a term over the other variables instead of the variable itself.
 *  Old values (of clauses, the target type) are brought up to date by [[norm]], which re-evaluates them
 *  in the current values; since values refer to variables by level, solutions may mention variables of
 *  any level. */
final case class SplitProblem(
    names: Vector[Name],
    types: Vector[Val],
    values: Vector[Val],
    /** The values a free variable of a nat-like type cannot have, in the branches of a split by value
     *  that are not the values' own ([[CaseTree.SplitNat]]). */
    ranges: Map[Int, NatRange] = Map.empty,
    /** No value is in this case: a range left no value. */
    dead: Boolean = false
):
  def size: Int = names.length

  /** The values as an environment (innermost first), computed once per problem. */
  lazy val env: List[Val] = values.reverse.toList
  def isFree(l: Int): Boolean = values(l) == Val.local(l)

  def extend(name: Name, ty: Val): SplitProblem =
    copy(names = names :+ name, types = types :+ ty, values = values :+ Val.local(size))

  /** The range of the free variable `x` (every numeral if none). */
  def range(x: Int): NatRange = ranges.getOrElse(x, NatRange.all)

  /** The problem with the free variable `x` restricted to the range `r` as well. */
  def restrict(x: Int, r: NatRange): SplitProblem =
    val merged = range(x).meet(r)
    copy(ranges = ranges.updated(x, merged), dead = dead || merged.isEmpty)

  /** Brings a value up to date with the current solutions. */
  def norm(core: Core, v: Val): Val = core.eval(env, core.quote(size, v))

  /** The free variables, ordered so that each one's type only mentions variables before it (solutions may
   *  mention later variables, so level order is not a telescope any more): a stable topological sort. */
  def telescopeOrder(core: Core): Vector[Int] =
    val free = (0 until size).filter(isFree).toVector
    val deps = free.map { l =>
      val ty = core.quote(size, types(l))
      l -> free.filter(x => x != l && core.occurs(size - x - 1, ty)).toSet
    }.toMap
    val out = scala.collection.mutable.ArrayBuffer.empty[Int]
    while out.length < free.length do
      out += free.find(l => !out.contains(l) && deps(l).forall(out.contains)).getOrElse(free.find(!out.contains(_)).get)
    out.toVector

  /** Translates values of the problem into a context of the free variables in the given order. */
  def renaming(core: Core, order: Vector[Int]): Val => Val =
    val position = order.zipWithIndex.toMap
    val env = (0 until size).map(l => position.get(l).map(Val.local).getOrElse(Val.Wild)).reverse.toList
    v => core.eval(env, core.quote(size, v))

  /** Solves the free variable `x` by `t` (which must not mention `x`); a range of `x` moves to the
   *  variable under the successors of `t`, or decides whether the case is dead. */
  def solve(core: Core, x: Int, t: Val): SplitProblem =
    val p = copy(values = values.updated(x, t))
    val solved = p.copy(values = p.values.map(p.norm(core, _)), types = p.types.map(p.norm(core, _)))
    ranges.get(x) match
      case None => solved
      case Some(r) =>
        val q = solved.copy(ranges = ranges - x)
        core.natChain(solved.values(x)) match
          case Left(m) => if r.allows(m) then q else q.copy(dead = true)
          case Right((i, Val.Rigid(Head.Local(y), Nil))) if q.isFree(y) => q.restrict(y, r.shift(i))
          case Right(_) => q

/** The numerals a variable of a nat-like type can still be: not one of `excluded`, and below `below` if
 *  given. */
final case class NatRange(excluded: Set[BigInt], below: Option[BigInt]):
  def allows(v: BigInt): Boolean = v >= 0 && !excluded(v) && below.forall(v < _)
  def meet(r: NatRange): NatRange =
    NatRange(excluded ++ r.excluded, (below.toList ++ r.below.toList).minOption)

  /** The range of `y` where the variable is `y + i`. */
  def shift(i: BigInt): NatRange = NatRange(excluded.collect { case v if v >= i => v - i }, below.map(_ - i))

  /** No numeral is in the range. */
  def isEmpty: Boolean = below.exists(b => b <= 0 || (b <= excluded.size && (BigInt(0) until b).forall(excluded)))

object NatRange:
  val all: NatRange = NatRange(Set.empty, None)

/** The outcome of unifying constructor indices during a split. */
enum IndexUnification:
  case Solved(p: SplitProblem)

  /** The constructor cannot apply (distinct constructors, a cycle `n = suc n`, distinct literals): the
   *  equation `a = b` that conflicts (`a` from the constructor's type, `b` from the scrutinee's). */
  case Conflict(a: Val, b: Val)

  /** Neither: an equation between terms that are not constructor applications or variables. */
  case Stuck(a: Val, b: Val)

/** Unification of indices for dependent pattern matching (Cockx & Abel's unifier, without the
 *  restrictions needed for univalence: deletion, solution, injectivity, conflict and cycle rules). The
 *  variables of the split problem are the unknowns. */
trait IndexUnifier:
  self: Elaborator =>
  import core.*

  /** Unifies the equations `eqs0`. An equation that is neither solvable nor refutable yet is postponed
   *  until the others make no more progress (a worklist, as Agda's unifier tries every equation): a later
   *  equation may solve a variable it mentions, or end in a conflict. It is stuck only if a whole round
   *  of the postponed equations solves nothing. */
  def unifyIndices(p0: SplitProblem, eqs0: List[(Val, Val)]): IndexUnification =
    var p = p0
    var eqs = eqs0
    var postponed = List.empty[(Val, Val)]
    var stuck: Option[IndexUnification.Stuck] = None
    var progress = false
    var result: Option[IndexUnification] = None
    while result.isEmpty && (eqs.nonEmpty || postponed.nonEmpty) do
      if eqs.isEmpty then
        // a round of the postponed equations, if the last one solved something
        if progress then
          eqs = postponed.reverse
          postponed = Nil
          progress = false
        else result = stuck
      else
        val (a0, b0) = eqs.head
        eqs = eqs.tail
        val a = force(p.norm(core, a0))
        val b = force(p.norm(core, b0))
        def postpone(s: IndexUnification.Stuck): Unit =
          if postponed.isEmpty then stuck = Some(s)
          postponed = (a, b) :: postponed
        if quote(p.size, a) != quote(p.size, b) then
          (freeVar(p, a), freeVar(p, b)) match
            case (Some(x), Some(y)) =>
              p = p.solve(core, x.max(y), Val.local(x.min(y)))
              progress = true
            case (Some(x), None) =>
              solveVar(p, x, b) match
                case Right(q) => p = q; progress = true
                case Left(s: IndexUnification.Stuck) => postpone(s)
                case Left(r) => result = Some(r)
            case (None, Some(y)) =>
              solveVar(p, y, a) match
                case Right(q) => p = q; progress = true
                case Left(s: IndexUnification.Stuck) => postpone(s)
                case Left(r) => result = Some(r)
            case (None, None) if isNumeralForm(a) && isNumeralForm(b) =>
              // numerals and offsets by value: the smaller number of successors is taken off both sides
              (natChain(a), natChain(b)) match
                case (Left(m), Left(n)) => result = Some(IndexUnification.Conflict(a, b))
                case (Left(m), Right((i, base))) =>
                  if m >= i then
                    eqs = (Val.Nat(natFamilyOf(b), m - i), base) :: eqs
                    progress = true
                  else result = Some(IndexUnification.Conflict(a, b))
                case (Right((i, base)), Left(n)) =>
                  if n >= i then
                    eqs = (base, Val.Nat(natFamilyOf(a), n - i)) :: eqs
                    progress = true
                  else result = Some(IndexUnification.Conflict(a, b))
                case (Right((i, b1)), Right((j, b2))) =>
                  val m = i.min(j)
                  eqs = (natAdd(natFamilyOf(a), b1, i - m), natAdd(natFamilyOf(b), b2, j - m)) :: eqs
                  progress = true
            case (None, None) =>
              // a numeral against a constructor application by one view step
              (natView(a), natView(b)) match
                case _ if a.isInstanceOf[Val.Nat] && b.isInstanceOf[Val.Nat] => result = Some(IndexUnification.Conflict(a, b))
                case (Val.Rigid(Head.Glob(c1), sp1), Val.Rigid(Head.Glob(c2), sp2)) if isConstructor(c1) && isConstructor(c2) =>
                  if c1 != c2 || sp1.length != sp2.length then result = Some(IndexUnification.Conflict(a, b))
                  else
                    eqs = sp1.reverse.zip(sp2.reverse).collect { case (Elim.EApp(x, _), Elim.EApp(y, _)) => (x, y) } ++ eqs
                    progress = true
                case (Val.Lit(x, _), Val.Lit(y, _)) if x != y => result = Some(IndexUnification.Conflict(a, b))
                case _ => postpone(IndexUnification.Stuck(a, b))
    result.getOrElse(IndexUnification.Solved(p))

  private def freeVar(p: SplitProblem, v: Val): Option[Int] = v match
    case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => Some(x)
    case _ => None

  /** `x = t`: solve, unless `x` occurs in `t` (a cycle under constructors is a conflict). */
  private def solveVar(p: SplitProblem, x: Int, t: Val): Either[IndexUnification, SplitProblem] =
    if !occurs(p.size - x - 1, quote(p.size, t)) then Right(p.solve(core, x, t))
    else if constructorTerm(t) then Left(IndexUnification.Conflict(Val.local(x), t))
    else Left(IndexUnification.Stuck(Val.local(x), t))

  /** A numeral, an offset, or a successor application. */
  private def isNumeralForm(v: Val): Boolean = v match
    case _: Val.Nat | _: Val.NatAdd => true
    case Val.Rigid(Head.Glob(c), _) => isSuccessor(c)
    case _ => false

  /** The nat-like family of a numeral form. */
  private def natFamilyOf(v: Val): Int = v match
    case Val.Nat(f, _) => f
    case Val.NatAdd(f, _, _) => f
    case Val.Rigid(Head.Glob(c), _) =>
      globals(c).kind match
        case GlobalKind.Constructor(f) => f
        case _ => -1
    case _ => -1

  private def constructorTerm(v: Val): Boolean = force(v) match
    case Val.Rigid(Head.Glob(c), _) => isConstructor(c)
    case _: Val.Nat | _: Val.NatAdd => true
    case _ => false
