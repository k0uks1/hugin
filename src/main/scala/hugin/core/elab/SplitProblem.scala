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

  def isFree(l: Int): Boolean = values(l) == Val.local(l)

  def extend(name: Name, ty: Val): SplitProblem =
    copy(names = names :+ name, types = types :+ ty, values = values :+ Val.local(size))

  /** The range of the free variable `x` (every numeral if none). */
  def range(x: Int): NatRange = ranges.getOrElse(x, NatRange.all)

  /** The problem with the free variable `x` restricted to the range `r` as well. */
  def restrict(x: Int, r: NatRange): SplitProblem =
    val merged = range(x).meet(r)
    copy(ranges = ranges.updated(x, merged), dead = dead || merged.isEmpty)

  /** Brings a value up to date with the current solutions: substitutes them, without evaluating (issue
   *  #195). The applications a solution unblocks stay delayed: index unification evaluates them to
   *  weak-head form on demand ([[Core.whnf]]), anything else when it forces or reads back the value.
   *  (Evaluation and read-back normalised the whole value, `double n` with `n := 9223372036854775807` in
   *  2^63 steps.) */
  def norm(core: Core, v: Val): Val = core.substitute(values, v)

  /** The free variables, ordered so that each one's type only mentions variables before it (solutions may
   *  mention later variables, so level order is not a telescope any more): a stable topological sort. */
  def telescopeOrder(core: Core): Vector[Int] =
    val free = (0 until size).filter(isFree).toVector
    val deps = free.map { l =>
      // read back only if a variable is in the type as it is (it may not be in its normal form)
      lazy val ty = core.quote(size, types(l))
      l -> free.filter(x => x != l && core.mentions(x, types(l)) && core.occurs(size - x - 1, ty)).toSet
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
    // the values and types are up to date with the solutions before: only those that mention `x` change
    def upd(v: Val): Val = if core.mentions(x, v) then p.norm(core, v) else v
    val solved = p.copy(values = p.values.updated(x, p.norm(core, t)).map(upd), types = p.types.map(upd))
    ranges.get(x) match
      case None => solved
      case Some(r) =>
        val q = solved.copy(ranges = ranges - x)
        core.natChainWeak(solved.values(x), Long.MaxValue) match
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

  /** The constructor cannot apply (distinct constructors, a cycle `n = suc n`, distinct atoms): the
   *  equation `a = b` that conflicts (`a` from the constructor's type, `b` from the scrutinee's). */
  case Conflict(a: Val, b: Val)

  /** Neither: an equation between terms that are not constructor applications or variables. */
  case Stuck(a: Val, b: Val)

/** Unification of indices for dependent pattern matching (Cockx & Abel's unifier, without the
 *  restrictions needed for univalence: deletion, solution, injectivity, conflict and cycle rules; the
 *  conflict rule also for distinct atoms, symbols and literals, which have no constructors). The
 *  variables of the split problem are the unknowns.
 *
 *  It works up to weak-head normal form (issue #195), as Agda's unifier and the conversion checks of Lean
 *  and Rocq do: each side of an equation is evaluated until its head is known ([[Core.whnf]]), and an
 *  argument only when an equation between it and another one is reached. The outcome is the one of
 *  unifying normal forms; what it shows in a diagnostic is the equation's sides, normalised if that is
 *  cheap ([[Core.quoteShown]]). */
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
        // the sides up to date (`an`, `bn`, what diagnostics show), and their weak-head forms
        val an = p.norm(core, a0)
        val bn = p.norm(core, b0)
        val a = whnf(an)
        val b = whnf(bn)
        def postpone(s: IndexUnification.Stuck): Unit =
          if postponed.isEmpty then stuck = Some(s)
          postponed = (an, bn) :: postponed
        lazy val code = if isCode(a) || isCode(b) then objectCode(p, a, b, an, bn) else None
        if !sameWeak(p.size, a, b) then
          (freeVar(p, a), freeVar(p, b)) match
            case (Some(x), Some(y)) =>
              p = p.solve(core, x.max(y), Val.local(x.min(y)))
              progress = true
            case (Some(x), None) =>
              solveVar(p, x, b, bn) match
                case Right(q) => p = q; progress = true
                case Left(s: IndexUnification.Stuck) => postpone(s)
                case Left(r) => result = Some(r)
            case (None, Some(y)) =>
              solveVar(p, y, a, an) match
                case Right(q) => p = q; progress = true
                case Left(s: IndexUnification.Stuck) => postpone(s)
                case Left(r) => result = Some(r)
            case (None, None) if isNumeralForm(a) && isNumeralForm(b) =>
              // numerals and offsets by value: the smaller number of successors is taken off both sides
              numerals(a, b) match
                case Some(eq) =>
                  eqs = eq :: eqs
                  progress = true
                case None => result = Some(IndexUnification.Conflict(an, bn))
            case (None, None) if code.isDefined =>
              code.get match
                case Right(more) =>
                  eqs = more ++ eqs
                  progress = true
                case Left(r) => result = Some(r)
            case (None, None) =>
              // a numeral against a constructor application by one view step
              (natView(a), natView(b)) match
                case _ if a.isInstanceOf[Val.Nat] && b.isInstanceOf[Val.Nat] => result = Some(IndexUnification.Conflict(an, bn))
                case (Val.Rigid(Head.Glob(c1), sp1), Val.Rigid(Head.Glob(c2), sp2)) if isConstructor(c1) && isConstructor(c2) =>
                  if c1 != c2 || sp1.length != sp2.length then result = Some(IndexUnification.Conflict(an, bn))
                  else
                    eqs = sp1.reverse.zip(sp2.reverse).collect { case (Elim.EApp(x, _), Elim.EApp(y, _)) => (x, y) } ++ eqs
                    progress = true
                case (Val.Lit(x, _), Val.Lit(y, _)) if x != y => result = Some(IndexUnification.Conflict(an, bn))
                // two atoms (symbols, literals) are equal only if they are the same atom: distinct ones
                // conflict, as distinct constructors do (reference: meta/coverage, index unification)
                case _ if atomOf(a).isDefined && atomOf(b).isDefined =>
                  if stripPositions(atomOf(a).get) == stripPositions(atomOf(b).get) then progress = true
                  else result = Some(IndexUnification.Conflict(an, bn))
                case _ => postpone(IndexUnification.Stuck(an, bn))
    result.getOrElse(IndexUnification.Solved(p))

  private def freeVar(p: SplitProblem, v: Val): Option[Int] = v match
    case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => Some(x)
    case _ => None

  // ---------------------------------------------------------------- object code (#186 P5)

  /** A weak-head form that is object code or a quote of it: index unification compares it by the rules
   *  of [[objectCode]]. */
  private def isCode(v: Val): Boolean = Val.unloc(v) match
    case _: Val.Quote | _: Val.Persist => true
    case Val.Lit(_, Stage.S0) => true
    case Val.Rigid(Head.Glob(c), _) => isObjectConst(c)
    case Val.Rigid(Head.Local(_), Elim.ESplice :: _) => true
    case Val.Base(_, Stage.S0) => true
    case _ => false

  /** An object constant (a type, relation, constructor or struct): generative, so distinct ones are never
   *  equal, and an application of one is equal to another only argument by argument. An instance of an
   *  object family is one too; the family itself is not (it is applied to types first). */
  private def isObjectConst(c: Int): Boolean = globals(c).kind.isInstanceOf[GlobalKind.Object]

  /** An equation between object code (in weak-head form; `an`, `bn` as the equation shows them), by the
   *  rules for closed object code, whose equality is syntactic (reference: meta/coverage, index
   *  unification; the proofs note, chapter 9): a quote is decomposed (`⟨t⟩ = ⟨u⟩` is `t = u`, and η
   *  `⟨t⟩ = u` is `t = $u`), a spliced variable is solved (`$x = t` is `x = ⟨t⟩`), applications of the
   *  same object constant are decomposed (injectivity), distinct object constants and distinct literals
   *  conflict (disjointness), as constructors of a meta family do. Persisted meta values are equal if the
   *  values are (persisting is injective). `None` (postponed) for anything else: object arithmetic
   *  (`⟨1 + 2⟩` is not the literal `⟨3⟩` as code), a persisted value against a literal, an instance of
   *  an object family against an application of the family. `Some(Right(eqs))`: the equations it is
   *  equivalent to. */
  private def objectCode(
      p: SplitProblem,
      a0: Val,
      b0: Val,
      an: Val,
      bn: Val
  ): Option[Either[IndexUnification, List[(Val, Val)]]] =
    val a = Val.unloc(a0)
    val b = Val.unloc(b0)
    def conflict = Some(Left(IndexUnification.Conflict(an, bn)))
    def args(sp: Spine): Option[List[Val]] =
      val as = sp.reverse.collect { case Elim.EApp(x, _) => x }
      Option.when(as.length == sp.length)(as)
    (a, b) match
      case (Val.Quote(x), Val.Quote(y)) => Some(Right(List((x, y))))
      case (Val.Quote(x), y: Val.Rigid) => Some(Right(List((x, vSplice(y)))))
      case (x: Val.Rigid, Val.Quote(y)) => Some(Right(List((vSplice(x), y))))
      case (Val.Rigid(Head.Local(x), List(Elim.ESplice)), y) if p.isFree(x) => Some(Right(List((Val.local(x), vQuote(y)))))
      case (x, Val.Rigid(Head.Local(y), List(Elim.ESplice))) if p.isFree(y) => Some(Right(List((vQuote(x), Val.local(y)))))
      case (Val.Lit(x, Stage.S0), Val.Lit(y, Stage.S0)) => if x == y then Some(Right(Nil)) else conflict
      case (Val.Persist(x), Val.Persist(y)) => Some(Right(List((x, y))))
      case (Val.Rigid(Head.Glob(c1), sp1), Val.Rigid(Head.Glob(c2), sp2)) if isObjectConst(c1) && isObjectConst(c2) =>
        if c1 != c2 then conflict
        else
          (args(sp1), args(sp2)) match
            case (Some(xs), Some(ys)) if xs.length == ys.length => Some(Right(xs.zip(ys)))
            case _ => None
      case (Val.Rigid(Head.Glob(c), _), Val.Lit(_, Stage.S0)) if isObjectConst(c) => conflict
      case (Val.Lit(_, Stage.S0), Val.Rigid(Head.Glob(c), _)) if isObjectConst(c) => conflict
      // the base types, as object types: distinct from each other and from the declared object types
      case (Val.Base(x, Stage.S0), Val.Base(y, Stage.S0)) => if x == y then Some(Right(Nil)) else conflict
      case (Val.Base(_, Stage.S0), Val.Rigid(Head.Glob(c), _)) if isObjectConst(c) => conflict
      case (Val.Rigid(Head.Glob(c), _), Val.Base(_, Stage.S0)) if isObjectConst(c) => conflict
      case _ => None

  /** The atom a weak-head form is ([[Matching.atomKey]]); anything else is none without being evaluated
   *  further. */
  private def atomOf(v: Val): Option[Tm] = v match
    case _: Val.Lit | _: Val.Nat | _: Val.Quote | _: Val.Obj => atomKey(v)
    case _ => None

  /** `x = t` (`t` in weak-head form, `shown` as the equation has it): solve, unless `x` occurs in `t` (a
   *  cycle under constructors is a conflict). The occurs check reads `t` back only if `x` is in it as it
   *  is ([[Core.mentions]]). */
  private def solveVar(p: SplitProblem, x: Int, t: Val, shown: Val): Either[IndexUnification, SplitProblem] =
    if !mentions(x, t) || !occurs(p.size - x - 1, quote(p.size, t)) then
      // the program of a module body stays folded (reference: std/semantics): judgments print as such, and
      // its applications unify by their arguments ([[Core.unify]])
      val solution = shown match
        case Val.Top(id, _, _) if globals(id).program != null => shown
        case _ => t
      Right(p.solve(core, x, solution))
    else if constructorTerm(t) then Left(IndexUnification.Conflict(Val.local(x), shown))
    else Left(IndexUnification.Stuck(Val.local(x), shown))

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

  /** A side of an equation between numeral forms, with successors taken off one weak-head step at a time:
   *  `count` successors over `rest`, which is zero (`null`), or a value that is not a numeral form in
   *  weak-head form (`done`), or a value not evaluated yet. */
  private final class NatSide(val fam: Int, var count: BigInt, var rest: Val | Null, var done: Boolean):
    def isZero: Boolean = done && rest == null

    /** One weak-head step of the rest. */
    def step(): Unit =
      val w = whnf(rest.nn)
      w match
        case Val.Nat(_, n) => count += n; rest = null; done = true
        case Val.NatAdd(_, b, k) => count += k; rest = b
        case Val.Rigid(Head.Glob(c), List(Elim.EApp(x, Icit.Expl))) if isSuccessor(c) => count += 1; rest = x
        case Val.Rigid(Head.Glob(c), Nil) if constantOf(c) => rest = null; done = true
        case other => rest = other; done = true

  private def natSide(v: Val): NatSide =
    val s = NatSide(natFamilyOf(v), BigInt(0), v, false)
    s.step()
    s

  /** An equation between numeral forms (in weak-head form) as the equation between what is left after the
   *  smaller number of successors is taken off both sides, or `None` if they conflict: what comparing the
   *  sides as numerals or successors applied to a base ([[Naturals.natChain]]) gives, with successors
   *  taken off a side only as far as that is decided (`0 = double 9223372036854775807` conflicts after
   *  one step of `double`, which gives two successors). */
  private def numerals(a: Val, b: Val): Option[(Val, Val)] =
    val x = natSide(a)
    val y = natSide(b)
    var out: Option[Option[(Val, Val)]] = None
    while out.isEmpty do
      if x.done && y.done then
        out = Some(
          if x.isZero && y.isZero then None
          else if x.isZero then Option.when(x.count >= y.count)((Val.Nat(y.fam, x.count - y.count), y.rest.nn))
          else if y.isZero then Option.when(y.count >= x.count)((x.rest.nn, Val.Nat(x.fam, y.count - x.count)))
          else
            val m = x.count.min(y.count)
            Some((natAdd(x.fam, x.rest.nn, x.count - m), natAdd(y.fam, y.rest.nn, y.count - m)))
        )
      // a numeral against more successors than it has
      else if x.isZero && y.count > x.count then out = Some(None)
      else if y.isZero && x.count > y.count then out = Some(None)
      // a base under fewer successors than the other side has so far: it equals the rest of that side
      else if x.done && !x.isZero && y.count >= x.count then out = Some(Some((x.rest.nn, natAdd(y.fam, y.rest.nn, y.count - x.count))))
      else if y.done && !y.isZero && x.count >= y.count then out = Some(Some((natAdd(x.fam, x.rest.nn, x.count - y.count), y.rest.nn)))
      else if !x.done && (y.done || x.count <= y.count) then x.step()
      else y.step()
    out.get

  private def constructorTerm(v: Val): Boolean = v match
    case Val.Rigid(Head.Glob(c), _) => isConstructor(c)
    case _: Val.Nat | _: Val.NatAdd => true
    // an object constant applied, quoted: object terms are finite trees, so `x = ⟨c $x⟩` is a cycle
    case Val.Quote(t) =>
      Val.unloc(t) match
        case Val.Rigid(Head.Glob(c), _) => isObjectConst(c)
        case _ => false
    case _ => false
