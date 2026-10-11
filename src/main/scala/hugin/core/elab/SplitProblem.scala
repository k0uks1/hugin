package hugin.core
package elab

/** The context of one branch of a case tree under construction: a variable per level (the function's
 *  arguments, then the arguments of the constructors matched so far). Matching and index unification
 *  *solve* variables: `values(l)` is then a term over the other variables instead of the variable itself.
 *  Old values (of clauses, the target type) are brought up to date by [[norm]], which re-evaluates them
 *  in the current values; since values refer to variables by level, solutions may mention variables of
 *  any level. */
final case class SplitProblem(names: Vector[Name], types: Vector[Val], values: Vector[Val]):
  def size: Int = names.length

  /** The values as an environment (innermost first), computed once per problem. */
  lazy val env: List[Val] = values.reverse.toList
  def isFree(l: Int): Boolean = values(l) == Val.local(l)

  def extend(name: Name, ty: Val): SplitProblem =
    SplitProblem(names :+ name, types :+ ty, values :+ Val.local(size))

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

  /** Solves the free variable `x` by `t` (which must not mention `x`). */
  def solve(core: Core, x: Int, t: Val): SplitProblem =
    val p = copy(values = values.updated(x, t))
    p.copy(values = p.values.map(p.norm(core, _)), types = p.types.map(p.norm(core, _)))

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

  def unifyIndices(p0: SplitProblem, eqs0: List[(Val, Val)]): IndexUnification =
    var p = p0
    var eqs = eqs0
    var result: Option[IndexUnification] = None
    while result.isEmpty && eqs.nonEmpty do
      val (a0, b0) = eqs.head
      eqs = eqs.tail
      val a = force(p.norm(core, a0))
      val b = force(p.norm(core, b0))
      if quote(p.size, a) != quote(p.size, b) then
        (freeVar(p, a), freeVar(p, b)) match
          case (Some(x), Some(y)) => p = p.solve(core, x.max(y), Val.local(x.min(y)))
          case (Some(x), None) => solveVar(p, x, b).fold(r => result = Some(r), q => p = q)
          case (None, Some(y)) => solveVar(p, y, a).fold(r => result = Some(r), q => p = q)
          case (None, None) =>
            (a, b) match
              case (Val.Rigid(Head.Glob(c1), sp1), Val.Rigid(Head.Glob(c2), sp2)) if isConstructor(c1) && isConstructor(c2) =>
                if c1 != c2 || sp1.length != sp2.length then result = Some(IndexUnification.Conflict(a, b))
                else eqs = sp1.reverse.zip(sp2.reverse).collect { case (Elim.EApp(x, _), Elim.EApp(y, _)) => (x, y) } ++ eqs
              case (Val.Lit(x, _), Val.Lit(y, _)) if x != y => result = Some(IndexUnification.Conflict(a, b))
              case _ => result = Some(IndexUnification.Stuck(a, b))
    result.getOrElse(IndexUnification.Solved(p))

  private def freeVar(p: SplitProblem, v: Val): Option[Int] = v match
    case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => Some(x)
    case _ => None

  /** `x = t`: solve, unless `x` occurs in `t` (a cycle under constructors is a conflict). */
  private def solveVar(p: SplitProblem, x: Int, t: Val): Either[IndexUnification, SplitProblem] =
    if !occurs(p.size - x - 1, quote(p.size, t)) then Right(p.solve(core, x, t))
    else if constructorTerm(t) then Left(IndexUnification.Conflict(Val.local(x), t))
    else Left(IndexUnification.Stuck(Val.local(x), t))

  private def constructorTerm(v: Val): Boolean = force(v) match
    case Val.Rigid(Head.Glob(c), _) => isConstructor(c)
    case _ => false
