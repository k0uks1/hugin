package hugin.core
package elab

import hugin.syntax.Trees.*

/** Member functions of module bodies (reference: modules): a declaration `f : A.` of a body with a meta
 *  type, and the clauses `f p̄ = e.` of the same body.
 *
 *  A member function is lambda-lifted ([[Lifting]]), as the local functions of `where` blocks are: a
 *  hidden global function named after the member's path (`lib.double`, `tc.step` in a functor `tc`)
 *  over the bound variables of the body's context (the parameters of enclosing functors, the object
 *  constants of the enclosing bodies and of this one). The member is that global applied to the context,
 *  so the function is elaborated once per body, not per instance, and every instance's field is the
 *  shared function applied to the instance's arguments and object constants. The clauses are elaborated
 *  after all members, in the context of the whole body (forward references, mutual recursion), each
 *  function a block of its own ([[Core.inBlock]]); coverage and termination are those of the written
 *  clauses. */
trait MemberFunctions:
  self: Elaborator =>
  import core.*

  /** A member function: its lifted global and the context it was lifted from. */
  final case class MemberFunction(name: Name, id: Int, cx: Cxt)

  /** The names of the members whose definitions are being elaborated, innermost first (for the paths of
   *  member functions in nested bodies). */
  private var memberPath: List[Name] = Nil

  def inMember[A](n: Name)(f: => A): A =
    val saved = memberPath
    memberPath = n :: memberPath
    try f
    finally memberPath = saved

  /** The path of the member `n` of the body being elaborated, after the definition that contains it. */
  private def pathOf(n: Name): Name =
    val top = if hint.nonEmpty then hint else "_"
    (top :: memberPath.reverse ::: List(n)).mkString(".")

  /** The signature `f : A.` of a member function: lifted from the context `c` it is elaborated in. Its
   *  unknowns must be solved by it (E0903), as a top-level signature's. A declaration of an object
   *  constant with clauses is an object constant (its clauses are E0914). */
  def functionMember(c: Cxt, d: Decl, parts: BodyItems): (Cxt, Member, Option[MemberFunction]) =
    if parts.broken(d.name.name) then
      // a clause has a syntax error: the function is left out, and its uses are not reported
      state.erroneous += d.name.name
      syntaxError(d.span)
    val start = metas.length
    val (ty, st) = declType(d, c)
    if st == Stage.S0 then
      val (cx, m) = objectMember(c, d, parts)
      (cx, m, None)
    else
      checkSolved(start)
      val zty = zonk(c.env, c.lvl, ty)
      val (id, value) = liftedFunction(c, pathOf(d.name.name), zty, d.name.span, d.span)
      val (cx, m) = defined(c, d.name, zty, quote(c.lvl, value), d.span)
      (cx, m, Some(MemberFunction(d.name.name, id, c)))

  /** The clauses of the body, by function in order of appearance, each group a block of its own. */
  def elabMemberClauses(cb: Cxt, parts: BodyItems, members: List[Member], functions: Map[Name, MemberFunction]): Unit =
    val groups = scala.collection.mutable.LinkedHashMap.empty[Name, List[Item]]
    for item <- parts.clauses do
      clauseHead(item) match
        case Some(n) => groups(n) = groups.getOrElse(n, Nil) :+ item
        case None => reportingErrors(surfaceClause(item)) // E0915: not a name applied to patterns
    for (n, group) <- groups if !parts.broken(n) do
      functions.get(n) match
        case Some(f) => clauseGroup(cb, f, group)
        case None => reportingErrors(notAFunction(n, group, members, parts))

  /** Clauses of `n`, which is not a member function of the body. */
  private def notAFunction(n: Name, group: List[Item], members: List[Member], parts: BodyItems): Nothing =
    members.find(_.name == n) match
      case Some(m) =>
        val kind = m.kind match
          case MemberKind.Object(_) => "an object constant"
          case MemberKind.Defined(_) => "a definition"
        fail(ClauseProblem.NotDefinableByClauses(n, group.head.span, m.span, kind))
      // its declaration was left out: reported there
      case None if parts.declares(n) || state.erroneous(n) => syntaxError(group.head.span)
      case None => fail(ClauseProblem.ClausesWithoutDeclaration(n, group.head.span, inBody = true))

  private def memberClause(item: Item): Option[SurfaceClause] = item match
    case d: Def => Some(defClause(d))
    case other => surfaceClause(other)

  /** The clauses of the member function `f`, in the context `cb` of the members elaborated before them
   *  (all of them): its prelude re-defines those. `cb` binds the variables `f` was lifted over, since
   *  the object constants are bound before the first member function ([[ModuleBodies]]). */
  private def clauseGroup(cb: Cxt, f: MemberFunction, group: List[Item]): Unit =
    if boundVars(cb).length != boundVars(f.cx).length then throw Impossible("an object constant after a member function")
    val cx = cb
    inBlock {
      val start = metas.length
      val mark = toolingMark
      try
        undoOnFailure {
          // the records of a failed group are shown before its metas are undone
          try
            elabFunction(f.id, padded(cx, group.flatMap(memberClause)), prelude(cx))
            checkSolved(start)
          catch
            case e: ElabError =>
              flushFailedSince(mark)
              throw e
        }
      catch
        case e: ElabError if retriedOutside(e) => throw e
        case e: ElabError =>
          report(e)
          // its case tree may refer to the undone metas: the function is stuck
          globals(f.id).kind match
            case GlobalKind.Function(arity, Some(_)) => globals(f.id).kind = GlobalKind.Function(arity, None)
            case _ =>
    }
