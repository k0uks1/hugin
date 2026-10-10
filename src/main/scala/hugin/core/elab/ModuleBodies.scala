package hugin.core
package elab

import hugin.syntax.{Trees, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

import scala.collection.mutable

/** Module bodies `{ items }` (reference: modules): record values whose object members are generative.
 *
 *  The declarations and definitions of a body are its *members*, elaborated in the context of the body
 *  (the enclosing variables, such as a functor's parameters) and of the members before them; each member
 *  is a variable of that context: an object constant `r : τ` is a variable of type `⇑τ` (as a functor's
 *  relation parameter is), a definition is let-bound. Members may be written in any order: one that
 *  refers to a later one is retried after it, and a member's name shadows the file's in the whole body
 *  ([[ElabState.bodyDeclared]]). A declaration `f : A.` with clauses `f p̄ = e.` in the body is a
 *  *member function* ([[MemberFunctions]]): its clauses are elaborated after the members, each function
 *  a block of its own; so are the rules of a body's formula functions. Then the body's object items (rules, queries, directives, edges) are elaborated
 *  in the context of all members. The body's type is the record type of its members, a telescope, and
 *  its value is a record: evaluation creates fresh object constants for the object members of each
 *  instance ([[Modules]]), and the handover stages the instance's items. */
trait ModuleBodies:
  self: Elaborator =>
  import core.*

  /** The items of a body by role: members (declarations and definitions), clauses of member functions,
   *  rules of formula functions, object items; the names of the member functions (declarations with
   *  clauses in the body), of the formula functions (other declarations `f : τ̄ -> prop.` without a
   *  definition), and of the functions with a clause or rule with a syntax error. */
  final case class BodyItems(
      members: List[Item],
      clauses: List[Item],
      rules: List[Rule],
      objects: List[Item],
      functions: Set[Name],
      formulas: Set[Name],
      broken: Set[Name]
  ):
    def lifted(n: Name): Boolean = functions(n) || formulas(n)

    def declares(n: Name): Boolean = members.exists(memberName(_).contains(n))

  def inferModuleBody(c: Cxt, body: Trees.ModuleBody): (Tm, Val, Stage) =
    val parts = bodyItems(body.items)
    // the names that items with syntax errors might declare: their uses are not reported (`docs/PARSER.md`, §5)
    state.erroneous ++= body.items.filter(TreeOps.hasSyntaxErrors).flatMap(mightDeclare)
    val saved = state.bodyDeclared
    val savedLeftOut = state.leftOutMembers
    state.bodyDeclared = saved ++ parts.members.flatMap(memberName)
    try
      val functions = mutable.LinkedHashMap.empty[Name, MemberFunction]
      val (cb, members) = elabMembers(c, parts, functions)
      recordBody(c, cb, body.span, members, parts.members)
      if !file.signaturesOnly then elabMemberClauses(cb, parts, members, functions.toMap)
      val items = objectItems(cb, parts.objects)
      val mb = hugin.core.ModuleBody(nextBodyId(), body.span, members, items)
      val ty = Tm.RecTy(members.map(m => (m.name, m.ty)), Nil, members.map(m => (m.span, m.declSpan)))
      (Tm.Module(mb, (0 until c.lvl).map(Tm.Var(_)).toList), ev(c, ty), Stage.S1)
    finally
      state.bodyDeclared = saved
      state.leftOutMembers = savedLeftOut

  private def bodyItems(items: List[Item]): BodyItems =
    val declared = items.collect { case d: Decl => d.name.name }.toSet
    val (clauses, rest) = items.partition {
      case _: Clause => true
      case d: Def => declared(d.name.name)
      case _ => false
    }
    val heads = clauses.flatMap(clauseHead)
    val (members, objects) = rest.partition {
      case _: Decl | _: Def => true
      case _ => false
    }
    def plain(d: Decl) = d.defn.isEmpty && d.params.isEmpty && d.sup.isEmpty
    val functions = members.collect { case d: Decl if plain(d) && heads.contains(d.name.name) => d.name.name }.toSet
    val formulas = members.collect {
      case d: Decl if plain(d) && !functions(d.name.name) && endsInProp(d.tpe) => d.name.name
    }.toSet
    val (rules, others) = objects.partition(clauseOf(formulas)(_).isDefined)
    val broken = (clauses.filter(TreeOps.hasSyntaxErrors).flatMap(clauseHead) ++
      rules.filter(TreeOps.hasSyntaxErrors).flatMap(clauseOf(formulas))).toSet
    BodyItems(members, clauses, rules.collect { case r: Rule => r }, others, functions, formulas, broken)

  /** The function a clause of a body defines. */
  def clauseHead(item: Item): Option[Name] = item match
    case Clause(lhs, _, _) => TreeOps.headName(lhs).map(_.name)
    case d: Def => Some(d.name.name)
    case _ => None

  /** The object items, the body's edges first: object typing of its rules needs them. */
  private def objectItems(cb: Cxt, objects: List[Item]): List[CoreItem] =
    val (edges, others) = objects.partition(_.isInstanceOf[SubEdge])
    val edgeItems = edges.flatMap(item => reportingErrors(objectItem(cb, item)).getOrElse(Nil))
    val saved = state.localEdges
    state.localEdges = edgeItems.collect { case CoreItem.EdgeItem(sub, sup, _) => (ev(cb, sub), ev(cb, sup)) } ++ saved
    try edgeItems ++ others.flatMap(item => reportingErrors(objectItem(cb, item)).getOrElse(Nil))
    finally state.localEdges = saved

  def reportingErrors[A](a: => A): Option[A] =
    try Some(a)
    catch
      case e: ElabError if retriedOutside(e) => throw e
      case e: ElabError =>
        report(e)
        None

  /** An error about a name the file declares later (a directive, a function), or whose declaration is
   *  pending (it may still fail, and its uses are then not reported): the definition of the body is
   *  retried after it. */
  def retriedOutside(e: ElabError): Boolean =
    e.unresolved.exists(n => state.declaredHere(n) && lookupGlobal(n).forall(globals(_).pending))

  /** Elaborates the members in dependency order (as the top level's declarations), in two phases: first
   *  the object constants and the definitions they need, then the signatures of the member functions with
   *  the other definitions. So the context that member functions are lifted over (the enclosing variables
   *  and the body's object constants) is fixed before the first of them, and all of them take the same
   *  leading arguments ([[MemberFunctions]]). An object constant that waits for a member function, through
   *  a definition, is left out with its error. The order of the members is decided here only. */
  private def elabMembers(c: Cxt, parts: BodyItems, functions: mutable.Map[Name, MemberFunction]): (Cxt, List[Member]) =
    var cb = c
    val members = mutable.ListBuffer.empty[Member]
    def isSignature(item: Item) = item match
      case d: Decl => parts.lifted(d.name.name)
      case _ => false
    def isObjectConstant(item: Item) = item match
      case d: Decl => !parts.lifted(d.name.name) && (d.defn.isEmpty || isStructDecl(d))
      case _ => false
    def attempt(item: Item): Unit =
      val (next, m, f) = undoOnFailure(member(cb, item, parts))
      members.find(_.name == m.name).foreach(first => duplicate(m, first))
      cb = next
      members += m
      f.foreach(fn => functions(fn.name) = fn)
    def finish(item: Item): Unit =
      try attempt(item)
      catch
        case e: ElabError if retriedOutside(e) => throw e
        case e: ElabError => failedMember(item, e)
    /* the items that wait for a later name (of an item still pending, or in `waitingFor`) are retried
       after the others, until none makes progress; returns those left */
    def inDependencyOrder(items: List[Item], waitingFor: Set[Name]): List[Item] =
      var pending = items
      var progress = true
      while pending.nonEmpty && progress do
        val before = pending.length
        pending = pending.filter { item =>
          val later = pending.filter(_ ne item).flatMap(memberName).toSet ++ waitingFor
          try
            attempt(item)
            false
          catch
            case e: ElabError =>
              if e.unresolved.exists(later) then true
              else if retriedOutside(e) then throw e
              else
                failedMember(item, e)
                false
        }
        progress = pending.length < before
      pending
    val (signatures, others) = parts.members.partition(isSignature)
    val left = inDependencyOrder(others, signatures.flatMap(memberName).toSet)
    val (stuckObjects, definitions) = left.partition(isObjectConstant)
    stuckObjects.foreach(finish)
    inDependencyOrder(definitions ++ signatures, Set.empty).foreach(finish)
    (cb, members.toList)

  /** Reports the error of a member that is left out (E0105 if it refers to itself); its name is
   *  erroneous, so its uses in the body are not reported again. */
  private def failedMember(item: Item, e: ElabError): Unit =
    memberIdent(item) match
      case Some(n) if e.unresolved.contains(n.name) =>
        reporter.report(ElabProblem.SelfReference(n.name, e.diag.labels.head.span, n.span).toDiagnostic)
      case _ => report(e)
    memberName(item).foreach(state.erroneous += _)

  private def duplicate(m: Member, first: Member): Nothing = fail(ElabProblem.DuplicateMember(m.name, m.span, first.span))

  def memberName(item: Item): Option[Name] = memberIdent(item).map(_.name)

  private def memberIdent(item: Item): Option[Ident] = item match
    case d: Decl => Some(d.name)
    case d: Def => Some(d.name)
    case _ => None

  /** One member, the context extended with it, and the member function it declares. */
  private def member(c: Cxt, item: Item, parts: BodyItems): (Cxt, Member, Option[MemberFunction]) =
    if TreeOps.hasSyntaxErrors(item) then
      // dropped silently; uses of its name are not reported (`docs/PARSER.md`, §5)
      memberName(item).foreach(state.erroneous += _)
      syntaxError(item.span)
    item match
      case d: Decl if parts.lifted(d.name.name) => functionMember(c, d, parts)
      case _ =>
        val (cx, m) = memberOf(c, item)
        (cx, m, None)

  private def memberOf(c: Cxt, item: Item): (Cxt, Member) = item match
    case d: Decl if d.defn.isDefined && !isStructDecl(d) =>
      val (ty, tm) = inMember(d.name.name)(declDefinition(c, d, d.defn.get))
      defined(c, d.name, ty, tm, d.span)
    case d: Def =>
      val (ty, tm) = inMember(d.name.name)(definition(c, d.params, d.rhs))
      defined(c, d.name, ty, tm, d.span)
    case d: Decl => objectMember(c, d)
    case other => throw Impossible(s"not a member: $other")

  def defined(c: Cxt, name: Ident, ty: Tm, tm: Tm, span: Span): (Cxt, Member) =
    val zty = zonk(c.env, c.lvl, ty)
    val ztm = zonk(c.env, c.lvl, tm)
    val tyV = ev(c, zty)
    (define(c, name.name, tyV, ev(c, ztm)), Member(name.name, MemberKind.Defined(ztm), zty, name.span, span))

  /** An object constant of the body: a variable of type `⇑τ`. */
  def objectMember(c: Cxt, d: Decl): (Cxt, Member) =
    if d.sup.isDefined then unsupportedAt(d.span, "refinements in module bodies")
    if d.params.nonEmpty then unsupportedAt(d.span, "families of object constants in module bodies")
    val (ty, decl) =
      if isStructDecl(d) then (structType(c, d), ObjDecl.Struct)
      else
        val (t, st) = declType(d, c)
        if st != Stage.S0 then unsupportedAt(d.span, metaWithoutDefinition(c, t))
        (t, objectDecl(d, ev(c, t)))
    val lifted = Tm.Lift(zonk(c.env, c.lvl, ty))
    (
      bind(c, d.name.name, ev(c, lifted), Stage.S1, BinderOrigin.Member),
      Member(d.name.name, MemberKind.Object(decl), lifted, d.name.span, d.span)
    )

  /** What E0907 says about a meta declaration of a body without a definition and without clauses. */
  private def metaWithoutDefinition(c: Cxt, ty: Tm): String =
    force(telescope(ev(c, ty))._2) match
      case Val.U1(_) => "meta inductive families in module bodies"
      case _ => "meta declarations without a definition or clauses in module bodies"

  private def objectItem(c: Cxt, item: Item): List[CoreItem] =
    if TreeOps.hasSyntaxErrors(item) then syntaxError(item.span)
    objectItemOf(c, item)

  private def objectItemOf(c: Cxt, item: Item): List[CoreItem] = item match
    case r: Rule if isSpliceItem(r) => unsupportedAt(r.span, "reflected items (`$e.`) in module bodies")
    case r: Rule => List(ruleItem(c, r))
    case q: Query => List(queryItem(c, q))
    case d: Directive => directiveItems(c, d, inBody = true)
    case e: SubEdge => List(edgeItem(c, e))
    case other => throw Impossible(s"not an object item: $other")
