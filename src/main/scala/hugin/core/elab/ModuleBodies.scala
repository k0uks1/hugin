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
 *  relation parameter is), a definition is let-bound. Members may be written in any order: they are
 *  elaborated in dependency order ([[elabMembers]]), and a member's name shadows the file's in the whole
 *  body ([[ElabState.bodyDeclared]]). A declaration `f : A.` with clauses `f p̄ = e.` in the body is a
 *  *member function* ([[MemberFunctions]]): its clauses are elaborated in its component, after the
 *  component's members, each function a block of its own; so are the rules of a body's formula
 *  functions. Then the body's object items
 *  (rules, queries, directives, edges) are elaborated in the context of all members. The body's type
 *  is the record type of its members, a telescope, and its value is a record: evaluation creates fresh
 *  object constants for the object members of each instance ([[Modules]]), and the handover stages the
 *  instance's items. */
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
    val all0 = bodyItems(body.items)
    // `%opaque m.` names members of the body (#186 P9g): known before they are elaborated
    val (opaques, others) = all0.objects.partition {
      case Directive("opaque", _) => true
      case _ => false
    }
    val all = all0.copy(objects = others)
    // the program-dependent members, elaborated after the body's object items (#186 P9f)
    val (parts, later) = programPhase(c, all)
    // the names that items with syntax errors might declare: their uses are not reported (`docs/PARSER.md`, §5)
    state.erroneous ++= body.items.filter(TreeOps.hasSyntaxErrors).flatMap(mightDeclare)
    val saved = state.bodyDeclared
    val savedLeftOut = state.leftOutMembers
    val savedHere = hereState
    val savedAmbient = ambient
    val savedDependent = state.programDependent
    val savedUses = bodyUses
    val savedOpaque = opaqueMembers
    val memberNames = all.members.flatMap(memberName)
    state.bodyDeclared = saved ++ memberNames
    // the members shadow the enclosing scope's program-dependent names; `here` is the body's program
    state.programDependent =
      savedDependent -- memberNames ++ later.fold(Map.empty)(_._2.chains.map((n, ch) => n -> ProgramPhase.Dependence(ch, true)))
    hereState = HereState.Unavailable(true)
    ambient = None
    bodyUses = mutable.HashMap.empty
    opaqueMembers = opaques.flatMap {
      case Directive(_, DirArgs.Apply(args, None)) => args.collect { case Ident(n) => n }
      case _ => Nil
    }.toSet
    try
      val functions = mutable.LinkedHashMap.empty[Name, MemberFunction]
      val (cb0, members0) = elabMembers(c, parts, functions)
      if later.isEmpty then recordBody(c, cb0, body.span, members0, all.members)
      val items = objectItems(cb0, parts.objects)
      val context = c.binders.reverse.map(b => (b.name, b.tyTm))
      val id = nextBodyId()
      val (cb, members, shifted) = later match
        case None => (cb0, members0, items)
        case Some((deferred, _)) =>
          val name = Option.when(hint.nonEmpty && !inMemberDefinition)(hint)
          hereState = bodyHere(hugin.core.ModuleBody(id, body.span, members0, items, context), c.lvl, name)
          // its own relations and its context's relations, written unqualified, are its propositions (#186 P9g)
          ambient = Some(bodyAmbient(c, all))
          state.programDependent = savedDependent -- memberNames
          val (cb1, members1) = elabMembers(cb0, deferred, functions)
          // the object items see the members after them as well: their variables are shifted past them
          (cb1, members0 ++ members1, items.map(shiftItem(_, members1.length)))
      if later.isDefined then recordBody(c, cb, body.span, members, all.members)
      opaques.foreach { case d: Directive => reportingErrors(checkOpaqueMembers(d, members)); case _ => }
      val free = freeMembers(members, bodyUses.view.mapValues(_.toSet).toMap)
      val mb = hugin.core.ModuleBody(id, body.span, members, shifted, context, free)
      val ty = Tm.RecTy(members.map(m => (m.name, m.ty)), Nil, members.map(m => (m.span, m.declSpan)))
      (Tm.Module(mb, (0 until c.lvl).map(Tm.Var(_)).toList), ev(c, ty), Stage.S1)
    finally
      state.bodyDeclared = saved
      state.leftOutMembers = savedLeftOut
      state.programDependent = savedDependent
      hereState = savedHere
      ambient = savedAmbient
      bodyUses = savedUses
      opaqueMembers = savedOpaque

  /** An object item of a body, elaborated in the context of its members so far, in a context with `by`
   *  more members (a rule's and a query's variables bind in its terms). */
  private def shiftItem(item: CoreItem, by: Int): CoreItem =
    def vars(vs: List[(Name, Tm)]) = vs.zipWithIndex.map { case ((x, t), i) => (x, Tm.shift(t, by, i)) }
    item match
      case r: CoreItem.RuleItem =>
        val n = r.vars.length
        r.copy(vars = vars(r.vars), heads = r.heads.map(Tm.shift(_, by, n)), body = r.body.map(Tm.shift(_, by, n)))
      case q: CoreItem.QueryItem => q.copy(vars = vars(q.vars), body = Tm.shift(q.body, by, q.vars.length))
      case e: CoreItem.EdgeItem => e.copy(sub = Tm.shift(e.sub, by), sup = Tm.shift(e.sup, by))
      case d: CoreItem.DeclItem => d.copy(decl = Tm.shift(d.decl, by), attached = d.attached.map(Tm.shift(_, by)))
      case g: CoreItem.GlobalItem => g

  /** The items of a body split into those elaborated before its object items and its program-dependent
   *  members with their clauses and rules ([[ProgramPhase]]), with why each is program-dependent. An object
   *  constant stays before: if it needs a program-dependent member, that is a cycle (E0962). */
  private def programPhase(c: Cxt, parts: BodyItems): (BodyItems, Option[(BodyItems, ProgramPhase.Deferred)]) =
    def isObjectConstant(item: Item) = item match
      case d: Decl => !parts.lifted(d.name.name) && (d.defn.isEmpty || isStructDecl(d))
      case _ => false
    val programOfFree = !parts.members.flatMap(memberName).contains("programOf")
    // the relations its members may write unqualified as its propositions (#186 P9g)
    val context = contextVariables(c)
    val own = ProgramPhase.OwnRelations(
      ownRelationNames(parts),
      (x, r) => context(x) && c.scope.get(x).exists(relationField(c, _, r)),
      context.nonEmpty
    )
    val (_, deferred) =
      ProgramPhase.classify(parts.members ++ parts.clauses ++ parts.rules, programOfFree, i => !isObjectConstant(i), own)
    if deferred.isEmpty then (parts, None)
    else
      val later = deferred.items.toSet
      val now = parts.copy(
        members = parts.members.filterNot(later),
        clauses = parts.clauses.filterNot(later),
        rules = parts.rules.filterNot(later)
      )
      val after = parts.copy(
        members = parts.members.filter(later),
        clauses = parts.clauses.filter(later),
        rules = parts.rules.filter(later),
        objects = Nil
      )
      (now, Some((after, deferred)))

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

  /** Elaborates the members, the clauses of the member functions and the rules of the formula functions in
   *  dependency order, as a file's items (reference: modules, "Module bodies"; `docs/design/elab-order.md`,
   *  5.5). First the object constants and the definitions their types mention, so that the context member
   *  functions are lifted over (the enclosing variables and the body's object constants) is fixed before
   *  the first of them, and all of them take the same leading arguments ([[MemberFunctions]]); an object
   *  constant that waits for a member function, through a definition, is left out with its error. Then the
   *  other members by the components of their dependency graph ([[ElabOrder]], [[elabMemberComponent]]).
   *  The order of the members is decided here only. */
  private def elabMembers(c: Cxt, parts: BodyItems, functions: mutable.Map[Name, MemberFunction]): (Cxt, List[Member]) =
    var cb = c
    val members = mutable.ListBuffer.empty[Member]
    def isObjectConstant(item: Item) = item match
      case d: Decl => !parts.lifted(d.name.name) && (d.defn.isEmpty || isStructDecl(d))
      case _ => false
    def attempt(item: Item): Unit =
      val (next, m, f) = collectingUses(memberName(item).getOrElse("_"))(undoOnFailure(member(cb, item, parts)))
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
    // the object constants and the definitions (not lifted) that their types mention, transitively
    val byName = parts.members.flatMap(i => memberName(i).map(_ -> i)).toMap
    val first = mutable.LinkedHashSet.from(parts.members.filter(isObjectConstant))
    val todo = mutable.Stack.from(first)
    while todo.nonEmpty do
      for n <- ElabOrder.mentions(todo.pop()); d <- byName.get(n) if !parts.lifted(n) && first.add(d) do todo.push(d)
    val firstItems = parts.members.filter(first)
    val others = parts.members.filterNot(first)
    val left = inDependencyOrder(firstItems, others.flatMap(memberName).toSet)
    val (stuckObjects, waiting) = left.partition(isObjectConstant)
    stuckObjects.foreach(finish)
    // the other members, the clause groups and the formula functions' rules, by components
    val rest = (waiting ++ others).sortBy(_.span.start)
    val groups = memberClauseGroups(parts)
    val declared = parts.members.flatMap(memberName).toSet
    val formulaRules =
      for n <- parts.members.flatMap(memberName).distinct if parts.formulas(n)
      yield (n, parts.rules.filter(clauseOf(Set(n))(_).isDefined): List[Item], byName(n).span.start)
    val plan = ElabOrder.plan(
      ElabOrder.Input(rest.map(i => (i, memberName(i).toList)), groups.toList, formulaRules, None, Set.empty, n => !declared(n))
    )
    for component <- plan.components do
      val nodes = component.map(plan.nodes(_))
      val plain = nodes.collect { case n if n.kind == ElabOrder.Kind.Plain => n.items }.flatten.sortBy(_.span.start)
      inDependencyOrder(plain, Set.empty).foreach(finish)
      cb = elabMemberComponent(cb, nodes, parts, members.toList, functions.toMap)
    (cb, members.toList)

  /** The bodies of one component of a module body's members, after its members: the clause groups of its
   *  member functions and the rules of its formula functions, each a block. In a component of several
   *  nodes, its member functions are sealed until it is done, as a file's: no clause group of the
   *  component unfolds another (`DependencyOrder`). At its end, termination and the cycles of its formula
   *  functions are checked and its bodies unfold. Unlike a file's (`DependencyOrder.reevaluateDefinitions`),
   *  its definitions are not evaluated again: none can be stuck at a function of its cycle (docs/NOTES.md,
   *  "Module bodies in dependency order"). */
  private def elabMemberComponent(
      cb: Cxt,
      nodes: List[ElabOrder.Node],
      parts: BodyItems,
      members: List[Member],
      functions: Map[Name, MemberFunction]
  ): Cxt =
    val sealing = nodes.length > 1
    val names = nodes.flatMap(n =>
      n.kind match
        case ElabOrder.Kind.Clauses(f) => List(f)
        case ElabOrder.Kind.Rules(f) => List(f)
        case ElabOrder.Kind.Plain => n.items.flatMap(memberName)
        case ElabOrder.Kind.Derived => Nil
    ).distinct
    val sealedIds = if sealing then names.flatMap(functions.get).map(_.id).filterNot(globals(_).inCycle) else Nil
    sealedIds.foreach(globals(_).inCycle = true)
    val savedCycle = cycleNames
    if sealing then cycleNames = names
    try
      val formulas = if file.signaturesOnly then Nil
      else
        for case ElabOrder.Node(ElabOrder.Kind.Clauses(f), group, _) <- nodes do
          collectingUses(f)(memberClauseGroup(cb, f, group, members, parts, functions))
        nodes.flatMap {
          case ElabOrder.Node(ElabOrder.Kind.Rules(f), rules, _) =>
            collectingUses(f)(memberFormula(cb, f, rules.collect { case r: Rule => r }, parts, functions))
          case _ => None
        }
      checkTermination()
      for id <- sealedIds; kind <- withheld.remove(id) if !rejectedByTermination(id) do globals(id).kind = kind
      sealedIds.foreach(globals(_).inCycle = false)
      finishMemberFormulas(cb, formulas)
      cb
    finally cycleNames = savedCycle

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
    case Decl(_, _, _, _, Some(p: Postulate)) => unsupportedAt(p.span, "postulates (`%postulate`) in module bodies")
    case d: Decl if d.defn.isDefined && !isStructDecl(d) =>
      val (ty, tm) = inMember(d.name.name)(declDefinition(c, d, d.defn.get))
      definedMember(c, d.name, ty, tm, d.span)
    case d: Def =>
      val (ty, tm) = inMember(d.name.name)(definition(c, d.params, d.rhs))
      definedMember(c, d.name, ty, tm, d.span)
    case d: Decl => objectMember(c, d)
    case other => throw Impossible(s"not a member: $other")

  /** A member definition; an opaque one (`%opaque m.` in the body, #186 P9g) is lifted to a global
   *  without a value, as a member function is lifted ([[MemberFunctions]]), so that it never unfolds. */
  private def definedMember(c: Cxt, name: Ident, ty: Tm, tm: Tm, span: Span): (Cxt, Member) =
    if !opaqueMembers(name.name) then defined(c, name, ty, tm, span)
    else
      resolveLiterals(blockStart)
      val zty = zonk(c.env, c.lvl, ty)
      val ztm = zonk(c.env, c.lvl, tm)
      val (_, value) = liftedFunction(c, pathOf(name.name), zty, name.span, span, GlobalKind.Opaque(Some(closeTerm(c, ztm)), None))
      defined(c, name, zty, quote(c.lvl, value), span)

  def defined(c: Cxt, name: Ident, ty: Tm, tm: Tm, span: Span): (Cxt, Member) =
    resolveLiterals(blockStart)
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

  // ---------------------------------------------------------------- locale-style members (#186 P9g)

  /** The members named by the body's `%opaque` items, while it is elaborated; the lifted globals of the
   *  member functions they name. */
  var opaqueMembers: Set[Name] = Set.empty
  val opaqueLifted: mutable.Set[Int] = mutable.HashSet.empty

  /** The local names that each member of the body being elaborated resolves (its declaration, definition,
   *  clauses or rules), for [[freeMembers]]; and those of the member being elaborated. */
  private var bodyUses: mutable.Map[Name, mutable.Set[Name]] = mutable.HashMap.empty
  private var memberUses: mutable.Set[Name] | Null = null

  /** A local name resolved ([[Names.resolve]]): a use of the member being elaborated. */
  def noteLocalUse(n: Name): Unit =
    val u = memberUses
    if u != null then u += n

  private def collectingUses[A](n: Name)(f: => A): A =
    val saved = memberUses
    val mine = mutable.HashSet.empty[Name]
    memberUses = mine
    try f
    finally
      memberUses = saved
      bodyUses.getOrElseUpdate(n, mutable.HashSet.empty) ++= mine
      if saved != null then saved ++= mine

  /** The meta members that mention no object constant of the body, directly or through other members,
   *  with the members each mentions: the greatest set closed under the members' uses. A use is a local
   *  name resolved while the member was elaborated, so a binder named like an object constant counts as
   *  a mention (a member is then read through an instance, as before). */
  private def freeMembers(members: List[Member], uses: Map[Name, Set[Name]]): Map[Name, Set[Name]] =
    val objects = members.collect { case m if m.kind.isInstanceOf[MemberKind.Object] => m.name }.toSet
    val defined = members.collect { case m if m.kind.isInstanceOf[MemberKind.Defined] => m.name }.toSet
    def usesOf(n: Name) = uses.getOrElse(n, Set.empty)
    var free = defined.filterNot(n => usesOf(n).exists(objects))
    var changed = true
    while changed do
      val next = free.filter(n => usesOf(n).forall(u => !defined(u) || free(u)))
      changed = next.size != free.size
      free = next
    free.map { n =>
      // the members it needs, transitively
      val seen = mutable.LinkedHashSet(n)
      val todo = mutable.Stack(n)
      while todo.nonEmpty do for u <- usesOf(todo.pop()) if defined(u) && seen.add(u) do todo.push(u)
      n -> (seen.toSet - n)
    }.toMap

  /** `%opaque m₁ … mₙ.` in a body: every `mᵢ` must be a member definition or member function of it. */
  private def checkOpaqueMembers(d: Directive, members: List[Member]): Unit = d.args match
    case DirArgs.Apply(args, None) if args.nonEmpty =>
      for a <- args do
        a match
          case n @ Ident(name) =>
            members.find(_.name == name) match
              case Some(m) =>
                m.kind match
                  case MemberKind.Defined(_) =>
                  case MemberKind.Object(_) => fail(DirectiveProblem.NotOpaqueable(name, "an object constant of the body", n.span))
              // its declaration failed (reported there)
              case None if state.erroneous(name) =>
              case None => fail(DirectiveProblem.NotOpaqueable(name, "not a member of this module body", n.span))
          case other => fail(DirectiveProblem.OpaqueArgument(other.span))
    case _ => fail(DirectiveProblem.OpaqueArgument(d.span))

  /** The names of the body's own relations (and structs), which its members write unqualified. */
  private def ownRelationNames(parts: BodyItems): Set[Name] =
    parts.members.collect { case d: Decl if !parts.lifted(d.name.name) && ProgramPhase.declaresRelation(d) => d.name.name }.toSet

  /** The variables of the body's context that it may read relations of (a functor's parameters). */
  private def contextVariables(c: Cxt): Set[Name] =
    c.binders.filter(b => b.defn.isEmpty && c.scope.get(b.name).exists(c.binder(_) eq b)).map(_.name).toSet

  /** What a coerced atom written unqualified in the body's program-dependent members names (#186 P9g): an
   *  own relation, a member bound in the body (or, in a member function's clauses, re-bound for them);
   *  or a relation `x.r` of a variable `x` of the body's context `c0`. A local variable of the same name
   *  shadows them. */
  private def bodyAmbient(c0: Cxt, parts: BodyItems): Ambient =
    val own = ownRelationNames(parts)
    val context = contextVariables(c0)
    def member(b: Binder) = b.origin == BinderOrigin.Member || b.defn.isDefined && b.site.isEmpty
    Ambient(
      (c, n) => own(n) && c.scope.get(n).exists(l => member(c.binder(l))),
      (c, x, r) => context(x) && c.scope.get(x).exists(l => c.binder(l).site.isEmpty && relationField(c, l, r)),
      body = true
    )
