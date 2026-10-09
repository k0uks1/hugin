package hugin.core
package elab

import hugin.syntax.Trees.*
import hugin.syntax.TreeOps.hasSyntaxErrors

/** The items of a program: elaborated one by one, each with error recovery (an item with an error is
 *  reported and dropped), in three phases: declarations and definitions; the clauses of functions (which
 *  may refer to every declaration, also recursively); object items (rules, queries, directives). The
 *  first two are the program's *declarations*, which the object items are elaborated against, each on its
 *  own ([[hugin.core.ProgramElab]]). Finally the termination of the functions is checked.
 *
 *  Each declaration, clause group (a function, a formula function) and object item is a *block*
 *  ([[Core.inBlock]]): the unknowns of earlier blocks are frozen while it is elaborated, so it can neither
 *  solve them nor be changed by a later block (smalltt freezes metas per top-level definition). */
trait Items:
  self: Elaborator =>
  import core.*

  def elabProgram(prog: List[Item]): Unit =
    val (declarations, objectItems) = splitItems(prog)
    elabDeclarations(declarations)
    objectItems.foreach(elabItemReporting)
    if rewrites(state.parts) then
      // module-wide directives: the rules and queries are those of the expansion
      items.filterInPlace {
        case _: CoreItem.RuleItem | _: CoreItem.QueryItem => false
        case _ => true
      }
      items ++= expandModule(state.parts.toList)
    finish()

  /** A program's declarations (declarations, definitions, clauses of functions and formula functions,
   *  subtyping edges) and its object items (rules, queries, directives), each in source order. */
  def splitItems(prog: List[Item]): (List[Item], List[Item]) =
    val declared = prog.collect { case d: Decl => d.name.name }.toSet
    val (_, rest) = prog.partition(clauseName(_, declared).isDefined)
    val formulaFunctions = formulaFunctionNames(rest)
    prog.partition {
      // dropped with the declarations, which record the names they might declare ([[elabDeclarations]])
      case item if hasSyntaxErrors(item) => true
      case r: Rule => clauseName(r, declared).isDefined || clauseOf(formulaFunctions)(r).isDefined
      // `%use` and `%export` belong to the file's scope ([[Uses]])
      case Directive(_, _: DirArgs.Use | _: DirArgs.Export) => true
      case _: Query | _: Directive => false
      case _ => true
    }

  /** Elaborates a program's declarations ([[splitItems]]). */
  def elabDeclarations(prog: List[Item]): Unit =
    val declared = prog.collect { case d: Decl => d.name.name }.toSet
    state.functionNames = prog.flatMap(clauseName(_, declared)).toSet
    state.declaredHere = prog.flatMap(declares).toSet
    state.signatures = prog.collect { case d @ Decl(n, Nil, _, None, Some(rt: RecordType)) => n.name -> rt }.toMap
    val (clauses, rest) = prog.partition(clauseName(_, declared).isDefined)
    val formulaFunctions = formulaFunctionNames(rest)
    val (formulaClauses, meta0) = rest.partition(clauseOf(formulaFunctions)(_).isDefined)
    // `%use` first (the names it opens are retried for), `%export` after all declarations ([[Uses]])
    val (exports, nonExports) = meta0.partition(isExport)
    val (uses, others) = nonExports.partition(isUse)
    val meta = uses ++ others
    // the names that items with syntax errors might declare: their uses are not reported (if no other
    // item declares them); the items are dropped silently by `elabItem`
    state.erroneous ++= prog.filter(hasSyntaxErrors).flatMap(mightDeclare)
    // a function with a clause with a syntax error is not defined, and its uses are not elaborated
    state.unelaborated = clauses.filter(hasSyntaxErrors).flatMap(clauseName(_, declared)).toSet ++
      formulaClauses.filter(hasSyntaxErrors).flatMap(clauseOf(formulaFunctions)).toSet
    val firstGlobal = globals.length
    predeclare(meta)
    elabInDependencyOrder(meta)
    dropPending()
    checkObjectDeclarations(firstGlobal)
    // the derived functions are generated code: nothing to show for their positions
    withoutTooling(defineSharedFunctions())
    if !file.signaturesOnly then
      elabClauseGroups(clauses)
      for f <- formulaFunctions if !state.unelaborated(f) do
        inBlock(elabFormulaClauses(f, formulaClauses.collect { case r: Rule if clauseOf(Set(f))(r).isDefined => r }))
      exports.foreach(elabItemReporting)
    flushTooling(success = true)

  /** Records what a dropped `%use` might have opened ([[ElabState.droppedUses]]). */
  private def droppedUse(item: Item): Unit = item match
    case Directive(_, DirArgs.Use(_, names)) =>
      val these = names.map(_.map(_.name).toSet)
      state.droppedUses = (state.droppedUses, these) match
        case (None, t) => Some(t)
        case (Some(None), _) | (_, None) => Some(None)
        case (Some(Some(a)), Some(b)) => Some(Some(a ++ b))
    case _ => ()

  private def isUse(item: Item): Boolean = item match
    case Directive(_, _: DirArgs.Use) => true
    case _ => false

  private def isExport(item: Item): Boolean = item match
    case Directive(_, _: DirArgs.Export) => true
    case _ => false

  /** The names an item with a syntax error might have been meant to declare: its name, or the name of
   *  the head of a rule (a declaration whose `:` is missing is a rule). */
  private def mightDeclare(item: Item): List[Name] =
    def head(t: hugin.syntax.Tree): Option[Name] = t match
      case ErrorTree(parts) => parts.headOption.flatMap(head)
      case other => hugin.syntax.TreeOps.headName(other).map(_.name)
    item match
      case r: Rule => r.heads.flatMap(head)
      case cl: Clause => head(cl.lhs).toList
      case other => declares(other).toList

  /** The name an item declares. */
  private def declares(item: Item): Option[Name] = declaresIdent(item).map(_.name)

  private def declaresIdent(item: Item): Option[Ident] = item match
    case d: Decl => Some(d.name)
    case d: Def => Some(d.name)
    case _ => None

  /** Elaborates items in source order, except that an item referring to a name declared by a later item
   *  is retried after it (object declarations may be written in any order); the items left form cycles of
   *  such references ([[reportCycles]]). */
  private def elabInDependencyOrder(items: List[Item]): Unit =
    var pending = items.map(i => (i, Option.empty[ElabError]))
    var progress = true
    while pending.nonEmpty && progress do
      val before = pending.length
      // how many of this round's items declare a name: a name is declared by a later item if another
      // one does (counted once per round instead of listing the others for every item)
      val declaring = pending.flatMap((i, _) => declares(i)).groupMapReduce(identity)(_ => 1)(_ + _)
      // a pending `%use` may open the name
      val uses = pending.count((i, _) => isUse(i))
      pending = pending.flatMap { (item, _) =>
        def later(n: Name) =
          declaring.getOrElse(n, 0) > (if declares(item).contains(n) then 1 else 0) || uses > (if isUse(item) then 1 else 0)
        attemptItem(item) match
          case Some(e) if e.unresolved.exists(later) => Some((item, Some(e)))
          case Some(e) =>
            if e.unresolved.isDefined && e.unresolved == declares(item) then selfReference(item, e) else report(e)
            // the names of a dropped item are erroneous: their uses are not reported again
            declares(item).foreach(state.erroneous += _)
            droppedUse(item)
            None
          case None => None
      }
      progress = pending.length < before
    reportCycles(pending.collect { case (item, Some(e)) => (item, e) })

  /** Items that refer to each other in a cycle: refinements (E0404) and type definitions (E0104, once per
   *  cycle, at the reference that closes it) as the old typer reported them; others as unresolved names. */
  private def reportCycles(stuck: List[(Item, ElabError)]): Unit =
    val byName = stuck.flatMap((item, e) => declares(item).map(_ -> (item, e))).toMap
    def target(item: Item, e: ElabError) = e.unresolved.flatMap(byName.get)
    def isTypeDefinition(item: Item) = item match
      case Decl(_, Nil, Keyword(Kw.Type), None, Some(_)) => true
      case _ => false
    for (item, e) <- stuck do
      (item, target(item, e)) match
        case (d: Decl, _) if d.sup.isDefined => reporter.report(ElabProblem.CyclicRefinement(d.name.name, d.span).toDiagnostic)
        case (d: Decl, Some((t: Decl, _))) if isTypeDefinition(d) && isTypeDefinition(t) =>
          if t.span.start < d.span.start then
            reporter.report(ElabProblem.CyclicTypeDefinition(t.name.name, e.diag.labels.head.span, t.name.span).toDiagnostic)
        case _ => report(e)

  /** E0105: the definition `item` refers to itself (`e` is the unresolved reference). */
  private def selfReference(item: Item, e: ElabError): Unit =
    val name = declaresIdent(item).get
    reporter.report(ElabProblem.SelfReference(name.name, e.diag.labels.head.span, name.span).toDiagnostic)

  /** Elaborates an item; on an error, undoes its effects on metas and returns the error. */
  private def attemptItem(item: Item): Option[ElabError] = inBlock {
    val start = metas.length
    try
      itemTransaction {
        undoOnFailure {
          elabItem(item)
          solvedAndRecorded(start)
        }
      }
      None
    catch case e: ElabError => Some(e)
  }

  /** Called after all items: checks across items. W0003: a meta definition or formula function of the
   *  program that nothing refers to (module values and signatures are exempt: a module emits its rules
   *  even when unreferenced). */
  def finish(): Unit =
    if file.lintUnused then recordTopLevel()
    if file.lintUnused then
      for (n, id) <- scope if !state.used(id) && isDefinitionToLint(id) do
        reporter.report(ElabProblem.UnusedDefinition(n, globals(id).span).toDiagnostic)

  private def isDefinitionToLint(id: Int): Boolean =
    val g = globals(id)
    val definition = g.stage == Stage.S1 && (g.kind match
      case GlobalKind.Definition(_, _) => true
      case _ => false
    )
    // module values, signatures and type definitions are exempt
    definition && (force(g.ty) match
      case Val.RecTy(_, _, _, _, _) | Val.U1(_) => false
      case _ => force(telescope(g.ty)._2) != Val.Lift(Val.U0)
    )

  /** The function an item is a clause of: `f p̄ = e.`, or `f X̄ = e.` after a declaration `f : A.`. */
  private def clauseName(item: Item, declared: Set[Name]): Option[Name] = item match
    case Clause(lhs, _, _) => hugin.syntax.TreeOps.headName(lhs).map(_.name)
    case d: Def if declared(d.name.name) => Some(d.name.name)
    case _ => None

  /** Elaborates the clauses of each function, grouped by name in order of appearance. */
  private def elabClauseGroups(items: List[Item]): Unit =
    val groups = scala.collection.mutable.LinkedHashMap.empty[Name, List[Item]]
    for item <- items; n <- clauseName(item, state.functionNames) do groups(n) = groups.getOrElse(n, Nil) :+ item
    for (n, group) <- groups if !state.unelaborated(n) do
      inBlock {
        val start = metas.length
        try
          undoOnFailure {
            // the records of a failed group are shown before its metas are undone
            try
              val id = declaredFunction(n, group.head)
              elabFunction(id, group.flatMap(surfaceClause))
              checkSolved(start)
            catch
              case e: ElabError =>
                flushTooling(success = false)
                throw e
            flushTooling(success = true)
          }
        catch
          case e: ElabError =>
            report(e)
            // dropped for an error that follows from a syntax error: its uses are not elaborated either
            if e.silent then state.unelaborated += n
      }

  private def declaredFunction(n: Name, first: Item): Int =
    scope.get(n) match
      case Some(id) if globals(id).kind.isInstanceOf[GlobalKind.Function] => id
      case Some(id) =>
        fail(ClauseProblem.NotDefinableByClauses(n, first.span, globals(id).span, describeKind(id)))
      case None if state.erroneous(n) => syntaxError(first.span) // its declaration had a syntax error
      case None =>
        fail(ClauseProblem.ClausesWithoutDeclaration(n, first.span))

  private def describeKind(id: Int): String = globals(id).kind match
    case _ if globals(id).stage == Stage.S0 => "an object constant"
    case GlobalKind.Inductive(_) => "an inductive family"
    case GlobalKind.Constructor(_) => "a constructor"
    case GlobalKind.Definition(_, _) => "a definition"
    case _ => "a constant"

  /** Elaborates an item; module bodies it evaluates are instances of this item's site, named after the
   *  definition ([[Modules]]). */
  def elabItem(item: Item): Unit =
    // an item with a syntax error (reported by the parser) is not elaborated: it is dropped silently and
    // the names it declares are erroneous (`docs/PARSER.md`, §5)
    if hasSyntaxErrors(item) then syntaxError(item.span)
    // the records of a failed item are shown before its metas are undone ([[solvedAndRecorded]])
    try at(item.span, declares(item).getOrElse(""))(elabItemAt(item))
    catch
      case e: ElabError =>
        flushTooling(success = false)
        throw e
    // a shared declaration declares a constant at each stage under the name
    declares(item).flatMap(scope.get).foreach(id =>
      (id :: globals(id).shared.map(_.counterpart).toList).foreach(recordDeclaration(_, item))
    )

  private def elabItemAt(item: Item): Unit = item match
    case d: Decl => elabDecl(d)
    case d: Def => elabDef(d.name, d.params, d.rhs, d.span)
    case r: Rule => elabRule(r)
    case q: Query => elabQuery(q)
    case d @ Directive(_, DirArgs.Use(m, ns)) => elabUse(d, m, ns)
    case d @ Directive(_, DirArgs.Export(s)) => elabExport(d, s)
    case d: Directive => items ++= directiveItems(Cxt.empty, d, inBody = false)
    case e: SubEdge => elabEdge(e)
    case cl: Clause => fail(ElabProblem.MalformedClause(cl.lhs.span))

  def elabItemReporting(item: Item): Unit = inBlock {
    val start = metas.length
    try
      itemTransaction {
        elabItem(item)
        solvedAndRecorded(start)
      }
    catch case e: ElabError => report(e)
  }

  /** Runs `f`; if it fails, the items and names it added are removed (an item with an error is dropped). */
  private def itemTransaction[A](f: => A): A =
    val count = items.length
    val partCount = state.parts.length
    val names = scope.begin()
    val result =
      try f
      catch
        case e: ElabError =>
          items.dropRightInPlace(items.length - count)
          state.parts.dropRightInPlace(state.parts.length - partCount)
          scope.rollback(names)
          throw e
        case e: Throwable =>
          scope.commit(names)
          throw e
    scope.commit(names)
    result

  /** [[checkSolved]], then the item's tooling records are flushed ([[MetaTooling]]): once it is known
   *  whether the item succeeded, and before its metas are undone if it did not. */
  private def solvedAndRecorded(start: Int): Unit =
    try checkSolved(start)
    catch
      case e: ElabError =>
        flushTooling(success = false)
        throw e
    flushTooling(success = true)

  /** Every meta created since `start` must be solved (except the types of object variables, which the
   *  object typing infers). */
  def checkSolved(start: Int): Unit =
    (start until metas.length).find(m => metas(m).solution.isEmpty && !metas(m).allowUnsolved).foreach { m =>
      val e = metas(m)
      if e.what.startsWith("type argument") then fail(ElabProblem.UndeterminedTypeArgument(e.what, e.span))
      fail(TypeProblem.CannotInfer(e.what, e.span))
    }
