package hugin.core
package elab

import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** The items of a program: elaborated one by one, each with error recovery (an item with an error is
 *  reported and dropped), in three phases: declarations and definitions; the clauses of functions (which
 *  may refer to every declaration, also recursively); object items (rules, queries, directives). Finally
 *  the termination of the functions is checked. */
trait Items:
  self: Elaborator =>
  import core.*

  def elabProgram(prog: List[Item]): Unit =
    val declared = prog.collect { case d: Decl => d.name.name }.toSet
    state.functionNames = prog.flatMap(clauseName(_, declared)).toSet
    state.signatures = prog.collect { case d @ Decl(n, Nil, _, None, Some(rt: RecordType), _, _) => n.name -> rt }.toMap
    val (clauses, rest) = prog.partition(clauseName(_, declared).isDefined)
    val formulaFunctions = formulaFunctionNames(rest)
    val (formulaClauses, rest1) = rest.partition(clauseOf(formulaFunctions)(_).isDefined)
    val (obj, meta) = rest1.partition {
      case _: Rule | _: Query | _: Directive => true
      case _ => false
    }
    predeclare(meta)
    elabInDependencyOrder(meta)
    dropPending()
    elabClauseGroups(clauses)
    for f <- formulaFunctions do
      elabFormulaClauses(f, formulaClauses.collect { case r: Rule if clauseOf(Set(f))(r).isDefined => r })
    obj.foreach(elabItemReporting)
    finish()

  /** The name an item declares. */
  private def declares(item: Item): Option[Name] = item match
    case d: Decl => Some(d.name.name)
    case d: Def => Some(d.name.name)
    case _ => None

  /** Elaborates items in source order, except that an item referring to a name declared by a later item
   *  is retried after it (object declarations may be written in any order); the items left form cycles of
   *  such references ([[reportCycles]]). */
  private def elabInDependencyOrder(items: List[Item]): Unit =
    var pending = items.map(i => (i, Option.empty[ElabError]))
    var progress = true
    while pending.nonEmpty && progress do
      val before = pending.length
      pending = pending.flatMap { (item, _) =>
        val later = pending.map(_._1).filter(_ ne item).flatMap(declares).toSet
        attemptItem(item) match
          case Some(e) if e.unresolved.exists(later) => Some((item, Some(e)))
          case Some(e) =>
            report(e)
            // a name defined by an item dropped silently (an erroneous import) is erroneous too
            if e.silent then declares(item).foreach(state.erroneous += _)
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
      case Decl(_, Nil, Keyword(Kw.Type), None, Some(_), _, _) => true
      case _ => false
    for (item, e) <- stuck do
      (item, target(item, e)) match
        case (d: Decl, _) if d.sup.isDefined => reporter.report(ElabProblem.CyclicRefinement(d.name.name, d.span).toDiagnostic)
        case (d: Decl, Some((t: Decl, _))) if isTypeDefinition(d) && isTypeDefinition(t) =>
          if t.span.start < d.span.start then
            reporter.report(ElabProblem.CyclicTypeDefinition(t.name.name, e.diag.labels.head.span, t.name.span).toDiagnostic)
        case _ => report(e)

  /** Elaborates an item; on an error, undoes its effects on metas and returns the error. */
  private def attemptItem(item: Item): Option[ElabError] =
    val start = metas.length
    try
      itemTransaction {
        undoOnFailure {
          elabItem(item)
          checkSolved(start)
        }
      }
      None
    catch case e: ElabError => Some(e)

  /** Called after all items: checks across items. W0003: a meta definition or formula function of the
   *  program that nothing refers to (module values and signatures are exempt: a module emits its rules
   *  even when unreferenced). */
  def finish(): Unit =
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
      case Val.RecTy(_, _, _, _) | Val.U1(_) => false
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
    for (n, group) <- groups do
      val start = metas.length
      try
        undoOnFailure {
          val id = declaredFunction(n, group.head)
          elabFunction(id, group.flatMap(surfaceClause))
          checkSolved(start)
        }
      catch case e: ElabError => report(e)

  private def declaredFunction(n: Name, first: Item): Int =
    scope.get(n) match
      case Some(id) if globals(id).kind.isInstanceOf[GlobalKind.Function] => id
      case Some(id) =>
        fail(
          Legacy.error(DiagCode.E0914, s"`$n` cannot be defined by clauses", first.span, "clause")
            .withLabel(globals(id).span, s"`$n` is declared here as ${describeKind(id)}")
            .withNote("clauses define meta functions; object relations are defined by rules (`:-`)")
        )
      case None =>
        fail(
          Legacy.error(DiagCode.E0915, s"clauses of `$n` without a declaration", first.span, "clause")
            .withHelp(s"declare its type first: `$n : A -> B.`")
        )

  private def describeKind(id: Int): String = globals(id).kind match
    case _ if globals(id).stage == Stage.S0 => "an object constant"
    case GlobalKind.Inductive(_) => "an inductive family"
    case GlobalKind.Constructor(_) => "a constructor"
    case GlobalKind.Definition(_, _) => "a definition"
    case _ => "a constant"

  /** Elaborates an item; module bodies it evaluates are instances of this item's site, named after the
   *  definition ([[Modules]]). */
  def elabItem(item: Item): Unit = at(item.span, declares(item).getOrElse(""))(elabItemAt(item))

  private def elabItemAt(item: Item): Unit = item match
    case d: Decl => elabDecl(d)
    case d: Def => elabDef(d.name, d.params, d.rhs, d.span)
    case r: Rule => elabRule(r)
    case q: Query => elabQuery(q)
    case d: Directive => elabDirective(d)
    case e: SubEdge => elabEdge(e)
    case cl: Clause => throw Impossible(s"clause outside of its group: ${cl.span}")

  def elabItemReporting(item: Item): Unit =
    val start = metas.length
    try
      itemTransaction {
        elabItem(item)
        checkSolved(start)
      }
    catch case e: ElabError => report(e)

  /** Runs `f`; if it fails, the items and names it added are removed (an item with an error is dropped). */
  private def itemTransaction[A](f: => A): A =
    val count = items.length
    val names = scope.keySet.toSet
    try f
    catch
      case e: ElabError =>
        items.dropRightInPlace(items.length - count)
        scope.filterInPlace((n, _) => names(n))
        throw e

  /** Every meta created since `start` must be solved (except the types of object variables, which the
   *  object typer infers). */
  def checkSolved(start: Int): Unit =
    (start until metas.length).find(m => metas(m).solution.isEmpty && !metas(m).allowUnsolved).foreach { m =>
      val e = metas(m)
      fail(
        Legacy.error(DiagCode.E0903, s"cannot infer ${e.what}", e.span, "cannot infer this")
          .withNote("the elaborator found no constraint that determines it; add a type annotation")
      )
    }
