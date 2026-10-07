package hugin.core
package elab

import hugin.syntax.Trees.*
import hugin.util.*

/** The items of a program: elaborated one by one, each with error recovery (an item with an error is
 *  reported and dropped). Meta items come first, then object items (rules, queries, directives), which
 *  may refer to everything declared in the module. */
trait Items:
  self: Elaborator =>
  import core.*

  def elabProgram(prog: List[Item]): Unit =
    val (meta, obj) = prog.partition {
      case _: Rule | _: Query | _: Directive => false
      case _ => true
    }
    elabInDependencyOrder(meta)
    obj.foreach(elabItemReporting)
    finish()

  /** The name an item declares. */
  private def declares(item: Item): Option[Name] = item match
    case d: Decl => Some(d.name.name)
    case d: Def => Some(d.name.name)
    case _ => None

  /** Elaborates items in source order, except that an item referring to a name declared by a later item
   *  is retried after it (object declarations may be written in any order); a cycle of such references is
   *  reported as unresolved names. */
  private def elabInDependencyOrder(items: List[Item]): Unit =
    var pending = items
    var progress = true
    while pending.nonEmpty && progress do
      val before = pending.length
      pending = pending.filter { item =>
        val later = pending.filter(_ ne item).flatMap(declares).toSet
        attemptItem(item).exists(e => e.unresolved.exists(later) || { reporter.report(e.diag); false })
      }
      progress = pending.length < before
    pending.foreach(elabItemReporting)

  /** Elaborates an item; on an error, undoes its effects on metas and returns the error. */
  private def attemptItem(item: Item): Option[ElabError] =
    val start = metas.length
    try
      undoOnFailure {
        elabItem(item)
        checkSolved(start)
      }
      None
    catch case e: ElabError => Some(e)

  /** Called after all items (for checks across items). */
  def finish(): Unit = ()

  def elabItem(item: Item): Unit = item match
    case d: Decl => elabDecl(d)
    case d: Def => elabDef(d.name, d.params, d.rhs, d.span)
    case r: Rule => elabRule(r)
    case q: Query => elabQuery(q)
    case d: Directive => elabDirective(d)
    case e: SubEdge => unsupportedAt(e.span, "subtyping edges")
    case cl: Clause => elabClause(cl)

  def elabClause(cl: Clause): Unit = unsupportedAt(cl.span, "equational clauses")

  def elabItemReporting(item: Item): Unit =
    val start = metas.length
    try
      elabItem(item)
      checkSolved(start)
    catch case e: ElabError => reporter.report(e.diag)

  /** Every meta created since `start` must be solved (except the types of object variables, which the
   *  object typer infers). */
  def checkSolved(start: Int): Unit =
    (start until metas.length).find(m => metas(m).solution.isEmpty && !metas(m).allowUnsolved).foreach { m =>
      val e = metas(m)
      fail(
        Diagnostic.error("E0903", s"cannot infer ${e.what}", e.span, "cannot infer this")
          .withNote("the elaborator found no constraint that determines it; add a type annotation")
      )
    }
