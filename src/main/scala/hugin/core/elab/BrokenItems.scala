package hugin.core
package elab

import hugin.syntax.Trees.*
import hugin.syntax.TreeOps.{hasSyntaxErrors, headName}
import hugin.util.Span

/** Stand-ins for the rules and queries with syntax errors among a program's declarations (issue #126,
 *  PR 1). [[Items.splitItems]] files an item with a syntax error with the declarations, so that the names
 *  it might declare are not reported as unresolved; [[Items.elabDeclarations]] drops it silently and
 *  reads of it only:
 *
 *  - the names it might declare ([[Items.mightDeclare]], for `state.erroneous` and the dependency graph
 *    of [[ElabOrder]]): for a rule, the head name of each head, looking into the first part of an
 *    erroneous head;
 *  - for a rule with a single unnamed head, the formula function it may be a clause of (`clauseOf`, for
 *    `state.unelaborated`): the head name of its head;
 *  - the names it mentions ([[ElabOrder.mentions]]) that are dependencies of its node: those declared by
 *    an item of the file, the derived functions (`T.lift`, `T.reify`), and any name if the file has a
 *    `%use` (it may open it); another name is a dependency of nothing (`ElabOrder.plan`'s `target`);
 *  - its position (the order of the nodes);
 *  - that it has a syntax error, and its place in the list (each dropped item is one block).
 *
 *  A stand-in has exactly these and nothing else: the head names, the mentioned names in a sorted
 *  erroneous tree, and the item's span (for its position; the query layer compares it by its start,
 *  `hugin.query.DeclarationsOf`). So typing inside a rule, while it does not parse, leaves the program's
 *  declarations as they were and does not elaborate them and every object item again. A declaration, a
 *  definition, a clause of a function or a directive with a syntax error is kept as it is: the
 *  declarations read more of it (its name, its clause group, the names a `%use` might open). */
object BrokenItems:
  private val none = Span.NoSpan

  /** Whether `item` is replaced by a stand-in. */
  def summarised(item: Item): Boolean = item match
    case _: Rule | _: Query => hasSyntaxErrors(item)
    case _ => false

  /** The declarations of a program ([[Items.splitItems]]) with each rule and query with a syntax error
   *  replaced by its stand-in. */
  def standIns(decls: List[Item]): List[Item] =
    lazy val names = decls.flatMap(names0).toSet
    lazy val uses = decls.exists {
      case Directive(_, _: DirArgs.Use) => true
      case _ => false
    }
    def dependency(n: String) = uses || names(n) || n.endsWith(".lift") || n.endsWith(".reify")
    def mentioned(item: Item) = ErrorTree(ElabOrder.mentions(item).filter(dependency).toList.sorted.map(n => Ident(n)(none)))(none)
    decls.map {
      case item @ Rule(name, heads, _) if summarised(item) =>
        Rule(name.map(n => Ident(n.name)(none)), heads.map(head), Some(mentioned(item)))(item.span)
      case q: Query if summarised(q) => Query(mentioned(q))(q.span)
      case other => other
    }

  /** The names an item of the declarations may declare or define (more than [[Items.mightDeclare]]:
   *  also the heads of clauses and rules that parse); a mention of another name has no node to depend on
   *  unless a `%use` may open it. */
  private def names0(item: Item): List[String] = item match
    case d: Decl => List(d.name.name)
    case d: Def => List(d.name.name)
    case Clause(lhs, _, _) => declared(lhs).toList
    case Rule(name, heads, _) => name.map(_.name).toList ++ heads.flatMap(declared)
    case _ => Nil

  /** A head with the same head name (for `clauseOf`) and the same name for [[Items.mightDeclare]]. */
  private def head(t: hugin.syntax.Tree): hugin.syntax.Tree = t match
    case ErrorTree(parts) => ErrorTree(parts.headOption.flatMap(declared).map(n => Ident(n)(none)).toList)(none)
    case other => headName(other).fold[hugin.syntax.Tree](ErrorTree(Nil)(none))(n => Ident(n.name)(none))

  /** The name [[Items.mightDeclare]] finds in a head. */
  private def declared(t: hugin.syntax.Tree): Option[String] = t match
    case ErrorTree(parts) => parts.headOption.flatMap(declared)
    case other => headName(other).map(_.name)
