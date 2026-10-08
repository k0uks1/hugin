package hugin.core
package elab

import hugin.syntax.Literal
import hugin.syntax.Trees.*
import hugin.util.*
import scala.collection.mutable

/** What an object item of a file contributes to the module that module-wide directives rewrite
 *  (REDESIGN §7.1). The terms are closed. */
enum ModulePart:
  /** A rule or query as written: its data is reified from its syntax. */
  case Source(item: Item)

  /** Reflected items: of a splice `$e.`, or of an additive directive (`directive`). */
  case Data(data: Tm, kind: RKind, frame: TraceFrame, directive: Boolean)

  /** A module-wide directive: a function `module -> module`. */
  case Rewrite(fn: Tm, frame: TraceFrame, span: Span)

object ModulePart:
  def map(p: ModulePart, f: Tm => Tm): ModulePart = p match
    case d: Data => d.copy(data = f(d.data))
    case r: Rewrite => r.copy(fn = f(r.fn))
    case s: Source => s

/** Module-wide directives (`module -> module`, REDESIGN §7.1) rewrite the rules and queries of the file.
 *  The elaboration of each object item records what it contributes ([[ModulePart]]); if a module-wide
 *  directive is among them, [[expandModule]] replaces the rules and queries elaborated item by item with
 *  the expansion: in source order, the rules, queries and splices are the module's data, an additive
 *  directive adds its items at its place, and a module-wide directive replaces all the data so far with
 *  its result (so each directive sees the output of those before it). The result is reflected and
 *  elaborated like hand-written code, with the directive's frame as provenance. Items with errors are not
 *  part of the module (they were reported). Local directives keep their items. */
trait ModuleDirectives:
  self: Elaborator =>
  import core.*

  def recordPart(p: ModulePart): Unit = state.parts += p

  /** Whether the parts contain a module-wide directive. */
  def rewrites(parts: Iterable[ModulePart]): Boolean = parts.exists(_.isInstanceOf[ModulePart.Rewrite])

  /** The rules and queries of the module described by `parts`, expanded and elaborated (errors reported). */
  def expandModule(parts: List[ModulePart]): List[CoreItem] =
    // the module, in order: data with its provenance, or the index of a directive not yet expanded
    val module = mutable.ListBuffer.empty[Either[Int, Entry]]
    parts.zipWithIndex.foreach {
      case (ModulePart.Source(item), _) => sourceData(item).foreach(e => module += Right(e))
      case (ModulePart.Data(tm, k, frame, false), _) => entries(tm, k, Origin(List(frame)), frame.span).foreach(e => module += Right(e))
      case (_, i) => module += Left(i)
    }
    for (part, i) <- parts.zipWithIndex do
      val at = module.indexOf(Left(i))
      part match
        case ModulePart.Data(tm, k, frame, true) =>
          module.remove(at)
          module.insertAll(at, entries(tm, k, Origin(List(frame)), frame.span).map(Right(_)))
        case ModulePart.Rewrite(fn, frame, span) =>
          module.remove(at)
          val first = module.indexWhere(_.isRight)
          val result = rewrite(fn, module.toList.collect { case Right(e) => e }, frame, span)
          val pending = module.filter(_.isLeft)
          val before = module.take(if first < 0 then at else first).count(_.isLeft)
          module.clear()
          module ++= pending.take(before) ++ result.map(Right(_)) ++ pending.drop(before)
        case _ =>
    module.toList.collect { case Right(e) => e }.flatMap(elabEntry)

  /** One item of the module as data: a value of type `item`, where it came from, and the span of the
   *  source item or directive (where data without positions is placed). */
  private final case class Entry(value: Val, origin: Origin, span: Span)

  private def sourceData(item: Item): Option[Entry] =
    val saved = index.muted
    index.muted = true
    try Some(Entry(eval(Nil, reifyItem(item)), Origin.Source, item.span))
    catch
      case e: ElabError =>
        report(e)
        None
    finally index.muted = saved

  /** A rule or query as written, as data of type `item`. */
  def reifyItem(item: Item): Tm = item match
    case Rule(name, heads, body) =>
      val rule = reify(Cxt.empty, RuleQuote(heads, body)(item.span), RKind.Rule)
      name match
        case Some(n) => con("inamed", Tm.Lit(Literal.StrL(n.name), Stage.S1), rule)
        case None => con("irule", rule)
    case Query(body) =>
      con("iquery", listData(kindType(RKind.Formula), conjuncts(body).map(f => Left(reify(Cxt.empty, f, RKind.Formula)))))
    case other => throw Impossible(s"not a rule or query: $other")

  /** The items of data `tm` of kind `k`, one entry each. */
  private def entries(tm: Tm, k: RKind, origin: Origin, span: Span): List[Entry] =
    def items(v: Val, k: RKind): List[Val] = k match
      case RKind.List(e) => listValues(v, span).flatMap(items(_, e))
      case RKind.Rule => List(eval(Nil, con("irule", quote(0, v))))
      case _ => List(v)
    items(eval(Nil, tm), k).map(Entry(_, origin, span))

  private def rewrite(fn: Tm, module: List[Entry], frame: TraceFrame, span: Span): List[Entry] =
    try
      val data = listData(kindType(RKind.Item), module.map(e => Left(quote(0, e.value))))
      val result = eval(Nil, Tm.App(fn, data, Icit.Expl))
      listValues(result, span).map(Entry(_, Origin(List(frame)), span))
    catch
      case e: ElabError =>
        report(e)
        module

  private def elabEntry(e: Entry): List[CoreItem] =
    try reflectedItems(e.value, RKind.Item, e.span).map(elabGenerated(_, e.origin))
    catch
      case err: ElabError =>
        report(err)
        Nil
