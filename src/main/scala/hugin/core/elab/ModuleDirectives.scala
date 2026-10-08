package hugin.core
package elab

import hugin.syntax.Trees.*
import hugin.util.*
import scala.collection.mutable

/** What an object item of a file contributes to the module that module-wide directives rewrite
 *  (reference: directives). The terms are closed. */
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

/** Module-wide directives (`module -> module`, reference: directives) rewrite the rules and queries of the file.
 *  The elaboration of each object item records what it contributes ([[ModulePart]]); if a module-wide
 *  directive is among them, [[expandModule]] replaces the rules and queries elaborated item by item with
 *  the expansion: the rules, queries and splices of the whole file are the module's data (in source
 *  order); then, in source order, an additive directive adds its items at its place and a module-wide
 *  directive replaces the module with its result. So a module-wide directive sees every rule, query and
 *  splice of the file (also later ones) and the items of earlier additive and module-wide directives;
 *  only the items of later additive directives are not seen. The result is reflected and
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

  /** A rule or query as written, as data of type `item` (at the item's position). Its meta subterms
   *  (a meta constant used as object code) are evaluated and their values reified (issue #79). */
  def reifyItem(item: Item): Tm = Tm.loc(item.span, reifyAt(item))

  private def reifyAt(item: Item): Tm = item match
    case _: Rule | _: Query => reifyingFile(reify(Cxt.empty, Quote(List(item), true)(item.span), RKind.Item))
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
      val quoted = module.map(e => quote(0, e.value))
      val before = quoted.map(stripPositions).zip(module).toMap
      val data = listData(kindType(RKind.Item), quoted.map(Left(_)))
      val result = eval(Nil, Tm.App(fn, data, Icit.Expl))
      // an item the directive passed on unchanged keeps its place and provenance; a new one is placed at
      // the directive, or, if it was built by a directive of another file (the prelude), at the first position
      // in this file of the data it was built from (a rule generated from a source rule is placed at that
      // rule), and notes its expansion
      listValues(result, span).map { v =>
        before.get(stripPositions(quote(0, v))) match
          case Some(e) => e.copy(value = v)
          case None => Entry(v, Origin(List(frame)), (if foreign(fn, span) then placeOf(v, span) else None).getOrElse(span))
      }
    catch
      case e: ElabError =>
        report(e)
        module

  private def placeOf(v: Val, at: Span): Option[Span] = force(v) match
    case Val.Obj(ObjForm.Loc(s), _) if s.exists && (!at.exists || s.source.path == at.source.path) => Some(s)
    case Val.Obj(ObjForm.Loc(_), List(x)) => placeOf(x, at)
    case Val.Rigid(_, sp) => sp.reverse.iterator.collect { case Elim.EApp(a, Icit.Expl) => a }.flatMap(placeOf(_, at)).nextOption()
    case _ => None

  /** Whether the directive `fn` is defined in another file than `at` (the prelude's `demand`). */
  private def foreign(fn: Tm, at: Span): Boolean =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case other => other
    head(fn) match
      case Tm.Global(id) => at.exists && globals(id).declSpan.exists && globals(id).declSpan.source.path != at.source.path
      case _ => false

  private def elabEntry(e: Entry): List[CoreItem] =
    try reflectedItems(e.value, RKind.Item, e.span).map(elabGenerated(_, e.origin))
    catch
      case err: ElabError =>
        report(err)
        Nil
