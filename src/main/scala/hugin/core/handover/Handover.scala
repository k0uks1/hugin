package hugin.core
package handover

import hugin.obj
import hugin.obj.ObjProgram
import hugin.util.*

/** The handover of an elaborated program to the object level (redesign step B3). The object items are
 *  staged — normalised, which runs the meta code they splice ([[Staging]]) — and translated to an
 *  [[ObjProgram]], which the object-level phases (object typing, moding, transformations, checks,
 *  lowering) then process. An item whose staged code is not object code is reported and left out. */
final class Handover(core: Core, reporter: Reporter, index: hugin.compiler.SemanticIndex = hugin.compiler.SemanticIndex()):
  import core.*

  private val staging = Staging(core, reporter)
  private val symbols = ObjectSymbols(core, reporter, index)
  private val declData = DeclData(core, symbols, reporter)
  private val typing = StagedTyping(core, symbols, reporter, index)

  /** The types of the variables of the staged rules and queries (for the object level's transformations). */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, obj.OType]] = java.util.IdentityHashMap()

  /** The object typing of the staged items, run once every item (and every edge) is staged. */
  private val typingChecks = scala.collection.mutable.ListBuffer.empty[() => Option[AnyRef]]

  def program(items: List[CoreItem]): ObjProgram =
    val ordered = items.sortBy(staging.position)
    symbols.declare(objectConstants)
    val (genericRules, rules) = ordered.collect { case r: CoreItem.RuleItem => r }.partition(_.generic)
    val own = ordered.filter {
      case r: CoreItem.RuleItem => !r.generic
      case _ => true
    }.flatMap(item => stage(item, Nil, "", Origin.Source).map(staging.position(item) -> _))
    // module instances' items are placed at the item that created the instance (staging may create more)
    val all = (own ++ moduleItems()).sortBy(_._1).map(_._2)
    // the generic rules come last: they are staged at the instances everything else uses
    val instantiated = Generics(core, symbols, reporter, this).rules(genericRules)
    recordInstances()
    val typed = java.util.Collections.newSetFromMap(java.util.IdentityHashMap[AnyRef, java.lang.Boolean]())
    typingChecks.foreach(check => check().foreach(typed.add))
    ObjProgram(
      symbols.allTypes,
      symbols.allRelations,
      all.collect { case e: obj.Edge => e }.toVector,
      (all.collect { case r: obj.Rule => r } ++ instantiated).filter(typed.contains).toVector,
      all.collect { case q: obj.Query => q }.filter(typed.contains).toVector,
      (all.collect { case d: obj.Directive => d } ++ declData.familyDirectives()).toVector
    )

  /** The instances of families, for tooling (hover over a family's declaration). */
  private def recordInstances(): Unit =
    for id <- globals.indices; (fam, _) <- globals(id).instanceOf do index.instance(globals(fam).span, globals(id).name)

  /** The requirements of signatures met by the relations passed to functors (checked by the object level,
   *  E0208). */
  def requirements: List[obj.RequirementCheck] = requirementUses.toList.flatMap { u =>
    symbols.relSym(u.rel).map { rel =>
      u.req match
        case SigReq.Complete(l, sp) => obj.RequirementCheck(obj.Requirement.Complete(l, sp), rel, u.use, u.origin)
    }
  }

  /** The object constants that are not instances of families, in the order of their declarations (module
   *  instances' constants at the item that created the instance). */
  private def objectConstants: List[Int] =
    globals.indices.toList
      .filter(id => globals(id).kind.isInstanceOf[GlobalKind.Object] && globals(id).instanceOf.isEmpty && !globals(id).pending)
      .sortBy(id => positionOf(if globals(id).placedAt.exists then globals(id).placedAt else globals(id).declSpan))

  private type Staged = obj.Rule | obj.Query | obj.Edge | obj.Directive

  /** An item staged in the environment `base` (of a module instance, or empty), rule names qualified with
   *  `prefix`. */
  private def stage(item: CoreItem, base: List[Val], prefix: String, origin: Origin): List[Staged] = item match
    case r: CoreItem.RuleItem => rule(r, base, prefix, origin).toList
    case q: CoreItem.QueryItem => query(q, base, origin).toList
    case e: CoreItem.EdgeItem => edge(e, base, origin).toList
    case d: CoreItem.DeclItem => declData.directives(d, base, prefix, origin)
    case _: CoreItem.GlobalItem => Nil

  /** The items of all module instances with their positions (staging may create further instances). */
  private def moduleItems(): List[(Int, Staged)] =
    val out = scala.collection.mutable.ListBuffer.empty[(Int, Staged)]
    var k = 0
    while k < moduleInstances.length do
      val i = moduleInstances(k)
      out ++= i.body.items.flatMap(stage(_, i.env, i.prefix, i.origin)).map(positionOf(i.placedAt) -> _)
      k += 1
    out.toList

  /** Stages object code over the variables `vars` and translates it with `f`; `None` (reported) if it is
   *  not object code. */
  def staged[A](vars: List[(Name, Tm)], parts: List[Tm], span: Span, base: List[Val] = Nil)(
      f: (ObjectTerms, List[Tm]) => A
  ): Option[A] =
    val env = vars.indices.reverse.map(Val.local).toList ++ base
    val names = vars.map(_._1).reverse
    // the base environment is closed: only the variables of the item are bound
    val normal = observing(names, vars.length)(at(span, "")(parts.map(p => quote(vars.length, eval(env, p)))))
    if !normal.forall(staging.objectCode(names, _, span)) then None
    else
      try Some(f(ObjectTerms(core, symbols, names, span), normal))
      catch
        case e: NotObjectCode =>
          reporter.report(e.diagnostic)
          None

  /** Records in the semantic index how code crossed the stages while `f` stages an item's code over the
   *  variables `names` (at level `lvl`). */
  private def observing[A](names: List[Name], lvl: Int)(f: => A): A =
    import hugin.compiler.SemanticIndex.Stage
    // bounded: a persisted value may be stuck code with an exponential tree (issue #108)
    def show(v: Val) = showTmBounded(names, quote(lvl, v))
    val saved = observer
    observer = new StagingObserver:
      def quoted(span: Span, code: Val): Unit = index.staged(span, Stage.Quoted, show(code))
      def spliced(span: Span, code: Val): Unit = index.staged(span, Stage.Spliced, show(code))
      def persisted(span: Span, value: Val): Unit = index.staged(span, Stage.Persisted, show(value))
    try f
    finally observer = saved

  private def qualify(prefix: String, name: String): String = if prefix.isEmpty then name else s"$prefix.$name"

  def rule(r: CoreItem.RuleItem, base: List[Val] = Nil, prefix: String = "", origin: Origin = Origin.Source): Option[obj.Rule] =
    staged(r.vars, r.heads ++ r.body.toList, r.span, base) { (terms, normal) =>
      val heads = normal.take(r.heads.length).map(terms.term(_))
      val body = normal.drop(r.heads.length).flatMap(terms.formulas(_))
      val rule = obj.Rule(r.name.map(qualify(prefix, _)), heads, body)(r.span, Origin(r.origin.frames ++ origin.frames))
      val meta = base.nonEmpty || r.generic || involvesMeta(r.heads ++ r.body.toList)
      typed(
        rule,
        r.vars,
        normal.take(r.heads.length),
        normal.drop(r.heads.length),
        rule.origin,
        rule.span,
        heads,
        body,
        meta || rule.origin.frames.nonEmpty
      )
      rule
    }

  private def query(q: CoreItem.QueryItem, base: List[Val] = Nil, origin: Origin = Origin.Source): Option[obj.Query] =
    staged(q.vars, List(q.body), q.span, base) { (terms, normal) =>
      val query = obj.Query(terms.formulas(normal.head))(q.span, Origin(q.origin.frames ++ origin.frames))
      val meta = base.nonEmpty || involvesMeta(List(q.body)) || query.origin.frames.nonEmpty
      typed(query, q.vars, Nil, normal, query.origin, query.span, Nil, query.body, meta)
      query
    }

  /** Whether elaborated object code splices meta code (or binds variables of a formula function). */
  private def involvesMeta(ts: List[Tm]): Boolean = ts.exists(t =>
    Tm.exists(t) {
      case Tm.Splice(_) | Tm.Persist(_) | Tm.Fresh(_, _) => true
      case _ => false
    }
  )

  /** Schedules the object typing of a staged item ([[StagedTyping]]); its problems are reported if it
   *  involves meta code. */
  private def typed(
      item: AnyRef,
      vars: List[(Name, Tm)],
      heads: List[Tm],
      body: List[Tm],
      origin: Origin,
      span: Span,
      oheads: List[obj.Term],
      obody: List[obj.Formula],
      report: Boolean
  ): Unit =
    val names = vars.map(_._1).reverse
    typingChecks += (() =>
      typing.check(names, heads, body, origin, report, (span, if item.isInstanceOf[obj.Query] then "query" else "rule")).map { g =>
        varTypes.put(item, g)
        typing.recordVariables(span, oheads, obody, g)
        item
      }
    )

  private def edge(e: CoreItem.EdgeItem, base: List[Val] = Nil, origin: Origin = Origin.Source): Option[obj.Edge] =
    Tm.unloc(nf(base, e.sup)) match
      case Tm.Global(id) =>
        if base.nonEmpty then typing.addEdge(eval(base, e.sub), id)
        symbols.typeSym(id).map(sup => obj.Edge(symbols.otype(nf(base, e.sub), e.span), sup)(e.span, origin))
      case _ => None
