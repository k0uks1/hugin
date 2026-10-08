package hugin.core
package handover

import hugin.obj
import hugin.obj.{DirKind, ModeSpec, ObjProgram}
import hugin.util.*

/** The handover of an elaborated program to the object level (REDESIGN §10, B3). The object items are
 *  staged — normalised, which runs the meta code they splice ([[Staging]]) — and translated to an
 *  [[ObjProgram]], which the object-level phases (object typing, moding, transformations, checks,
 *  lowering) then process. An item whose staged code is not object code is reported and left out. */
final class Handover(core: Core, reporter: Reporter, index: hugin.compiler.SemanticIndex = hugin.compiler.SemanticIndex()):
  import core.*

  private val staging = Staging(core, reporter)
  private val symbols = ObjectSymbols(core, reporter, index)
  private val declData = DeclData(core, symbols, reporter)

  def program(items: List[CoreItem]): ObjProgram =
    val ordered = items.sortBy(staging.position)
    symbols.declare(objectConstants)
    val (genericRules, rules) = ordered.collect { case r: CoreItem.RuleItem => r }.partition(_.generic)
    val (genericDirs, dirs) = ordered.collect { case d: CoreItem.DirectiveItem => d }.partition(isGeneric)
    val own = ordered.filter {
      case r: CoreItem.RuleItem => !r.generic
      case d: CoreItem.DirectiveItem => !isGeneric(d)
      case _ => true
    }.flatMap(item => stage(item, Nil, "", Origin.Source).map(staging.position(item) -> _))
    // module instances' items are placed at the item that created the instance (staging may create more)
    val all = (own ++ moduleItems()).sortBy(_._1).map(_._2)
    // the generic rules come last: they are staged at the instances everything else uses
    val instantiated = Generics(core, symbols, reporter, this).rules(genericRules)
    recordInstances()
    ObjProgram(
      symbols.allTypes,
      symbols.allRelations,
      all.collect { case e: obj.Edge => e }.toVector,
      (all.collect { case r: obj.Rule => r } ++ instantiated).toVector,
      all.collect { case q: obj.Query => q }.toVector,
      (all.collect { case d: obj.Directive => d } ++ genericDirs.flatMap(instanceDirectives) ++ declData.familyDirectives()).toVector
    )

  /** The instances of families, for tooling (hover over a family's declaration). */
  private def recordInstances(): Unit =
    for id <- globals.indices; (fam, _) <- globals(id).instanceOf do index.instance(globals(fam).span, globals(id).name)

  /** The requirements of signatures met by the relations passed to functors (checked by the object level,
   *  E0208); a `%fact` field must be passed a fact constructor (E0204). */
  def requirements: List[obj.RequirementCheck] = requirementUses.toList.flatMap { u =>
    symbols.relSym(u.rel).flatMap { rel =>
      u.req match
        case SigReq.Complete(l, sp) => Some(obj.RequirementCheck(obj.Requirement.Complete(l, sp), rel, u.use, u.origin))
        case SigReq.HasMode(l, ins, sp) => Some(obj.RequirementCheck(obj.Requirement.HasMode(l, obj.Mode(ins), sp), rel, u.use, u.origin))
        case SigReq.Fact(l) =>
          if rel.isData then reporter.report(elab.ElabProblem.NotAFactConstructor(rel.name, l, u.use).toDiagnostic)
          None
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
    case d: CoreItem.DirectiveItem => directive(d, base, origin).toList
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

  /** `%mode` about a family (`%mode len +l -n.`) applies to each of its instances. */
  private def isGeneric(d: CoreItem.DirectiveItem): Boolean = d.target.exists(t => familyOf(t).isDefined)

  private def familyOf(t: Tm): Option[Int] = Tm.unloc(t) match
    case Tm.Global(id) if globals(id).kind.isInstanceOf[GlobalKind.Family] => Some(id)
    case _ => None

  private def instanceDirectives(d: CoreItem.DirectiveItem): List[obj.Directive] =
    val fam = familyOf(d.target.get).get
    symbols.instancesOf(fam).flatMap(inst => directive(d.copy(target = Some(Tm.Global(inst)))))

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
    def show(v: Val) = showTm(names, quote(lvl, v))
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
      obj.Rule(r.name.map(qualify(prefix, _)), heads, body)(r.span, Origin(r.origin.frames ++ origin.frames))
    }

  private def query(q: CoreItem.QueryItem, base: List[Val] = Nil, origin: Origin = Origin.Source): Option[obj.Query] =
    staged(q.vars, List(q.body), q.span, base)((terms, normal) =>
      obj.Query(terms.formulas(normal.head))(q.span, Origin(q.origin.frames ++ origin.frames))
    )

  private def edge(e: CoreItem.EdgeItem, base: List[Val] = Nil, origin: Origin = Origin.Source): Option[obj.Edge] =
    Tm.unloc(nf(base, e.sup)) match
      case Tm.Global(id) =>
        symbols.typeSym(id).map(sup => obj.Edge(symbols.otype(nf(base, e.sub), e.span), sup)(e.span, origin))
      case _ => None

  /** `%mode` (until C3). */
  private def directive(d: CoreItem.DirectiveItem, base: List[Val] = Nil, origin: Origin = Origin.Source): Option[obj.Directive] =
    d.directive match
      case CoreDirective.Mode(inputs) =>
        val target = d.target.flatMap(t => staged(Nil, List(t), d.span, base)((terms, normal) => terms.term(normal.head)))
        target.collect { case obj.Term.App(r, Nil) => obj.Directive(DirKind.ModeD(ModeSpec(inputs)), Some(r), None)(d.span, origin) }
      case CoreDirective.FormulaMode(f, inputs) =>
        FormulaModes(core, symbols, reporter).check(f, inputs, d.span)
        None
