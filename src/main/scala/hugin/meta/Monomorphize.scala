package hugin.meta

import hugin.util.*
import hugin.compiler.*
import hugin.obj.*
import hugin.syntax.AggKind
import scala.collection.mutable

/** Family instantiation by worklist (Section 4.6). Type arguments of family uses are inferred by
 *  first-order matching against the expected object types; rule families are instantiated at every
 *  instance of their head relation. */
final class Monomorphizer(p: ObjProgram)(using Context):
  private val MaxInstances = 10000
  private val relMemo = mutable.LinkedHashMap.empty[(RelSym, List[OType]), RelSym]
  private val typeMemo = mutable.LinkedHashMap.empty[(TypeSym, List[OType]), TypeSym]
  val instancesOf: mutable.HashMap[RelSym, mutable.ListBuffer[RelSym]] = mutable.HashMap.empty
  private val worklist = mutable.Queue.empty[(RelSym, List[OType], Origin)]
  private val outRules = mutable.ArrayBuffer.empty[Rule]
  private val outQueries = mutable.ArrayBuffer.empty[Query]
  private val outTypes = mutable.ArrayBuffer.empty[TypeSym]
  private val outRels = mutable.ArrayBuffer.empty[RelSym]

  private val ruleFamilies: Map[RelSym, Vector[Rule]] =
    p.rules.filter(r => headFamily(r).isDefined).groupBy(r => headFamily(r).get)

  private def headFamily(r: Rule): Option[RelSym] =
    r.heads.collectFirst { case Term.App(RelRef.Sym(s), _) if s.tparams.nonEmpty => s }

  // components of the generic dependency graph (for the polymorphic recursion check)
  private val component: Map[RelSym, Int] =
    val nodes = p.rels.toList
    val edges = mutable.HashMap.empty[RelSym, mutable.Set[RelSym]]
    def relsIn(f: Formula): List[RelSym] = f match
      case Formula.Atom(r, args, _) => r.sym :: args.flatMap(relsInT)
      case Formula.Not(a) => relsIn(a)
      case Formula.Agg(_, _, t, b) => relsInT(t) ++ b.flatMap(relsIn)
      case Formula.Disj(alts) => alts.flatten.flatMap(relsIn)
      case Formula.Cmp(_, l, r) => relsInT(l) ++ relsInT(r)
      case _ => Nil
    def relsInT(t: Term): List[RelSym] = t match
      case Term.App(r, as) => r.sym :: as.flatMap(relsInT)
      case Term.As(x, _) => relsInT(x)
      case Term.Ascr(x, _) => relsInT(x)
      case Term.Arith(_, l, r) => relsInT(l) ++ relsInT(r)
      case _ => Nil
    for r <- p.rules; h <- r.heads do
      h match
        case Term.App(RelRef.Sym(hs), _) => edges.getOrElseUpdate(hs, mutable.Set.empty) ++= r.body.flatMap(relsIn)
        case _ =>
    Graphs.components(nodes, (n: RelSym) => edges.getOrElse(n, Nil).toList).zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap

  // ------------------------------------------------------------------ instances

  private def instName(base: String, args: List[OType]): String =
    s"$base[${args.map(showInst).mkString(", ")}]"

  private def showInst(t: OType): String = t match
    case OType.Con(s, Nil) => s.name
    case OType.Fact(r, Nil) => r.name
    case other => other.show

  /** Converts a ground generic type into its monomorphic form (family applications become instances). */
  def monoType(t: OType, span: Span, origin: Origin): OType = t match
    case OType.Con(s, args) if s.tparams.nonEmpty =>
      if args.length != s.tparams.length || !args.forall(OType.isGround) then OType.Err
      else OType.Con(typeInstance(s, args.map(monoType(_, span, origin)), span, origin), Nil)
    case OType.Fact(r, args) if r.tparams.nonEmpty =>
      if args.length != r.tparams.length || !args.forall(OType.isGround) then OType.Err
      else OType.Fact(relInstance(r, args.map(monoType(_, span, origin)), span, origin), Nil)
    case OType.Union(ms) => OType.union(ms.map(monoType(_, span, origin)))
    case OType.Param(_) | OType.Meta(_) => OType.Err
    case other => other

  def typeInstance(s: TypeSym, args: List[OType], span: Span, origin: Origin): TypeSym =
    typeMemo.get((s, args)) match
      case Some(i) => i
      case None =>
        val i = TypeSym(instName(s.name, args), TypeKind.Open, s.span, s.origin)
        i.instanceOf = Some((s, args))
        typeMemo((s, args)) = i
        ctx.unit.index.instance(s.span, i.name)
        val sub = s.tparams.zip(args).toMap
        i.kind = s.kind match
          case TypeKind.Refinement(b) => TypeKind.Refinement(monoType(OType.subst(b, sub), span, origin))
          case k => k
        outTypes += i
        // constructors of an open family are instantiated with it
        if s.isOpen then
          for c <- p.rels if c.tparams.nonEmpty do
            c.result match
              case Some(OType.Con(`s`, ps))
                  if ps.forall(_.isInstanceOf[OType.Param]) &&
                    ps.map { case OType.Param(x) => x; case _ => null }.toSet == c.tparams.toSet && ps.distinct.length == ps.length =>
                val m = ps.map { case OType.Param(x) => x; case _ => null }.zip(args).toMap
                relInstance(c, c.tparams.map(m), span, origin)
              case _ =>
        i

  def relInstance(r: RelSym, args: List[OType], span: Span, origin: Origin): RelSym =
    relMemo.get((r, args)) match
      case Some(i) => i
      case None =>
        val i = RelSym(instName(r.name, args), r.kind, r.span, r.origin)
        i.instanceOf = Some((r, args))
        relMemo((r, args)) = i
        ctx.unit.index.instance(r.span, i.name)
        instancesOf.getOrElseUpdate(r, mutable.ListBuffer.empty) += i
        val sub = r.tparams.zip(args).toMap
        i.cols = r.cols.map(c => c.copy(tpe = monoType(OType.subst(c.tpe, sub), span, origin)))
        i.result = r.result.map(t => monoType(OType.subst(t, sub), span, origin))
        outRels += i
        worklist.enqueue((r, args, origin))
        i

  // ------------------------------------------------------------------ inference

  private final class Inference(origin: Origin):
    private val sol = mutable.HashMap.empty[Int, OType]
    private var next = 0
    val varTypes = mutable.HashMap.empty[String, OType]

    /** Family occurrences: node identity → (relation, metas). */
    val occs = new java.util.IdentityHashMap[AnyRef, (RelSym, List[OType], Span)]()

    def fresh(): OType = { next += 1; OType.Meta(next) }

    def resolve(t: OType): OType = t match
      case OType.Meta(id) => sol.get(id).map(resolve).getOrElse(t)
      case OType.Con(s, as) => OType.Con(s, as.map(resolve))
      case OType.Fact(r, as) => OType.Fact(r, as.map(resolve))
      case OType.Union(ms) => OType.union(ms.map(resolve))
      case other => other

    private def occurs(id: Int, t: OType): Boolean = OType.exists(resolve(t)) { case OType.Meta(x) => x == id; case _ => false }

    def unify(a0: OType, b0: OType, span: Span): Unit =
      val a = resolve(a0)
      val b = resolve(b0)
      (a, b) match
        case (OType.Meta(x), OType.Meta(y)) if x == y =>
        case (OType.Meta(x), t) => if !occurs(x, t) then sol(x) = t
        case (t, OType.Meta(y)) => if !occurs(y, t) then sol(y) = t
        case (OType.Con(s1, as), OType.Con(s2, bs)) if s1 == s2 && as.length == bs.length =>
          as.zip(bs).foreach((x, y) => unify(x, y, span))
        case (OType.Fact(r1, as), OType.Fact(r2, bs)) if r1 == r2 && as.length == bs.length =>
          as.zip(bs).foreach((x, y) => unify(x, y, span))
        case _ =>

    /** Records that a value of type `sub` occurs where `sup` is expected. Only family arguments are solved.
     *  A constructor fact that determines a type argument stands for the constructor's declared result type:
     *  family arguments are invariant, so `cons here nil` is a `list place`, not a `list here`. */
    def constrain(sub0: OType, sup0: OType, span: Span): Unit =
      val sub = resolve(sub0)
      val sup = resolve(sup0)
      (sub, sup) match
        case (OType.Fact(c, as), OType.Meta(_)) if c.kind == RelKind.Ctor && c.result.isDefined =>
          unify(OType.subst(c.result.get, c.tparams.zip(as).toMap), sup, span)
        case (OType.Meta(_), _) | (_, OType.Meta(_)) => unify(sub, sup, span)
        case (OType.Con(s1, as), OType.Con(s2, bs)) if s1 == s2 =>
          as.zip(bs).foreach((x, y) => unify(x, y, span))
          if as.nonEmpty && as.map(resolve) != bs.map(resolve) && as.forall(x => OType.isGround(resolve(x))) && bs.forall(x =>
              OType.isGround(resolve(x))
            )
          then
            report(Diagnostic.error("E0402", "type mismatch", span, s"`${resolve(sub).show}` is not `${resolve(sup).show}`")
              .withNote("type arguments of families are invariant"))
        case (OType.Fact(r1, as), OType.Fact(r2, bs)) if r1 == r2 => as.zip(bs).foreach((x, y) => unify(x, y, span))
        case (OType.Fact(c, as), OType.Con(t, bs)) if c.tparams.nonEmpty || t.tparams.nonEmpty =>
          c.result match
            case Some(OType.Con(`t`, ps)) =>
              val sub2 = c.tparams.zip(as).toMap
              ps.zip(bs).foreach((x, y) => unify(OType.subst(x, sub2), y, span))
            case _ =>
        case _ =>

    def report(d: Diagnostic): Unit = ctx.report(d.withOrigin(origin))

    def varType(n: String): OType = varTypes.getOrElseUpdate(n, fresh())

    private def instantiate(r: RelSym, node: AnyRef, span: Span, pre: Option[List[OType]] = None): (List[Column], OType) =
      if r.tparams.isEmpty then (r.cols.toList, OType.Fact(r, Nil))
      else
        val metas = pre.getOrElse(r.tparams.map(_ => fresh()))
        occs.put(node, (r, metas, span))
        val sub = r.tparams.zip(metas).toMap
        (r.cols.toList.map(c => c.copy(tpe = OType.subst(c.tpe, sub))), OType.Fact(r, metas))

    def term(t: Term): OType = t match
      case Term.Var(n) => varType(n)
      case Term.Lit(l) => OType.Base(BaseType.of(l))
      case a @ Term.App(RelRef.Sym(r), args) =>
        val (cols, ft) = instantiate(r, a, a.span)
        args.zip(cols).foreach((x, c) => constrain(term(x), c.tpe, x.span))
        ft
      case Term.As(x, v) =>
        val tx = term(x)
        unify(varType(v), tx, t.span)
        tx
      case Term.Ascr(x, tp) =>
        val tx = term(x)
        constrain(tx, tp, t.span)
        tp
      case Term.Proj(v, _) => term(v); fresh()
      case Term.With(v, fs) => fs.foreach(f => term(f._2)); term(v)
      case Term.Arith(_, l, r) =>
        val tl = term(l)
        val tr = term(r)
        unify(tl, tr, t.span)
        tl
      case Term.Neg(x) => term(x)
      case _ => fresh()

    def head(h: Term, pre: Option[List[OType]]): Unit = h match
      case a @ Term.App(RelRef.Sym(r), args) =>
        val (cols, _) = instantiate(r, a, a.span, pre)
        args.zip(cols).foreach((x, c) => constrain(term(x), c.tpe, x.span))
      case other => term(other)

    def formula(f: Formula): Unit = f match
      case a @ Formula.Atom(RelRef.Sym(r), args, as) =>
        val (cols, ft) = instantiate(r, a, a.span)
        args.zip(cols).foreach((x, c) => constrain(term(x), c.tpe, x.span))
        as.foreach(v => unify(varType(v), ft, a.span))
      case Formula.Cmp(_, l, r) =>
        val tl = term(l)
        val tr = term(r)
        unify(tl, tr, f.span)
      case Formula.Not(a) => formula(a)
      case Formula.Agg(res, k, t, b) =>
        b.foreach(formula)
        val tt = term(t)
        unify(varType(res), if k == AggKind.Count then OType.Int else tt, f.span)
      case Formula.Disj(alts) => alts.flatten.foreach(formula)
      case _ =>

  // ------------------------------------------------------------------ rewriting

  private def rewriteRule(r: Rule, inf: Inference, family: Option[(RelSym, List[OType])]): Option[Rule] =
    var ok = true
    def inst(node: AnyRef, r0: RelSym): RelSym =
      val e = inf.occs.get(node)
      if e == null then r0
      else
        val (rel, metas, span) = e
        val args = metas.map(inf.resolve)
        if !args.forall(OType.isGround) then
          val first = ok
          ok = false
          val missing = rel.tparams.zip(args).filterNot((_, a) => OType.isGround(a)).map(_._1.name)
          if first then
            inf.report(Diagnostic.error(
              "E0206",
              s"cannot infer type argument${if missing.length > 1 then "s" else ""} ${missing.map(m => s"`$m`").mkString(", ")} of family `${rel.name}`",
              span,
              "type not determined"
            )
              .withHelp(s"add a type ascription, e.g. `(${rel.name} ... : T)`"))
          rel
        else
          val margs = args.map(monoType(_, span, r.origin))
          // polymorphic recursion (Definition 4.2)
          val recursive = family.exists { (f, ts) =>
            if component.get(rel) == component.get(f) && margs != ts then
              ok = false
              polyRec(rel, f, margs, ts, span, r.origin)
              true
            else false
          }
          if recursive then rel
          else if relMemo.size > MaxInstances then
            if ok then
              inf.report(Diagnostic.error(
                "E0205",
                s"too many family instances (more than $MaxInstances)",
                span,
                s"while instantiating `${rel.name}`"
              ).withNote("family instantiation does not terminate"))
            ok = false
            rel
          else
            val i = relInstance(rel, margs, span, r.origin)
            ctx.unit.index.instance(rel.span, i.name, span)
            i
    def t(x: Term): Term = x match
      case a @ Term.App(RelRef.Sym(s), args) => Term.App(RelRef.Sym(inst(a, s)), args.map(t))(a.span)
      case a @ Term.As(y, v) => Term.As(t(y), v)(a.span)
      case a @ Term.Ascr(y, tp) => Term.Ascr(t(y), monoType(inf.resolve(tp), a.span, r.origin))(a.span)
      case p @ Term.Proj(v, l) => Term.Proj(t(v), l)(p.span)
      case w @ Term.With(v, fs) => Term.With(t(v), fs.map((l, y, s) => (l, t(y), s)))(w.span)
      case a @ Term.Arith(op, l, rr) => Term.Arith(op, t(l), t(rr))(a.span)
      case n @ Term.Neg(y) => Term.Neg(t(y))(n.span)
      case other => other
    def f(x: Formula): Formula = x match
      case a @ Formula.Atom(RelRef.Sym(s), args, as) => Formula.Atom(RelRef.Sym(inst(a, s)), args.map(t), as)(a.span)
      case c @ Formula.Cmp(op, l, rr) => Formula.Cmp(op, t(l), t(rr))(c.span)
      case n @ Formula.Not(a) => Formula.Not(f(a).asInstanceOf[Formula.Atom])(n.span)
      case g @ Formula.Agg(res, k, tt, b) => Formula.Agg(res, k, t(tt), b.map(f))(g.span)
      case d @ Formula.Disj(alts) => Formula.Disj(alts.map(_.map(f)))(d.span)
      case other => other
    val out = r.withParts(heads = r.heads.map(t), body = r.body.map(f))
    if ok then Some(out) else None

  private def polyRec(g: RelSym, f: RelSym, us: List[OType], ts: List[OType], span: Span, origin: Origin): Unit =
    ctx.report(Diagnostic.error(
      "E0205",
      "polymorphic recursion",
      span,
      s"`${g.name}` used at [${us.map(showInst).mkString(", ")}] while instantiating `${f.name}` at [${ts.map(showInst).mkString(", ")}]"
    )
      .withNote(
        "within a recursive component every relation must be used at exactly the type parameters of the rule family (Definition 4.2)"
      )
      .withOrigin(origin))

  private def inferRule(r: Rule, family: Option[(RelSym, List[OType])]): Option[Rule] =
    val inf = Inference(r.origin)
    r.heads.zipWithIndex.foreach { (h, i) =>
      val pre = family.flatMap { (f, ts) =>
        h match
          case Term.App(RelRef.Sym(`f`), _) if i == r.heads.indexWhere { case Term.App(RelRef.Sym(`f`), _) => true; case _ => false } =>
            Some(ts)
          case _ => None
      }
      inf.head(h, pre)
    }
    r.body.foreach(inf.formula)
    rewriteRule(r, inf, family)

  def run(): ObjProgram =
    // monomorphic declarations
    for t <- p.types if t.tparams.isEmpty do
      t.kind match
        case TypeKind.Refinement(b) => t.kind = TypeKind.Refinement(monoType(b, t.span, t.origin))
        case _ =>
      outTypes += t
    for r <- p.rels if r.tparams.isEmpty do
      outRels += r
    val monoRels = outRels.toList
    // monomorphic rules and queries
    for r <- p.rules if headFamily(r).isEmpty do inferRule(r, None).foreach(outRules += _)
    for q <- p.queries do
      val inf = Inference(q.origin)
      q.body.foreach(inf.formula)
      rewriteRule(Rule(None, Nil, q.body)(q.span, q.origin, q.expansions), inf, None).foreach(r => outQueries += q.withBody(r.body))
    // declared column types of monomorphic relations (after rules, so that instances are requested in source order)
    for r <- monoRels do
      r.cols = r.cols.map(c => c.copy(tpe = monoType(c.tpe, r.span, r.origin)))
      r.result = r.result.map(monoType(_, r.span, r.origin))
    val edges = p.edges.map(e => Edge(monoType(e.sub, e.span, e.origin), e.sup)(e.span, e.origin))
    // worklist
    while worklist.nonEmpty do
      val (f, ts, origin) = worklist.dequeue()
      for rule <- ruleFamilies.getOrElse(f, Vector.empty) do
        inferRule(rule, Some((f, ts))).foreach { r =>
          outRules += r.withParts(name = r.name.map(n => s"$n[${ts.map(showInst).mkString(", ")}]"))
        }
    // directives on families apply to all instances
    val dirs = p.directives.flatMap { d =>
      d.target match
        case Some(RelRef.Sym(r)) if r.tparams.nonEmpty =>
          instancesOf.getOrElse(r, Nil).toVector.map(i => Directive(d.kind, Some(RelRef.Sym(i)), d.rule)(d.span, d.origin))
        case _ => Vector(d)
    }
    ObjProgram(outTypes.toVector, outRels.toVector, edges, outRules.toVector, outQueries.toVector, dirs)

/** Phase: instantiate families. */
final class MonomorphizePhase extends Phase:
  def phaseName = "monomorphize"
  def description = "instantiate families at concrete types (Section 4.6)"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.generic == null then return
    u.prog = Monomorphizer(u.generic.nn).run()
  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)
