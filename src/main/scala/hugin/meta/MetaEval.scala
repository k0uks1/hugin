package hugin.meta

import hugin.util.*
import hugin.syntax.Literal
import hugin.compiler.*
import hugin.compiler.SemanticIndex.Stage
import hugin.obj.*
import hugin.obj.typing.Moding
import scala.collection.mutable

/** Meta values V (Section 4.5). */
enum Value:
  case VLit(l: Literal)
  case VType(t: OType)
  case VRel(r: RelSym)
  case VTerm(t: Term)
  case VFormula(body: List[Formula])
  case VRec(fields: List[(String, Value)])
  case VClosure(env: Map[Sym, Value], param: Sym, body: MExpr)
  case VSig(t: MType)
  case VErr

  def describe: String = this match
    case VLit(l) => s"the literal ${l.show}"
    case VType(t) => s"the type `${t.show}`"
    case VRel(r) => s"the relation `${r.name}`"
    case VTerm(t) => s"the code `${ObjPrinter.term(t)}`"
    case VFormula(b) => s"the formula `${ObjPrinter.body(b)}`"
    case VRec(_) => "a record"
    case VClosure(_, _, _) => "a function"
    case VSig(_) => "a signature"
    case VErr => "an erroneous value"

/** Evaluation frame: hygiene tag of the current formula-function application, naming hint for module
 *  bodies, and the meta-level call chain (for diagnostics on generated code). */
final case class Frame(hyg: Option[Int], hint: String, origin: Origin, fnName: Option[String])

/** Evaluator for the meta level (rule M-Eval-Body and Section 4.5); emits the object program. */
final class MetaEval(using Context):
  import Value.*

  val types: mutable.ArrayBuffer[TypeSym] = mutable.ArrayBuffer.empty
  val rels: mutable.ArrayBuffer[RelSym] = mutable.ArrayBuffer.empty
  val edges: mutable.ArrayBuffer[Edge] = mutable.ArrayBuffer.empty
  val rules: mutable.ArrayBuffer[Rule] = mutable.ArrayBuffer.empty
  val queries: mutable.ArrayBuffer[Query] = mutable.ArrayBuffer.empty
  val directives: mutable.ArrayBuffer[Directive] = mutable.ArrayBuffer.empty
  val requirements: mutable.ArrayBuffer[RequirementCheck] = mutable.ArrayBuffer.empty

  private val usedPrefixes = mutable.HashSet.empty[String]
  private var hygCounter = 0
  private var anon = 0

  private def err(code: String, msg: String, span: Span, fr: Frame, label: String = ""): Unit =
    ctx.report(Diagnostic.error(code, msg, span, label).withOrigin(fr.origin))

  /** Records for tooling how object code crossed between the levels (see [[SemanticIndex.Stage]]). */
  private def staged(span: Span, stage: Stage, value: String): Unit = ctx.unit.index.staged(span, stage, value)

  private def freshPrefix(hint: String): String =
    val base = if hint.isEmpty then { anon += 1; s"_m$anon" }
    else hint
    if usedPrefixes.add(base) then base
    else
      var k = 2
      while !usedPrefixes.add(s"$base#$k") do k += 1
      s"$base#$k"

  def eval(m: MExpr, env: Map[Sym, Value], fr: Frame): Value = m match
    case MExpr.Ref(s) =>
      env.get(s) match
        case Some(v) => v
        case None =>
          // unreachable for well-typed programs; errors were reported by the typer
          VErr
    case MExpr.Lit(l) => VLit(l)
    case MExpr.Op(op, l, r, span) =>
      (eval(l, env, fr), eval(r, env, fr)) match
        case (VLit(a), VLit(b)) =>
          Prims.arith(op, a, b) match
            case Some(x) => VLit(x)
            case None =>
              ctx.report(Diagnostic.error(
                "E0209",
                "compile-time arithmetic failure",
                span,
                s"`${a.show} ${op.show} ${b.show}` is undefined"
              )
                .withNote(if op == ArithOp.Div then "division by zero" else "64-bit integer overflow")
                .withNote("at the meta level an undefined primitive operation is a compile-time error (Section 3.3)")
                .withOrigin(fr.origin))
              VErr
        case _ => VErr
    case MExpr.Neg(x, span) =>
      eval(x, env, fr) match
        case VLit(a) =>
          Prims.neg(a) match
            case Some(v) => VLit(v)
            case None =>
              err("E0209", "compile-time arithmetic failure", span, fr, "negation overflows")
              VErr
        case _ => VErr
    case MExpr.Proj(x, l) =>
      eval(x, env, fr) match
        case VRec(fs) => fs.find(_._1 == l).map(_._2).getOrElse(VErr)
        case _ => VErr
    case MExpr.Rec(fs) => VRec(fs.map((l, e) => (l, eval(e, env, fr.copy(hint = qualify(fr.hint, l))))))
    case MExpr.Lam(p, b) => VClosure(env, p, b)
    case MExpr.App(f, a, span) =>
      val fv = eval(f, env, fr)
      val av = eval(a, env, fr)
      apply(fv, av, fnName(f), span, fr)
    case MExpr.QuoteTerm(t) =>
      val code = reifyTerm(t, env, fr, renamer(fr))
      staged(t.span, Stage.Quoted, ObjPrinter.term(code))
      VTerm(code)
    case MExpr.QuoteFormula(b) =>
      val code = reifyBody(b, env, fr, renamer(fr))
      if b.nonEmpty then staged(b.head.span.to(b.last.span), Stage.Quoted, ObjPrinter.body(code))
      VFormula(code)
    case MExpr.QuoteType(t) => VType(reifyType(t, env, fr))
    case MExpr.FactTypeOf(x) =>
      eval(x, env, fr) match
        case VRel(r) => VType(OType.Fact(r, Nil))
        case VType(t) => VType(t)
        case _ => VErr
    case MExpr.TApp(f, as) =>
      val args = as.map(reifyType(_, env, fr))
      eval(f, env, fr) match
        case VType(OType.Con(s, Nil)) => VType(OType.Con(s, args))
        case VRel(r) => VType(OType.Fact(r, args)) // only used under FactTypeOf
        case _ => VErr
    case MExpr.Body(items, scope, span) => evalBody(items, scope, env, fr, span)
    case MExpr.SigV(t) => VSig(t)
    case MExpr.Err => VErr

  def apply(fv: Value, av: Value, name: Option[String], span: Span, fr: Frame): Value = fv match
    case VClosure(cenv, p, body) =>
      checkRequirements(p, av, span, fr)
      hygCounter += 1
      val inner = Frame(
        hyg = Some(hygCounter),
        hint = fr.hint,
        origin = fr.origin.push(TraceFrame(s"in application of `${name.getOrElse("<function>")}`", span)),
        fnName = name
      )
      eval(body, cenv + (p -> av), inner)
    case _ => VErr

  /** `%mode f m̄` (Section 4.8): the body is checked once, applied to fresh variables, to be well-moded
   *  from the input variables. */
  private def checkFnModes(s: Sym, v: Value, fr: Frame): Unit =
    var t = s.mtype
    var f = v
    val params = scala.collection.mutable.ListBuffer.empty[String]
    while t.isInstanceOf[MType.Pi] do
      val MType.Pi(x, _, cod, imp) = t: @unchecked
      val arg =
        if imp then VType(OType.Err)
        else
          val n = s"Arg${params.length + 1}"
          params += n
          VTerm(Term.Var(n)(s.span))
      f = apply(f, arg, Some(s.name), s.span, fr)
      t = cod
    f match
      case VFormula(body) =>
        for (mode, span) <- s.fnModes do
          if mode.length != params.length then
            ctx.report(Diagnostic.error(
              "E0701",
              s"mode for `${s.name}` has ${mode.length} items but the function takes ${params.length} arguments",
              span
            ))
          else
            val inputs = params.zip(mode).collect { case (p, true) => p }.toSet
            Moding.canonical(body, inputs) match
              case Left(stuck) =>
                ctx.report(Moding.describe(stuck)
                  .withLabel(span, "mode declared here")
                  .withNote(
                    s"the body of formula function `${s.name}` is not well-moded for mode ${mode.map(b => if b then "+" else "-").mkString}"
                  )
                  .withOrigin(fr.origin))
              case Right((_, b)) =>
                val outs = params.zip(mode).collect { case (p, false) => p }.filterNot(b)
                if outs.nonEmpty then
                  ctx.report(Diagnostic.error(
                    "E0501",
                    s"formula function `${s.name}` does not bind its output argument${if outs.length > 1 then "s" else ""}",
                    span,
                    s"mode ${mode.map(b => if b then "+" else "-").mkString}"
                  )
                    .withNote(
                      s"argument${if outs.length > 1 then "s" else ""} ${outs.map(o => o.drop(3)).mkString(", ")} must be bound by the body"
                    )
                    .withOrigin(fr.origin))
      case _ =>

  private def fnName(f: MExpr): Option[String] = f match
    case MExpr.Ref(s) => Some(s.name)
    case MExpr.App(g, _, _) => fnName(g)
    case MExpr.Proj(x, l) => fnName(x).map(_ + "." + l).orElse(Some(l))
    case _ => None

  private def qualify(prefix: String, name: String): String = if prefix.isEmpty then name else s"$prefix.$name"

  /** Requirements of a signature (Section 4.4) are recorded for the relations of the argument; they are
   *  checked by the `directives` phase (see [[RequirementCheck]]). */
  private def checkRequirements(p: Sym, av: Value, span: Span, fr: Frame): Unit =
    p.mtype match
      case MType.Sig(_, reqs) if reqs.nonEmpty =>
        av match
          case VRec(fs) =>
            for r <- reqs do
              val req = r match
                case Req.Complete(l, s) => Requirement.Complete(l, s)
                case Req.HasMode(l, m, s) => Requirement.HasMode(l, m, s)
              fs.find(_._1 == req.label).map(_._2) match
                case Some(VRel(rel)) => requirements += RequirementCheck(req, rel, span, fr.origin)
                case _ =>
          case _ =>
      case _ =>

  private def renamer(fr: Frame): String => String = fr.hyg match
    case Some(k) => n => s"$n#$k"
    case None => identity

  // ------------------------------------------------------------------ reification (↓ and reify_ρ)

  def reifyType(t: OType, env: Map[Sym, Value], fr: Frame): OType = OType.mapDeep(t) {
    case OType.Splice(m) =>
      eval(m, env, fr) match
        case VType(x) => x
        case VRel(r) => OType.Fact(r, Nil)
        case VErr => OType.Err
        case other =>
          err("E0202", s"splice of a non-type value", Span.NoSpan, fr, other.describe)
          OType.Err
  }

  private def reifyRel(r: RelRef, env: Map[Sym, Value], fr: Frame, span: Span): Option[RelSym] = r match
    case RelRef.Sym(s) => Some(s)
    case RelRef.Spliced(m) =>
      eval(m, env, fr) match
        case VRel(s) => Some(s)
        case VErr => None
        case other =>
          err("E0202", "splice of a non-relation value in relation position", span, fr, other.describe)
          None

  final class Abort extends Exception(null, null, false, false)

  def reifyTerm(t: Term, env: Map[Sym, Value], fr: Frame, rn: String => String): Term = t match
    case v @ Term.Var(n) => Term.Var(rn(n))(v.span)
    case l: Term.Lit => l
    case a @ Term.App(r, args) =>
      reifyRel(r, env, fr, a.span) match
        case Some(s) => Term.App(RelRef.Sym(s), args.map(reifyTerm(_, env, fr, rn)))(a.span)
        case None => throw Abort()
    case a @ Term.As(x, v) => Term.As(reifyTerm(x, env, fr, rn), rn(v))(a.span)
    case a @ Term.Ascr(x, tp) => Term.Ascr(reifyTerm(x, env, fr, rn), reifyType(tp, env, fr))(a.span)
    case p @ Term.Proj(v, l) => Term.Proj(reifyTerm(v, env, fr, rn), l)(p.span)
    case w @ Term.With(v, fs) => Term.With(reifyTerm(v, env, fr, rn), fs.map((l, x, sp) => (l, reifyTerm(x, env, fr, rn), sp)))(w.span)
    case a @ Term.Arith(op, l, r) => Term.Arith(op, reifyTerm(l, env, fr, rn), reifyTerm(r, env, fr, rn))(a.span)
    case n @ Term.Neg(x) => Term.Neg(reifyTerm(x, env, fr, rn))(n.span)
    case s @ Term.Splice(m) =>
      eval(m, env, fr) match
        case VTerm(x) =>
          staged(s.span, Stage.Spliced, ObjPrinter.term(x))
          x
        case VLit(l) =>
          staged(s.span, Stage.Persisted, l.show)
          Term.Lit(l)(s.span) // cross-stage persistence (rule Persist)
        case VErr => throw Abort()
        case other =>
          err("E0202", "splice of a value that is not code", s.span, fr, s"evaluates to ${other.describe}")
          throw Abort()

  def reifyFormula(f: Formula, env: Map[Sym, Value], fr: Frame, rn: String => String): List[Formula] = f match
    case a @ Formula.Atom(r, args, as) =>
      reifyRel(r, env, fr, a.span) match
        case Some(s) => List(Formula.Atom(RelRef.Sym(s), args.map(reifyTerm(_, env, fr, rn)), as.map(rn))(a.span))
        case None => throw Abort()
    case c @ Formula.Cmp(op, l, r) => List(Formula.Cmp(op, reifyTerm(l, env, fr, rn), reifyTerm(r, env, fr, rn))(c.span))
    case n @ Formula.Not(a) =>
      reifyFormula(a, env, fr, rn) match
        case List(x: Formula.Atom) => List(Formula.Not(x)(n.span))
        case _ => throw Abort()
    case g @ Formula.Agg(res, k, t, b) => List(Formula.Agg(rn(res), k, reifyTerm(t, env, fr, rn), reifyBody(b, env, fr, rn))(g.span))
    case d @ Formula.Disj(alts) => List(Formula.Disj(alts.map(reifyBody(_, env, fr, rn)))(d.span))
    case s @ Formula.Splice(m) =>
      eval(m, env, fr) match
        case VFormula(b) =>
          staged(s.span, Stage.Spliced, ObjPrinter.body(b))
          b
        case VErr => throw Abort()
        case other =>
          err("E0202", "splice of a value that is not a formula", s.span, fr, s"evaluates to ${other.describe}")
          throw Abort()

  def reifyBody(b: List[Formula], env: Map[Sym, Value], fr: Frame, rn: String => String): List[Formula] =
    b.flatMap(reifyFormula(_, env, fr, rn))

  // ------------------------------------------------------------------ module bodies

  def evalBody(items: List[EItem], scope: Scope, env0: Map[Sym, Value], fr0: Frame, span: Span): Value =
    val env = bodyEnv(items, scope, env0, fr0)
    VRec(scope.decls.values.toList.flatMap(s => env.get(s).map(s.name -> _)))

  /** Evaluates a file: the prelude, an imported file or the program. Its object declarations are named
   *  with the prefix `qualifier` (none if empty), except names in `shadowed`, which get the prefix
   *  `prelude` (the prelude's declarations that the program redeclares). Returns the environment
   *  extended with the file's declarations. */
  def evalFile(body: MExpr, env: Map[Sym, Value], qualifier: String, shadowed: Set[String] = Set.empty): Map[Sym, Value] =
    body match
      case MExpr.Body(items, scope, _) =>
        usedPrefixes += qualifier
        bodyEnv(items, scope, env, Frame(None, "", Origin.Source, None), Some(qualifier), shadowed)
      case _ => env

  /** Reserves the prefix of a file's object declarations, so module bodies do not reuse it. */
  def reserve(prefix: String): Unit = usedPrefixes += prefix

  private def bodyEnv(
      items: List[EItem],
      scope: Scope,
      env0: Map[Sym, Value],
      fr0: Frame,
      qualifier: Option[String] = None,
      shadowed: Set[String] = Set.empty
  ): Map[Sym, Value] =
    val prefix = qualifier.getOrElse(freshPrefix(fr0.hint))
    def objName(name: String) = if shadowed(name) then qualify("prelude", name) else qualify(prefix, name)
    val fr = fr0.copy(hyg = None)
    var env = env0
    // bind_π for all object declarations first: they may be mutually recursive
    val typeSyms = mutable.HashMap.empty[Sym, TypeSym]
    val relSyms = mutable.HashMap.empty[Sym, RelSym]
    for i <- items do
      i match
        case EItem.TypeDecl(s, _, sp) =>
          val ts = TypeSym(objName(s.name), TypeKind.Open, sp, fr.origin)
          ts.tparams = s.tparams
          typeSyms(s) = ts
          env += s -> VType(OType.Con(ts, Nil))
        case EItem.RelDecl(s, _, _, isStruct, sp) =>
          val kind = if isStruct then RelKind.Struct else if s.kind == SymKind.Ctor then RelKind.Ctor else RelKind.Plain
          val rs = RelSym(objName(s.name), kind, sp, fr.origin)
          rs.tparams = s.tparams
          relSyms(s) = rs
          env += s -> VRel(rs)
        case _ =>
    for i <- items do
      try
        i match
          case EItem.TypeDecl(s, k, _) =>
            val ts = typeSyms(s)
            k match
              case TypeKindE.Refinement(b) => ts.kind = TypeKind.Refinement(reifyType(b, env, fr))
              case TypeKindE.Open =>
            types += ts
          case EItem.RelDecl(s, cols, res, _, _) =>
            val rs = relSyms(s)
            rs.cols = cols.map(c => c.copy(tpe = reifyType(c.tpe, env, fr))).toVector
            rs.result = res.map(reifyType(_, env, fr))
            rels += rs
          case EItem.EdgeDecl(sub, sup, sp) =>
            val st = reifyType(sub, env, fr)
            eval(sup, env, fr) match
              case VType(OType.Con(ts, _)) => edges += Edge(st, ts)(sp, fr.origin)
              case _ =>
          case EItem.MetaDef(s, rhs, _) =>
            val v = eval(rhs, env, fr.copy(hint = qualify(prefix, s.name)))
            env += s -> v
            if s.kind == SymKind.FormulaFn && s.fnModes.nonEmpty then checkFnModes(s, v, fr)
          case EItem.RuleItem(r) =>
            val body = reifyBody(r.body, env, fr, identity)
            val heads = r.heads.map(reifyTerm(_, env, fr, identity))
            rules += Rule(r.name.map(qualify(prefix, _)), heads, body)(r.span, fr.origin, r.expansions)
          case EItem.QueryItem(q) =>
            queries += Query(reifyBody(q.body, env, fr, identity))(q.span, fr.origin, q.expansions)
          case EItem.DirectiveItem(d) =>
            val tgt = d.target.map {
              case RelRef.Spliced(m) =>
                eval(m, env, fr) match
                  case VRel(r) => RelRef.Sym(r)
                  case _ => throw Abort()
              case other => other
            }
            val kind = d.kind match
              case DirKind.TerminatesVar(vs, args) => DirKind.TerminatesVar(vs, args.map(reifyTerm(_, env, fr, identity)))
              case k => k
            directives += Directive(kind, tgt, d.rule.map(qualify(prefix, _)))(d.span, fr.origin)
      catch case _: Abort => ()
    env

/** Phase: evaluate the meta level; the result is an object program that may still contain families. */
final class MetaEvalPhase extends Phase:
  def phaseName = "metaEval"
  def description = "evaluate the meta level and emit object items (Section 4.5)"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.elab == null then return
    val ev = MetaEval()
    // object names: the program's and the prelude's declarations have no prefix (the prelude's get
    // `prelude.` where the program redeclares them), an imported file's are prefixed with its name
    val taken = mutable.HashSet("")
    val qualifiers = u.libraries.values.toList.map { lib =>
      lib -> (if lib.isPrelude then ""
              else Iterator.from(1).map(k => if k == 1 then lib.name else s"${lib.name}$k").find(taken.add).get)
    }.toMap
    qualifiers.values.foreach(ev.reserve)
    val shadowed = (for root <- Option(u.rootScope); lib <- u.libraries.values.find(_.isPrelude); p <- Option(lib.scope)
    yield root.decls.keySet.intersect(p.decls.keySet).toSet).getOrElse(Set.empty)
    // each file is evaluated once; the prelude's declarations are in scope everywhere, an imported file is
    // the module value of its `%import`s
    var preludeEnv = Map.empty[Sym, Value]
    var libraryValues = Map.empty[Sym, Value]
    for lib <- u.libraries.values; body <- Option(lib.body) do
      val env = ev.evalFile(body, preludeEnv ++ libraryValues, qualifiers(lib), if lib.isPrelude then shadowed else Set.empty)
      if lib.isPrelude then preludeEnv = env
      else
        val sc = lib.scope.nn
        for s <- Option(lib.sym) do
          libraryValues += s -> Value.VRec(sc.decls.values.toList.flatMap(d => env.get(d).map(d.name -> _)))
    ev.evalFile(u.elab.nn, preludeEnv ++ libraryValues, "")
    u.requirements = ev.requirements.toList
    u.generic =
      ObjProgram(ev.types.toVector, ev.rels.toVector, ev.edges.toVector, ev.rules.toVector, ev.queries.toVector, ev.directives.toVector)
  override def show(using Context): String = ObjPrinter.program(ctx.unit.generic.nn)
