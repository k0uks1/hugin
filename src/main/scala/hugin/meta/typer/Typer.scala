package hugin.meta
package typer

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{CmpOp, RelRef, ModeSpec, DirKind}
import hugin.obj
import scala.collection.mutable

/** Stage inference and meta typing (Sections 3.2, 4.2–4.4). Produces elaborated meta expressions with
 *  explicit quotes and splices; object code is checked for staging, arity and labels here, while object
 *  typing proper happens after elaboration (`objTyper`), with the meta-level call chain as context. */
final class Typer(c: Context, parents: List[SymTable] = Nil)
    extends TyperBase
    with Normalization
    with Declarations
    with TypeElaboration
    with MetaExpressions
    with ObjectCode:
  import MExpr.*
  import MType.*
  protected val context: Context = c
  val syms: SymTable = SymTable(parents)

  // ======================================================================= items and bodies

  private[meta] def elabRule(r: Rule, sc: Scope): Option[obj.Rule] =
    warnSingletons(r, sc)
    val rc = RuleCtx(allowVars = true)
    val heads = r.heads.flatMap(elabHead(_, sc, rc))
    val body = r.body.map(elabFormula(_, sc, rc)).getOrElse(Nil)
    if heads.length != r.heads.length || rc.failed then None
    else Some(obj.Rule(r.name.map(_.name), heads, body)(r.span, Origin.Source, rc.expansions.toList))

  /** W0002: object variables that occur only once in a rule or clause. Names starting with `_` are exempt,
   *  as are uppercase names that resolve to meta parameters. */
  private def warnSingletons(r: Rule, sc: Scope): Unit =
    def vars(x: Any): Iterator[VarRef] = x match
      case v: VarRef => Iterator(v)
      case p: Product => p.productIterator.flatMap(vars)
      case _ => Iterator.empty
    val occurrences = (r.heads ++ r.body).iterator.flatMap(vars).filterNot(_.name.startsWith("_")).toList
    for
      (name, List(v)) <- occurrences.groupBy(_.name).toList.sortBy(_._2.head.span.start)
      if !sc.lookup(name).exists(s => s.kind == SymKind.MetaParam || s.kind == SymKind.MetaDef)
    do
      ctx.report(Diagnostic.warning("W0002", s"variable `$name` occurs only once in this rule", v.span, "singleton variable")
        .withHelp(s"use `_` or `_$name` if this is intended")
        .withSuggestion(s"replace `$name` with `_`", v.span, "_")
        .withSuggestion(s"rename `$name` to `_$name`", v.span, s"_$name"))

  private[meta] def relTarget(t: Tree, sc: Scope, what: String): Option[RelRef] =
    classify(t, sc, null) match
      case Head.Obj(s) => Some(RelRef.Spliced(Ref(s)))
      case Head.Meta(m, RelT(_, _)) => Some(RelRef.Spliced(m))
      case Head.Bad | Head.Meta(_, MType.Err) => None
      case _ =>
        err("E0701", s"$what expects a relation", t.span, "not a relation")
        None

  private[meta] def elabDirective(d: Directive, sc: Scope): Option[obj.Directive] =
    def mk(k: DirKind, tgt: Tree) =
      relTarget(tgt, sc, s"`%${d.kind}`").map(r => obj.Directive(k, Some(r), None)(d.span, Origin.Source))
    d.args match
      case DirArgs.Mode(tgt, ms) =>
        // modes of formula functions were collected before the body (`collectFnModes`)
        tgt match
          case Ident(n) if sc.lookup(n).exists(_.kind == SymKind.FormulaFn) =>
            noteReference(tgt.span, sc.lookup(n).get)
            None
          case _ => mk(DirKind.ModeD(ModeSpec(ms.map(m => (m.input, m.label.map(_.name), m.span)))), tgt)
      case DirArgs.TerminatesVar(vs, tgt, args) =>
        val rc = RuleCtx(allowVars = true)
        mk(DirKind.TerminatesVar(vs.map(_.name), args.map(elabTerm(_, sc, rc))), tgt)
      case DirArgs.TerminatesLabel(ls, tgt) => mk(DirKind.TerminatesLabel(ls.map(_.name)), tgt)
      case DirArgs.Target(RuleRef(rn)) =>
        Some(obj.Directive(DirKind.Derivations, None, Some(rn))(d.span, Origin.Source))
      case DirArgs.Target(tgt) =>
        d.kind match
          case "partial" => mk(DirKind.Partial, tgt)
          case "open" => mk(DirKind.Open, tgt)
          case "input" => mk(DirKind.Input, tgt)
          case "output" => mk(DirKind.Output, tgt)
          case "derivations" => mk(DirKind.Derivations, tgt)
          case _ => None
      case DirArgs.NameHint(tgt, v) => mk(DirKind.NameHint(v.name), tgt)
      case DirArgs.Infix(_, _, _) => None

  /** Elaborates a meta definition or formula function in item order. */
  private[meta] def elabMetaDef(s: Sym): Option[MExpr] = inItemOf(s)(elabMetaDefIn(s))

  private def elabMetaDefIn(s: Sym): Option[MExpr] =
    val si = syms(s)
    si.state = ElabState.InProgress
    val sc = s.owner
    val result: Option[MExpr] = s.decl.get match
      case d @ Decl(name, params, tpe, _, defn, _) =>
        tpe match
          case Keyword(Kw.Mod) =>
            val sig = elabMType(defn.get, sc, TVars.NoTVars)
            si.sigValue = Some(sig)
            si.mtype = Some(ModU)
            si.static = Some(SigV(sig))
            Some(SigV(sig))
          case _ =>
            val psc = Scope(Some(sc), s"parameters of ${name.name}", ScopeKey.Params(s.key))
            val coll = mutable.ListBuffer.empty[Sym]
            val tv = TVars.MetaImplicit(psc, coll)
            val ps = elabParams(params, psc, tv)
            val resT = elabMType(tpe, psc, tv)
            // implicit parameters from the declared type are bound outermost
            val explicitT = ps.foldRight(resT)((p, acc) => Pi(p, syms.mtype(p).get, acc, isImplicit = false))
            val fullT = coll.foldRight(explicitT)((a, acc) => Pi(a, TypeU, acc, isImplicit = true))
            si.mtype = Some(fullT)
            if s.kind == SymKind.FormulaFn then
              if !endsInProp(resT) then
                err("E0103", s"formula function `${name.name}` must have a type ending in `prop`", tpe.span)
            defn match
              case Some(rhs) =>
                if s.clauses.nonEmpty then
                  ctx.report(Diagnostic.error(
                    "E0102",
                    s"formula function `${name.name}` has both a definition and clauses",
                    s.clauses.head.span,
                    "clause"
                  )
                    .withLabel(rhs.span, "definition"))
                val body = checkM(rhs, resT, psc)
                Some(coll.foldRight(ps.foldRight(body)((p, acc) => Lam(p, acc)))((a, acc) => Lam(a, acc)))
              case None if s.kind == SymKind.FormulaFn =>
                if s.clauses.isEmpty then
                  ctx.report(Diagnostic.warning("W0005", s"formula function `${name.name}` has no clauses", name.span, "always false"))
                Some(coll.foldRight(elabClauses(s, resT, psc))((a, acc) => Lam(a, acc)))
              case None => None
      case Def(name, params, rhs) =>
        val psc = Scope(Some(sc), s"parameters of ${name.name}", ScopeKey.Params(s.key))
        val coll = mutable.ListBuffer.empty[Sym]
        val ps = elabParams(params, psc, TVars.MetaImplicit(psc, coll))
        val (body, bt) = inferM(rhs, psc)
        val explicitT = ps.foldRight(bt)((p, acc) => Pi(p, syms.mtype(p).get, acc, isImplicit = false))
        si.mtype = Some(coll.foldRight(explicitT)((a, acc) => Pi(a, TypeU, acc, isImplicit = true)))
        if bt == ModU && ps.isEmpty then
          body match
            case SigV(sig) => si.sigValue = Some(sig)
            case _ =>
        Some(coll.foldRight(ps.foldRight(body)((p, acc) => Lam(p, acc)))((a, acc) => Lam(a, acc)))
      case _ => None
    result.foreach(r => if isStatic(r) then si.static = Some(r))
    if si.mtype.isEmpty then si.mtype = Some(MType.Err)
    si.state = ElabState.Done
    result

  private[meta] def arity(t: MType): Int = t match
    case Pi(_, _, c, false) => 1 + arity(c)
    case Pi(_, _, c, true) => arity(c)
    case _ => 0

  private[meta] def endsInProp(t: MType): Boolean = t match
    case Pi(_, _, c, _) => endsInProp(c)
    case PropT => true
    case _ => false

  private[meta] def elabParams(params: List[Param], psc: Scope, tv: TVars): List[Sym] =
    params.flatMap {
      case Param.Typed(n, tp, sp) =>
        val mt = elabMType(tp, psc, tv)
        val nm = n match
          case Ident(x) => x
          case VarRef(x) => x
          case _ => "_"
        if psc.lookupLocal(nm).isDefined then
          err("E0102", s"duplicate parameter `$nm`", n.span); None
        else
          val p = newParam(nm, n.span, psc)
          syms.setParamType(p, tp)
          syms.define(p, mt)
          psc.enter(p)
          Some(p)
      case Param.VarParam(v) =>
        ctx.report(Diagnostic.error("E0206", s"cannot infer the type of parameter `${v.name}`", v.span, "type needed")
          .withHelp(s"write `(${v.name} : T)` or declare the type of the definition"))
        None
    }

  /** Clauses `f t̄j :- ψj` define `f = [X̄] ⟨(X̄ = t̄1, ψ1) ; ... ; (X̄ = t̄k, ψk)⟩` (Section 4.8). */
  private[meta] def elabClauses(s: Sym, t: MType, sc: Scope): MExpr =
    val params = mutable.ListBuffer.empty[Sym]
    var cur = t
    val csc = localScope(Some(sc), s"clauses of ${s.name}")
    while cur.isInstanceOf[Pi] do
      val Pi(x, d, c, _) = cur: @unchecked
      val p = newParam(s"${s.name}#${params.length + 1}", s.span, csc)
      syms.define(p, d)
      params += p
      cur = substMT(c, Map(x -> Ref(p)))
    val alts = s.clauses.toList.flatMap { cl =>
      warnSingletons(cl, sc)
      val rc = RuleCtx(allowVars = true)
      val (_, args) = flattenApp(cl.heads.head)
      if args.length != params.length then
        err("E0207", s"clause of `${s.name}` has ${args.length} arguments, but the function takes ${params.length}", cl.heads.head.span)
        None
      else
        val eqs = params.toList.zip(args).map((p, a) =>
          obj.Formula.Cmp(CmpOp.Eq, obj.Term.Splice(Ref(p))(a.span), elabTerm(a, sc, rc))(a.span)
        )
        val body = cl.body.map(elabFormula(_, sc, rc)).getOrElse(Nil)
        Some(eqs ++ body)
    }
    val formula = alts match
      case List(single) => single
      case Nil => List(obj.Formula.Disj(Nil)(s.span))
      case many => List(obj.Formula.Disj(many)(s.span))
    params.foldRight(QuoteFormula(formula): MExpr)((p, acc) => Lam(p, acc))

  /** Records the `%mode` declarations of formula functions (Section 4.8) among `items`, which the meta
   *  evaluator checks; the function may be declared in an enclosing scope. */
  private def collectFnModes(items: List[Item], sc: Scope): Unit =
    for
      case d @ Directive(_, DirArgs.Mode(Ident(n), ms)) <- items
      f <- sc.lookup(n) if f.kind == SymKind.FormulaFn
    do syms(f).fnModes :+= ((ms.map(_.input), d.span))

  /** Elaborates one item of a module body into `out`. */
  private def elabItem(item: Item, sc: Scope, out: mutable.ListBuffer[EItem]): Unit =
    item match
      case d: Decl =>
        sc.lookupLocal(d.name.name).filter(_.decl.contains(d)) match
          case None =>
          case Some(s) =>
            s.kind match
              case SymKind.ObjType =>
                val di = info(s)
                out += EItem.TypeDecl(s, di.typeKind.getOrElse(TypeKindE.Open), d.span)
              case SymKind.Struct | SymKind.Rel | SymKind.Ctor =>
                val di = info(s)
                out += EItem.RelDecl(s, di.cols, di.result, s.kind == SymKind.Struct, d.span)
              case SymKind.TypeDef => ensureTypeDef(s, d.span)
              case SymKind.MetaDef | SymKind.FormulaFn =>
                elabMetaDef(s).foreach(m => out += EItem.MetaDef(s, m, d.span))
              case _ =>
      case d: Def =>
        sc.lookupLocal(d.name.name).filter(_.decl.contains(d)).foreach { s =>
          elabMetaDef(s).foreach(m => out += EItem.MetaDef(s, m, d.span))
        }
      case SubEdge(sub, sup) =>
        val st = elabOType(sub, sc, TVars.NoTVars)
        classify(sup, sc, null) match
          case Head.TypeLike(s) if s.kind == SymKind.ObjType =>
            if !info(s).typeKind.contains(TypeKindE.Open) then
              ctx.report(Diagnostic.error("E0404", s"`${s.name}` is not an open type", sup.span, "edge target must be open")
                .withLabel(s.span, "declared here"))
            else out += EItem.EdgeDecl(st, Ref(s), item.span)
          case Head.Meta(m, TypeU) => out += EItem.EdgeDecl(st, m, item.span)
          case Head.Bad =>
          case _ => err("E0404", "the target of a subtyping edge must be an open type", sup.span)
      case r: Rule =>
        val isClause = r.heads.headOption.exists { h =>
          flattenApp(h)._1 match
            case Ident(n) => sc.lookupLocal(n).exists(_.kind == SymKind.FormulaFn)
            case _ => false
        }
        if !isClause then elabRule(r, sc).foreach(x => out += EItem.RuleItem(x))
      case q: Query =>
        val rc = RuleCtx(allowVars = true)
        val body = elabFormula(q.body, sc, rc)
        if !rc.failed then out += EItem.QueryItem(obj.Query(body)(q.span, Origin.Source, rc.expansions.toList))
      case d: Directive => elabDirective(d, sc).foreach(x => out += EItem.DirectiveItem(x))

  /** Elaborates a module body (rule M-Body); returns the body and its signature of exports. */
  def elabBody(items: List[Item], sc: Scope, span: Span): (MExpr, MType) =
    context.unit.index.scope(span, sc)
    collectFnModes(items, sc)
    val out = mutable.ListBuffer.empty[EItem]
    for (item, key) <- items.zip(ItemKey.assign(sc.key, items)) do
      inItem(key)(elabItem(item, sc, out))
    // exports
    val fields = sc.decls.values.toList.flatMap { s =>
      s.kind match
        case SymKind.ObjType if syms.tparams(s).isEmpty => Some(s -> TypeU)
        case SymKind.Struct | SymKind.Rel | SymKind.Ctor if syms.tparams(s).isEmpty && syms.mtype(s).isDefined =>
          Some(s -> syms.mtype(s).get)
        case SymKind.TypeDef if syms.typeDef(s).exists(_.params.isEmpty) => Some(s -> TypeU)
        case SymKind.MetaDef | SymKind.FormulaFn if syms.mtype(s).exists(_ != MType.Err) => Some(s -> syms.mtype(s).get)
        case _ => None
    }
    (Body(out.toList, sc, span), Sig(fields, Nil))

  /** The module value of the file whose top-level scope is `sc` (what `%import` of the file refers to),
   *  with the signature of its exports. */
  def moduleValue(name: String, sc: Scope, sig: MType): Sym =
    val path = sc.key.file
    val s =
      Sym(name, SymKind.MetaDef, Span(context.unit.source, 0, 0), sc.parent.getOrElse(sc), Typer.moduleKey(path), context.unit.symKeys)
    syms.define(s, sig)
    s

  /** A one-line description of a symbol for tooling (hover). */
  def describe(s: Sym): String =
    def tps = if syms.tparams(s).isEmpty then "" else syms.tparams(s).map(_.name).mkString(" ", " ", "")
    def col(c: hugin.obj.Column) = c.label.map(l => s"($l : ${showO(c.tpe)})").getOrElse(showO(c.tpe))
    s.kind match
      case SymKind.BaseType => s"base type ${s.name}"
      case SymKind.ObjType =>
        info(s).typeKind match
          case Some(TypeKindE.Refinement(b)) => s"type ${s.name}$tps <: ${showO(b)}"
          case _ => s"type ${s.name}$tps (open)"
      case SymKind.TypeDef =>
        val td = syms.typeDef(s)
        val ps = td.toList.flatMap(_.params).map(p => s" ${p.name}").mkString
        s"type ${s.name}$ps = ${td.map(d => showO(d.rhs)).getOrElse("?")}"
      case SymKind.Rel | SymKind.Ctor | SymKind.Struct =>
        val di = info(s)
        val res = di.result.map(showO).getOrElse("rel")
        s"${s.kind.describe} ${s.name}$tps : ${(di.cols.map(col) :+ res).mkString(" -> ")}"
      case _ =>
        syms.sigValue(s) match
          case Some(sig) => s"signature ${s.name} = ${showMT(sig)}"
          case None => s"${s.kind.describe} ${s.name} : ${syms.mtype(s).fold("?")(showMT)}"

object Typer:
  /** The key of the module value of an imported file (`%import` refers to it); `%import` is not a name,
   *  so the key differs from the keys of the file's declarations. */
  def moduleKey(path: String): SymKey = SymKey(ScopeKey.File(path), "%import")

/** Phase: stage inference and meta typing of the program. The prelude and the imported files are
 *  elaborated apart, once ([[ElaboratedLibrary]]); the program's typer reads their results. */
final class TyperPhase extends Phase:
  def phaseName = "typer"
  def description = "stage inference and meta typing; inserts quotes and splices"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null || u.rootScope == null then return
    // files in dependency order: the prelude and every imported file before the files importing it
    for lib <- u.libraries.values if lib.named != null do
      val e = ctx.libraries.elaborated(lib.key)
      lib.elaborated = e
      e.diagnostics.foreach(ctx.report)
      u.symKeys.inherit(e.keys)
      u.index.include(e.index)
      u.scopes ++= e.scopes
    val typer = Typer(ctx, u.libraries.values.toList.flatMap(l => Option(l.elaborated).map(_.symbols)))
    u.symbols = typer.syms
    val (body, _) = typer.elabBody(u.untpd.nn.items, u.rootScope.nn, u.untpd.nn.span)
    u.elab = body
    // the semantic index: declarations of all scopes and descriptions of every known symbol
    val scopes = u.rootScope.nn :: u.libraries.values.toList.flatMap(l => Option(l.scope)) :::
      u.scopes.values.toList
    for sc <- scopes; s <- sc.decls.values do u.index.declare(s)
    for s <- u.index.symbols do u.index.describe(s, typer.describe(s))
    // unused top-level functions and constants; module-valued definitions emit rules even when unreferenced
    val used = u.index.references.collect { case r if r.isUse => r.sym }.toSet
    for s <- u.rootScope.nn.decls.values if (s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn) && !used(s) do
      val isModuleValued = typer.syms.mtype(s) match
        case Some(MType.Sig(_, _) | MType.ModU | MType.Err) | None => true
        case _ => false
      if !isModuleValued then
        ctx.report(Diagnostic.warning("W0003", s"unused definition `${s.name}`", s.span, "never referenced"))
  override def show(using Context): String = MetaPrinter(ctx.unit.symbols).showBody(ctx.unit.elab.nn)
