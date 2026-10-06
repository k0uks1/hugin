package hugin.meta

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{OType, Column, TParam, BaseType, Mode, ArithOp, CmpOp, RelRef, Expansion, ModeSpec, DirKind}
import hugin.obj
import scala.collection.mutable

/** Elaborated information about an object declaration. */
final case class DeclInfo(cols: List[Column], result: Option[OType], typeKind: Option[TypeKindE])

/** Per-rule state while elaborating object code. */
final class RuleCtx(val allowVars: Boolean):
  val expansions: mutable.ListBuffer[Expansion] = mutable.ListBuffer.empty

  /** Set when a structural error was reported; the item is then dropped to avoid cascading errors. */
  var failed = false

  /** Nesting depth of aggregate bodies (negative context). */
  var aggDepth = 0
  private var wild = 0
  def freshWild(): String = { wild += 1; s"${obj.Var.WildPrefix}$wild" }

/** How uppercase identifiers that do not resolve are treated in types. */
enum TVars:
  case NoTVars

  /** Implicit type parameters of an object declaration (a family). */
  case Family(explicit: Map[String, TParam], implicits: mutable.LinkedHashMap[String, TParam], allowImplicit: Boolean)

  /** Implicit meta parameters of a meta function type (entered into `scope`). */
  case MetaImplicit(scope: Scope, collected: mutable.ListBuffer[Sym])

/** Stage inference and meta typing (Sections 3.2, 4.2–4.4). Produces elaborated meta expressions with
 *  explicit quotes and splices; object code is checked for staging, arity and labels here, while object
 *  typing proper happens after elaboration (`objTyper`), with the meta-level call chain as context. */
final class Typer(using Context):
  import MExpr.*
  import MType.*

  val declInfo: mutable.HashMap[Sym, DeclInfo] = mutable.HashMap.empty
  private var freshN = 0
  private def fresh(prefix: String): String = { freshN += 1; s"$prefix$freshN" }

  private def err(code: String, msg: String, span: Span, label: String = ""): Unit =
    ctx.error(code, msg, span, label)

  // ======================================================================= names

  private def editDistance(a: String, b: String): Int =
    val d = Array.tabulate(a.length + 1, b.length + 1)((i, j) => if i == 0 then j else if j == 0 then i else 0)
    for i <- 1 to a.length; j <- 1 to b.length do
      d(i)(j) = (d(i - 1)(j) + 1).min(d(i)(j - 1) + 1).min(d(i - 1)(j - 1) + (if a(i - 1) == b(j - 1) then 0 else 1))
    d(a.length)(b.length)

  private def suggestion(name: String, sc: Scope): Option[String] =
    val cands = sc.allNames.toList.distinct.filter(n => n != name && n.headOption.map(_.isUpper) == name.headOption.map(_.isUpper))
    cands.map(n => (editDistance(n, name), n)).filter(_._1 <= (name.length / 3).max(1)).sortBy(_._1).headOption.map(_._2)

  private def unresolved(name: String, span: Span, sc: Scope, what: String = "name"): Unit =
    var d = Diagnostic.error("E0101", s"unresolved $what `$name`", span, "not found in this scope")
    suggestion(name, sc).foreach(s => d = d.withHelp(s"a declaration with a similar name exists: `$s`"))
    ctx.report(d)

  private def lookup(name: String, span: Span, sc: Scope): Option[Sym] =
    sc.lookup(name) match
      case some @ Some(s) => s.used = true; some
      case None => unresolved(name, span, sc); None

  /** Forward-reference check for meta definitions (Section 2.3). */
  private def visible(s: Sym, span: Span): Boolean =
    if s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn then
      s.state match
        case Sym.State.Done => s.mtype != null
        case Sym.State.InProgress =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` refers to itself", span, "recursive reference")
            .withLabel(s.span, "while elaborating this definition")
            .withNote("the meta level has no recursion; definitions may only refer to earlier definitions"))
          false
        case Sym.State.Pending =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` is used before its definition", span, "used here")
            .withLabel(s.span, "defined later here")
            .withNote("meta definitions may only refer to earlier definitions (Section 2.3)"))
          false
    else true

  // ======================================================================= substitution / normalization

  def substM(m: MExpr, s: Map[Sym, MExpr]): MExpr = if s.isEmpty then m
  else
    m match
      case Ref(x) => s.getOrElse(x, m)
      case Op(op, l, r, sp) => Op(op, substM(l, s), substM(r, s), sp)
      case Neg(x, sp) => Neg(substM(x, s), sp)
      case Proj(x, l) => Proj(substM(x, s), l)
      case Rec(fs) => Rec(fs.map((l, e) => (l, substM(e, s))))
      case App(f, a, sp) => App(substM(f, s), substM(a, s), sp)
      case QuoteType(t) => QuoteType(substO(t, s))
      case FactTypeOf(x) => FactTypeOf(substM(x, s))
      case TApp(f, as) => TApp(substM(f, s), as.map(substO(_, s)))
      case SigV(t) => SigV(substMT(t, s))
      case other => other

  def substO(t: OType, s: Map[Sym, MExpr]): OType = if s.isEmpty then t
  else
    OType.mapDeep(t) {
      case OType.Splice(m) => normO(OType.Splice(substM(m, s)))
    }

  def substMT(t: MType, s: Map[Sym, MExpr]): MType = if s.isEmpty then t
  else
    t match
      case Code(o) => Code(substO(o, s))
      case RelT(cols) => RelT(cols.map(c => c.copy(tpe = substO(c.tpe, s))))
      case Pi(x, d, c, imp) => Pi(x, substMT(d, s), substMT(c, s - x), imp)
      case Sig(fs, reqs) => Sig(fs.map((f, ft) => (f, substMT(ft, s))), reqs)
      case other => other

  /** Static normal form of meta expressions occurring in types (Section 4.3). */
  def normM(m: MExpr): MExpr = m match
    case Ref(s) if s.static.isDefined && (s.static.get ne m) => normM(s.static.get)
    case Proj(x, l) =>
      normM(x) match
        case Rec(fs) => fs.find(_._1 == l).map(f => normM(f._2)).getOrElse(Proj(Rec(fs), l))
        case nx => Proj(nx, l)
    case FactTypeOf(x) => FactTypeOf(normM(x))
    case TApp(f, as) => TApp(normM(f), as.map(normO))
    case QuoteType(t) =>
      normO(t) match
        case OType.Splice(inner) => inner
        case nt => QuoteType(nt)
    case Rec(fs) => Rec(fs.map((l, e) => (l, normM(e))))
    case other => other

  def normO(t: OType): OType = t match
    case OType.Splice(m) =>
      normM(m) match
        case QuoteType(inner) => normO(inner)
        case nm => OType.Splice(nm)
    case OType.Con(s, as) => OType.Con(s, as.map(normO))
    case OType.Fact(r, as) => OType.Fact(r, as.map(normO))
    case OType.Union(ms) => OType.union(ms.map(normO))
    case other => other

  def typesEqual(a: OType, b: OType): Boolean = normO(a) == normO(b)

  private def isStatic(m: MExpr): Boolean = m match
    case Ref(_) | Lit(_) | QuoteType(_) | SigV(_) => true
    case Proj(x, _) => isStatic(x)
    case Rec(fs) => fs.forall(f => isStatic(f._2))
    case FactTypeOf(x) => isStatic(x)
    case TApp(f, _) => isStatic(f)
    case _ => false

  // ======================================================================= object declarations

  private def flattenApp(t: Tree): (Tree, List[Tree]) =
    def go(t: Tree, acc: List[Tree]): (Tree, List[Tree]) = t match
      case Apply(f, a) => go(f, a :: acc)
      case Parens(i) if acc.isEmpty => go(i, acc)
      case other => (other, acc)
    go(t, Nil)

  private def flattenArrow(t: Tree): (List[(Option[Ident], Tree)], Tree) = t match
    case Arrow(l, d, c) =>
      val (ds, cod) = flattenArrow(c)
      ((l, d) :: ds, cod)
    case Parens(i @ Arrow(_, _, _)) => flattenArrow(i)
    case other => (Nil, other)

  def info(s: Sym): DeclInfo =
    ensureDecl(s)
    declInfo.getOrElse(s, DeclInfo(Nil, None, None))

  def relCols(s: Sym): List[Column] = info(s).cols

  /** Elaborates an object declaration (lazily: object declarations may be used before they occur). */
  def ensureDecl(s: Sym): Unit =
    if s.state != Sym.State.Pending || !s.kind.isObjectDecl then return
    s.state = Sym.State.InProgress
    val d = s.decl.get.asInstanceOf[Decl]
    val sc = s.owner
    val explicit = d.params.flatMap {
      case Param.VarParam(v) => Some(v.name -> TParam(v.name))
      case p =>
        err("E0004", "object declarations take only type parameters", p.span, "expected an uppercase type parameter")
        None
    }
    s.tparams = explicit.map(_._2)
    val implicits = mutable.LinkedHashMap.empty[String, TParam]
    val allowImplicit = s.kind == SymKind.Rel || s.kind == SymKind.Ctor
    val tv = TVars.Family(explicit.toMap, implicits, allowImplicit)
    def columns(doms: List[(Option[Ident], Tree)]): List[Column] =
      val seen = mutable.HashMap.empty[String, Span]
      doms.map { (l, t) =>
        l.foreach { id =>
          seen.get(id.name) match
            case Some(prev) =>
              ctx.report(Diagnostic.error("E0307", s"duplicate label `${id.name}`", id.span, "duplicate").withLabel(
                prev,
                "first used here"
              ))
            case None => seen(id.name) = id.span
        }
        Column(l.map(_.name), elabOType(t, sc, tv))
      }
    val di = s.kind match
      case SymKind.ObjType =>
        val k = d.sup match
          case Some(sup) => TypeKindE.Refinement(elabOType(sup, sc, tv))
          case None => TypeKindE.Open
        s.mtype = TypeU
        DeclInfo(Nil, None, Some(k))
      case SymKind.Struct =>
        val rt = d.defn.get.asInstanceOf[RecordType]
        val doms = rt.entries.flatMap {
          case SigEntry.FieldDecl(l, t) => Some((Some(l), t))
          case SigEntry.Complete(_, sp) => err("E0004", "requirements are not allowed in struct declarations", sp); None
          case SigEntry.ModeReq(_, _, sp) => err("E0004", "requirements are not allowed in struct declarations", sp); None
        }
        val cols = columns(doms)
        s.mtype = RelT(cols)
        DeclInfo(cols, None, None)
      case SymKind.Rel =>
        val (doms, _) = flattenArrow(d.tpe)
        val cols = columns(doms)
        s.mtype = RelT(cols)
        DeclInfo(cols, None, None)
      case SymKind.Ctor =>
        val (doms, cod) = flattenArrow(d.tpe)
        val cols = columns(doms)
        val res = elabOType(cod, sc, tv)
        if !isOpenType(res) && res != OType.Err then
          val what = normO(res) match
            case OType.Base(b) => s"the base type `${b.show}`"
            case _ => s"`${showO(res)}`, which is not an open type"
          ctx.report(
            Diagnostic.error("E0103", s"cannot classify the declaration of `${s.name}`", cod.span, s"result is $what")
              .withNote("a declaration `c : A -> ... -> R.` declares a relation if R is `rel` and a constructor if R is an open type")
              .withHelp(if doms.isEmpty then s"to define a compile-time constant, write `${s.name} : ${Printer.show(d.tpe)} = ...`."
              else "end the type in `rel` to declare a relation")
          )
        s.mtype = RelT(cols)
        DeclInfo(cols, Some(res), None)
      case _ => DeclInfo(Nil, None, None)
    s.tparams = s.tparams ++ implicits.values
    declInfo(s) = di
    s.state = Sym.State.Done

  private def isOpenType(t: OType): Boolean = normO(t) match
    case OType.Splice(Ref(s)) => s.kind == SymKind.ObjType && info(s).typeKind.contains(TypeKindE.Open)
    case OType.Splice(TApp(Ref(s), _)) => s.kind == SymKind.ObjType && info(s).typeKind.contains(TypeKindE.Open)
    case OType.Splice(m) =>
      // abstract types (parameters, module paths) of kind `type` may be open
      true
    case _ => false

  /** Elaborates a type definition (Section 4.7) with cycle detection. */
  def ensureTypeDef(s: Sym, useSpan: Span): Boolean =
    s.state match
      case Sym.State.Done => true
      case Sym.State.InProgress =>
        ctx.report(Diagnostic.error("E0104", s"cyclic type definition `${s.name}`", useSpan, "refers back to the definition")
          .withLabel(s.span, "type definition declared here")
          .withNote("type definitions are unfolded and must not form a cycle; declare an open type or struct instead"))
        false
      case Sym.State.Pending =>
        s.state = Sym.State.InProgress
        val d = s.decl.get.asInstanceOf[Decl]
        val psc = Scope(Some(s.owner), s"parameters of ${s.name}")
        val ps = d.params.flatMap {
          case Param.VarParam(v) =>
            val p = Sym(v.name, SymKind.MetaParam, v.span, psc)
            p.mtype = TypeU
            p.state = Sym.State.Done
            psc.enter(p)
            Some(p)
          case p => err("E0004", "type definitions take only type parameters", p.span); None
        }
        s.typeDefParams = ps
        val rhs = elabOType(d.defn.get, psc, TVars.NoTVars)
        s.typeDefRhs = Some(rhs)
        // strictness: each parameter occurs on the right-hand side
        val occurring = mutable.HashSet.empty[Sym]
        def collect(m: MExpr): Unit = m match
          case Ref(x) => occurring += x
          case Proj(x, _) => collect(x)
          case TApp(f, as) => collect(f); as.foreach(collectO)
          case FactTypeOf(x) => collect(x)
          case QuoteType(t) => collectO(t)
          case _ =>
        def collectO(t: OType): Unit = OType.exists(t) {
          case OType.Splice(m) => collect(m); false
          case _ => false
        }
        collectO(rhs)
        val missing = ps.filterNot(occurring)
        if missing.nonEmpty && !s.abbrev then
          ctx.report(Diagnostic.error(
            "E0106",
            s"type definition `${s.name}` is not strict",
            d.span,
            s"parameter${if missing.length > 1 then "s" else ""} ${missing.map(p => s"`${p.name}`").mkString(", ")} not used"
          )
            .withHelp(s"mark it `%abbrev ${Printer.showItem(d).stripSuffix(".")}.` to have it always expanded"))
        s.mtype = TypeU
        s.state = Sym.State.Done
        true

  private def unfoldTypeDef(s: Sym, args: List[OType], span: Span): OType =
    if !ensureTypeDef(s, span) then return OType.Err
    if args.length != s.typeDefParams.length then
      err("E0207", s"type definition `${s.name}` expects ${s.typeDefParams.length} type argument(s), found ${args.length}", span)
      return OType.Err
    normO(substO(s.typeDefRhs.getOrElse(OType.Err), s.typeDefParams.zip(args.map(QuoteType(_))).toMap))

  // ======================================================================= object types

  def elabOType(t: Tree, sc: Scope, tv: TVars): OType = t match
    case Parens(i) => elabOType(i, sc, tv)
    case Keyword(Kw.Rel) => OType.RelTop
    case Keyword(k) =>
      err("E0202", s"`${k.toString.toLowerCase}` is not an object type", t.span, "expected an object type")
      OType.Err
    case Trees.Union(l, r) => OType.union(List(elabOType(l, sc, tv), elabOType(r, sc, tv)))
    case VarRef(n) =>
      tv match
        case TVars.Family(ex, _, _) if ex.contains(n) => OType.Param(ex(n))
        case TVars.Family(_, imp, _) if imp.contains(n) => OType.Param(imp(n))
        case _ =>
          sc.lookup(n) match
            case Some(s) if s.kind == SymKind.MetaParam || s.kind == SymKind.MetaDef =>
              s.mtype match
                case TypeU => OType.Splice(Ref(s))
                case RelT(_) => OType.Splice(FactTypeOf(Ref(s)))
                case null => OType.Err
                case other =>
                  err("E0202", s"`$n` is not a type", t.span, s"has meta type ${other.show}")
                  OType.Err
            case _ =>
              tv match
                case TVars.Family(_, imp, true) =>
                  val p = TParam(n)
                  imp(n) = p
                  OType.Param(p)
                case TVars.MetaImplicit(isc, coll) =>
                  val p = Sym(n, SymKind.MetaParam, t.span, isc)
                  p.mtype = TypeU
                  p.state = Sym.State.Done
                  isc.enter(p)
                  coll += p
                  OType.Splice(Ref(p))
                case _ =>
                  unresolved(n, t.span, sc, "type variable")
                  OType.Err
    case _: Ident | _: Apply | _: Select =>
      val (head, args) = flattenApp(t)
      head match
        case id @ Ident(n) =>
          lookup(n, id.span, sc) match
            case None => OType.Err
            case Some(s) =>
              def argTypes = args.map(elabOType(_, sc, tv))
              s.kind match
                case SymKind.PreludeType =>
                  if args.nonEmpty then err("E0207", s"`$n` takes no type arguments", t.span)
                  OType.Base(s.base.get)
                case SymKind.TypeDef => unfoldTypeDef(s, argTypes, t.span)
                case SymKind.ObjType | SymKind.Struct | SymKind.Rel | SymKind.Ctor =>
                  ensureDecl(s)
                  val as = argTypes
                  if s.state == Sym.State.Done && as.length != s.tparams.length then
                    if s.tparams.nonEmpty && as.isEmpty then
                      err(
                        "E0207",
                        s"family `$n` needs ${s.tparams.length} type argument(s)",
                        t.span,
                        s"expected `$n ${s.tparams.map(_.name).mkString(" ")}`"
                      )
                    else err("E0207", s"`$n` expects ${s.tparams.length} type argument(s), found ${as.length}", t.span)
                    OType.Err
                  else
                    val m = if as.isEmpty then Ref(s) else TApp(Ref(s), as)
                    if s.kind == SymKind.ObjType then OType.Splice(m) else OType.Splice(FactTypeOf(m))
                case SymKind.MetaDef | SymKind.MetaParam =>
                  if !visible(s, id.span) then OType.Err
                  else if args.nonEmpty then
                    err("E0202", s"`$n` cannot be applied to type arguments", t.span); OType.Err
                  else
                    s.mtype match
                      case TypeU => OType.Splice(Ref(s))
                      case RelT(_) => OType.Splice(FactTypeOf(Ref(s)))
                      case other =>
                        err("E0202", s"`$n` is not a type", id.span, s"has meta type ${if other == null then "?" else other.show}")
                        OType.Err
                case SymKind.FormulaFn =>
                  err("E0202", s"formula function `$n` is not a type", id.span); OType.Err
        case sel: Select =>
          val (m, mt) = inferM(sel, sc)
          if args.nonEmpty then
            err("E0202", "type application through a module path is not supported", t.span); OType.Err
          else
            mt match
              case TypeU => OType.Splice(m)
              case RelT(_) => OType.Splice(FactTypeOf(m))
              case MType.Err => OType.Err
              case other => err("E0202", s"`${Printer.show(sel)}` is not a type", sel.span, s"has meta type ${other.show}"); OType.Err
        case other =>
          err("E0202", "expected an object type", other.span); OType.Err
    case ErrorTree() => OType.Err
    case other =>
      err("E0202", "expected an object type", other.span, "not a type")
      OType.Err

  // ======================================================================= meta types

  def elabMType(t: Tree, sc: Scope, tv: TVars): MType = t match
    case Parens(i) => elabMType(i, sc, tv)
    case Keyword(Kw.Type) => TypeU
    case Keyword(Kw.Mod) => ModU
    case Keyword(Kw.Prop) => PropT
    case Keyword(Kw.Rel) => RelT(Nil)
    case Ident(n) if sc.lookup(n).exists(_.kind == SymKind.PreludeType) => Prim(sc.lookup(n).get.base.get)
    case Ident(n)
        if sc.lookup(n).exists(s =>
          s.kind == SymKind.MetaDef && s.decl.exists {
            case Decl(_, _, Keyword(Kw.Mod), _, _, _) => true
            case Def(_, _, _: RecordType) => true
            case _ => false
          }
        ) =>
      val s = sc.lookup(n).get
      s.used = true
      if !visible(s, t.span) then MType.Err else s.sigValue.getOrElse(MType.Err)
    case sel: Select =>
      val (m, mt) = inferM(sel, sc)
      mt match
        case ModU => normM(m) match
            case SigV(sig) => sig
            case _ => err("E0202", "signature paths must be statically known", sel.span); MType.Err
        case TypeU => Code(OType.Splice(m))
        case RelT(_) => Code(OType.Splice(FactTypeOf(m)))
        case MType.Err => MType.Err
        case other => err("E0202", s"`${Printer.show(sel)}` is not a type", sel.span, s"has meta type ${other.show}"); MType.Err
    case rt: RecordType => elabSig(rt, sc, tv)
    case _: Arrow =>
      val (doms, cod) = flattenArrow(t)
      cod match
        case Keyword(Kw.Rel) =>
          RelT(doms.map((l, d) => Column(l.map(_.name), elabOType(d, sc, tv))))
        case Keyword(Kw.Prop) if doms.forall((_, d) => isObjectTypeTree(d, sc)) =>
          // a formula function type: ⇑A1 → ··· → ⇑An → ⇑prop (Section 4.8)
          val psc = Scope(Some(sc), "formula function type")
          doms.foldRight(PropT: MType) { case ((l, d), acc) =>
            val x = Sym(l.map(_.name).getOrElse(fresh("_")), SymKind.MetaParam, l.map(_.span).getOrElse(d.span), psc)
            val dt = Code(elabOType(d, sc, tv))
            x.mtype = dt
            x.state = Sym.State.Done
            Pi(x, dt, acc, isImplicit = false)
          }
        case _ =>
          val psc = Scope(Some(sc), "function type")
          val tv2 = tv match
            case TVars.MetaImplicit(_, coll) => tv
            case other => other
          def go(ds: List[(Option[Ident], Tree)]): MType = ds match
            case Nil => elabMType(cod, psc, tv2)
            case (l, d) :: rest =>
              val dt = elabMType(d, psc, tv2)
              val x = Sym(l.map(_.name).getOrElse(fresh("_")), SymKind.MetaParam, l.map(_.span).getOrElse(d.span), psc)
              x.mtype = dt
              x.state = Sym.State.Done
              l.foreach(_ => psc.enter(x))
              Pi(x, dt, go(rest), isImplicit = false)
          go(doms)
    case _ => Code(elabOType(t, sc, tv))

  /** Whether a type tree denotes an object type (rather than a meta type such as a signature or function type). */
  private def isObjectTypeTree(t: Tree, sc: Scope): Boolean = t match
    case Parens(i) => isObjectTypeTree(i, sc)
    case _: Arrow | _: RecordType => false
    case Keyword(k) => k == Kw.Rel
    case Ident(n) =>
      sc.lookup(n) match
        case Some(s) if s.kind == SymKind.MetaDef && s.sigValue.isDefined => false
        case Some(s) if s.kind == SymKind.MetaDef || s.kind == SymKind.MetaParam => s.mtype == TypeU || s.mtype.isInstanceOf[RelT]
        case _ => true
    case _ => true

  private def elabSig(rt: RecordType, sc: Scope, tv: TVars): MType =
    val ssc = Scope(Some(sc), "signature")
    val fields = mutable.ListBuffer.empty[(Sym, MType)]
    val reqs = mutable.ListBuffer.empty[Req]
    for e <- rt.entries do
      e match
        case SigEntry.FieldDecl(l, ft) =>
          if ssc.lookupLocal(l.name).isDefined then
            err("E0307", s"duplicate field `${l.name}` in signature", l.span)
          else
            val fty = elabMType(ft, ssc, tv)
            val f = Sym(l.name, SymKind.MetaParam, l.span, ssc)
            f.mtype = fty
            f.state = Sym.State.Done
            ssc.enter(f)
            fields += ((f, fty))
        case SigEntry.Complete(l, sp) =>
          fields.find(_._1.name == l.name) match
            case Some((_, RelT(_))) => reqs += Req.Complete(l.name, sp)
            case Some(_) => err("E0208", s"`%complete` requires a relation field, but `${l.name}` is not one", l.span)
            case None => unresolved(l.name, l.span, ssc, "field")
        case SigEntry.ModeReq(l, ms, sp) =>
          fields.find(_._1.name == l.name) match
            case Some((_, RelT(cols))) =>
              if ms.length != cols.length then
                err("E0207", s"mode for `${l.name}` has ${ms.length} items but the relation has ${cols.length} columns", sp)
              else reqs += Req.HasMode(l.name, Mode(ms.map(_.input).toVector), sp)
            case Some(_) => err("E0208", s"`%mode` requires a relation field, but `${l.name}` is not one", l.span)
            case None => unresolved(l.name, l.span, ssc, "field")
    Sig(fields.toList, reqs.toList)

  // ======================================================================= meta subtyping (Section 4.4)

  /** Returns an explanation if `a ≤ b` fails. */
  def subsumes(a: MType, b: MType): Option[String] = (a, b) match
    case (MType.Err, _) | (_, MType.Err) => None
    case (Code(_), Code(_)) => None // checked by subsumption at the object level after elaboration
    case (TypeU, TypeU) | (PropT, PropT) | (ModU, ModU) => None
    case (Prim(x), Prim(y)) if x == y => None
    case (RelT(c1), RelT(c2)) =>
      if c1.length != c2.length then Some(s"relation with ${c1.length} columns where ${c2.length} are expected")
      else
        c1.zip(c2).zipWithIndex.collectFirst {
          case ((x, y), i)
              if !typesEqual(x.tpe, y.tpe) && !OType.exists(normO(x.tpe))(_ == OType.Err) && !OType.exists(normO(y.tpe))(_ == OType.Err) =>
            s"column ${i + 1} has type `${showO(x.tpe)}` but `${showO(y.tpe)}` is expected (relation types are invariant)"
        }
    case (Pi(x, d1, c1, i1), Pi(y, d2, c2, i2)) if i1 == i2 =>
      subsumes(d2, d1).map("parameter: " + _).orElse(subsumes(substMT(c1, Map(x -> Ref(y))), c2))
    case (Sig(f1, _), Sig(f2, _)) =>
      val self = Sym("self", SymKind.MetaParam, Span.NoSpan, Namer.prelude)
      val s1 = f1.map((f, _) => f -> Proj(Ref(self), f.name)).toMap
      val s2 = f2.map((f, _) => f -> Proj(Ref(self), f.name)).toMap
      f2.iterator.map { (g, gt) =>
        f1.find(_._1.name == g.name) match
          case None => Some(s"missing field `${g.name}`")
          case Some((_, ft)) => subsumes(substMT(ft, s1), substMT(gt, s2)).map(r => s"field `${g.name}`: $r")
      }.collectFirst { case Some(r) => r }
    case _ => Some(s"expected `${showMT(b)}`, found `${showMT(a)}`")

  def showO(t: OType): String = normO(t) match
    case OType.Splice(m) => showPath(m)
    case other => OType.show(OType.mapDeep(other) { case OType.Splice(m) => OType.Splice(m) }).replace("~(", "(")
  private def showPath(m: MExpr): String = m match
    case Ref(s) => s.name
    case Proj(x, l) => s"${showPath(x)}.$l"
    case FactTypeOf(x) => showPath(x)
    case TApp(f, as) => (showPath(f) :: as.map(showO)).mkString(" ")
    case other => MExpr.show(other)

  def showMT(t: MType): String = t match
    case Code(o) => s"⇑${showO(o)}"
    case RelT(cols) => s"⇑(${(cols.map(c => c.label.map(l => s"$l : ").getOrElse("") + showO(c.tpe)) :+ "rel").mkString(" -> ")})"
    case Pi(x, d, c, imp) =>
      val dom = if imp then s"{${x.name} : ${showMT(d)}}" else if x.name.startsWith("_") then showMT(d) else s"(${x.name} : ${showMT(d)})"
      s"$dom -> ${showMT(c)}"
    case Sig(fs, _) => fs.map((s, ft) => s"${s.name} : ${showMT(ft)}").mkString("{ ", ", ", " }")
    case other => other.show

  private def mismatch(expected: MType, found: MType, span: Span, reason: String): Unit =
    var d = Diagnostic.error("E0203", "meta type mismatch", span, s"expected `${showMT(expected)}`")
      .withNote(s"found `${showMT(found)}`")
    if !reason.startsWith("expected") then d = d.withNote(reason)
    ctx.report(d)

  // ======================================================================= meta expressions

  /** Classification of the head of an application spine. */
  private enum Head:
    case Obj(s: Sym) // object relation / constructor / struct
    case TypeLike(s: Sym) // object type, type definition or base type
    case Meta(m: MExpr, t: MType) // meta value
    case ObjVar(name: String)
    case Bad

  private def classify(t: Tree, sc: Scope, rc: RuleCtx | Null): Head =
    val h = classify0(t, sc, rc)
    if h == Head.Bad && rc != null then rc.failed = true
    h

  private def classify0(t: Tree, sc: Scope, rc: RuleCtx | Null): Head = t match
    case Parens(i) => classify(i, sc, rc)
    case Ident(n) =>
      lookup(n, t.span, sc) match
        case None => Head.Bad
        case Some(s) =>
          s.kind match
            case SymKind.ObjType | SymKind.TypeDef | SymKind.PreludeType => Head.TypeLike(s)
            case SymKind.Rel | SymKind.Ctor | SymKind.Struct => ensureDecl(s); Head.Obj(s)
            case SymKind.MetaDef | SymKind.FormulaFn | SymKind.MetaParam =>
              if !visible(s, t.span) || s.mtype == null then Head.Bad else Head.Meta(Ref(s), s.mtype.nn)
    case VarRef(n) =>
      sc.lookup(n) match
        case Some(s) if (s.kind == SymKind.MetaParam || s.kind == SymKind.MetaDef) && s.mtype != null && (rc == null || capturesVar(s)) =>
          s.used = true
          Head.Meta(Ref(s), s.mtype.nn)
        case _ =>
          if rc == null then
            unresolved(n, t.span, sc, "variable")
            Head.Bad
          else Head.ObjVar(n)
    case sel: Select =>
      val (m, mt) = inferM(sel, sc)
      if mt == MType.Err then Head.Bad else Head.Meta(m, mt)
    case _ => Head.Bad

  /** Inside object code, an uppercase meta variable is spliced/persisted only if it denotes code or a primitive. */
  private def capturesVar(s: Sym): Boolean = s.mtype match
    case Code(_) | Prim(_) | PropT | RelT(_) => true
    case Pi(_, _, _, _) => true
    case _ => false

  def inferM(t: Tree, sc: Scope): (MExpr, MType) = t match
    case Parens(i) => inferM(i, sc)
    case Trees.Lit(l) => (MExpr.Lit(l), Prim(BaseType.of(l)))
    case Trees.Neg(x) =>
      val (m, mt) = inferM(x, sc)
      mt match
        case Prim(BaseType.IntT) | Prim(BaseType.FloatT) => (MExpr.Neg(m, t.span), mt)
        case MType.Err => (MExpr.Err, MType.Err)
        case other => mismatch(Prim(BaseType.IntT), other, x.span, "unary minus applies to numbers"); (MExpr.Err, MType.Err)
    case Infix(op, l, r) if ArithOp.fromString(op).isDefined =>
      val (ml, tl) = inferM(l, sc)
      val (mr, tr) = inferM(r, sc)
      val aop = ArithOp.fromString(op).get
      (tl, tr) match
        case (MType.Err, _) | (_, MType.Err) => (MExpr.Err, MType.Err)
        case (Prim(a), Prim(b)) if a == b && (if aop == ArithOp.Concat then a == BaseType.StringT else a != BaseType.StringT) =>
          (Op(aop, ml, mr, t.span), tl)
        case _ =>
          ctx.report(Diagnostic.error("E0203", s"operator `$op` cannot be applied to `${showMT(tl)}` and `${showMT(tr)}`", t.span)
            .withNote("`+ - * /` apply to two ints or two floats, `^` to two strings"))
          (MExpr.Err, MType.Err)
    case _: Ident | _: VarRef | _: Select | _: Apply =>
      val (head, args) = flattenApp(t)
      head match
        case Select(q, l) if args.isEmpty => inferSelect(t.asInstanceOf[Select], sc)
        case _ =>
          classify(head, sc, null) match
            case Head.Bad => (MExpr.Err, MType.Err)
            case Head.ObjVar(_) => (MExpr.Err, MType.Err)
            case Head.TypeLike(s) => (QuoteType(elabOType(t, sc, TVars.NoTVars)), TypeU)
            case Head.Obj(s) =>
              if args.isEmpty then
                if s.tparams.nonEmpty && s.kind != SymKind.Ctor && s.kind != SymKind.Rel then
                  (Ref(s), RelT(relCols(s)))
                else (Ref(s), RelT(relCols(s)))
              else
                // constructor application at the meta level: object code
                val rc = RuleCtx(allowVars = false)
                val term = elabTerm(t, sc, rc)
                (QuoteTerm(term), Code(OType.Splice(FactTypeOf(Ref(s)))))
            case Head.Meta(m, mt) =>
              if args.isEmpty then (m, mt) else elabApp(m, mt, args, sc, null, t.span, head)
    case RecordLit(fields, rest) =>
      if rest then err("E0001", "`..` is only allowed in named patterns", t.span)
      val seen = mutable.HashSet.empty[String]
      val fs = fields.flatMap { f =>
        if !seen.add(f.label.name) then
          err("E0307", s"duplicate field `${f.label.name}`", f.label.span); None
        else
          val (m, mt) = inferM(f.value, sc)
          val fsym = Sym(f.label.name, SymKind.MetaParam, f.label.span, sc)
          fsym.mtype = mt
          Some((f.label.name, m, fsym, mt))
      }
      (Rec(fs.map(f => (f._1, f._2))), Sig(fs.map(f => (f._3, f._4)), Nil))
    case mb: ModuleBody =>
      val bsc = Scope(Some(sc), "module body")
      ctx.unit.scopes.put(mb, bsc)
      Namer.enter(mb.items, bsc)
      elabBody(mb.items, bsc, mb.span)
    case Lambda(p, Some(pt), body) =>
      val psc = Scope(Some(sc), "lambda")
      val coll = mutable.ListBuffer.empty[Sym]
      val dom = elabMType(pt, psc, TVars.MetaImplicit(psc, coll))
      val ps = Sym(paramName(p), SymKind.MetaParam, p.span, psc)
      ps.mtype = dom
      ps.state = Sym.State.Done
      psc.enter(ps)
      val (mb, cod) = inferM(body, psc)
      val lam = Lam(ps, mb)
      val pi = Pi(ps, dom, cod, isImplicit = false)
      coll.foldRight((lam: MExpr, pi: MType))((a, acc) => (Lam(a, acc._1), Pi(a, TypeU, acc._2, isImplicit = true)))
    case Lambda(p, None, _) =>
      ctx.report(Diagnostic.error("E0206", s"cannot infer the type of lambda parameter `${paramName(p)}`", p.span, "type needed")
        .withHelp(s"annotate it, `[${paramName(p)} : T] ...`, or declare the type of the definition"))
      (MExpr.Err, MType.Err)
    case _: RecordType | _: Keyword | _: Arrow =>
      val mt = elabMType(t, sc, TVars.NoTVars)
      (SigV(mt), ModU)
    case _: Trees.Union => (QuoteType(elabOType(t, sc, TVars.NoTVars)), TypeU)
    case _: Conj | _: Disj | _: Trees.Not | Infix(_, _, _) =>
      val rc = RuleCtx(allowVars = true)
      (QuoteFormula(elabFormula(t, sc, rc)), PropT)
    case ErrorTree() => (MExpr.Err, MType.Err)
    case other =>
      err("E0202", "expected a meta expression", other.span, "this is object-level syntax")
      (MExpr.Err, MType.Err)

  private def paramName(p: Tree): String = p match
    case Ident(n) => n
    case VarRef(n) => n
    case _ => "_"

  private def inferSelect(sel: Select, sc: Scope): (MExpr, MType) =
    val (mq, tq) = inferM(sel.qual, sc)
    tq match
      case MType.Err => (MExpr.Err, MType.Err)
      case Sig(fields, _) =>
        fields.find(_._1.name == sel.name) match
          case Some((f, ft)) =>
            if f.kind == SymKind.TypeDef && f.typeDefRhs.isDefined then (QuoteType(f.typeDefRhs.get), TypeU)
            else
              val self = fields.map((g, _) => g -> Proj(mq, g.name)).toMap
              (Proj(mq, sel.name), substMT(ft, self))
          case None =>
            var d = Diagnostic.error("E0101", s"`${Printer.show(sel.qual)}` has no member `${sel.name}`", sel.nameSpan, "unknown member")
              .withNote(s"available members: ${fields.map(_._1.name).mkString(", ")}")
            val sugg = fields.map(_._1.name).filter(n => editDistance(n, sel.name) <= (sel.name.length / 3).max(1))
            sugg.headOption.foreach(s => d = d.withHelp(s"did you mean `$s`?"))
            ctx.report(d)
            (MExpr.Err, MType.Err)
      case other =>
        ctx.report(Diagnostic.error(
          "E0107",
          s"`${Printer.show(sel.qual)}` is not a module",
          sel.qual.span,
          s"has meta type `${showMT(other)}`"
        )
          .withNote("a path `m.x` requires `m` to be module-valued"))
        (MExpr.Err, MType.Err)

  // ---------------------------------------------------------------- application

  /** Elaborates `f a1 ... an` (rule M-App) with implicit type parameters inferred by first-order matching.
   *  `rc` is the enclosing rule context when the application occurs inside object code. */
  private def elabApp(fm: MExpr, ft: MType, args: List[Tree], sc: Scope, rc: RuleCtx | Null, span: Span, headTree: Tree): (MExpr, MType) =
    val solved = mutable.LinkedHashMap.empty[Sym, Option[OType]]
    val spine = mutable.ListBuffer.empty[Either[Sym, MExpr]]
    var cur = ft
    var ok = true
    def subst(t: MType): MType = substMT(t, solved.collect { case (k, Some(v)) => k -> QuoteType(v) }.toMap)
    def peel(): Unit =
      while cur match { case Pi(_, _, _, true) => true; case _ => false } do
        val Pi(x, _, cod, _) = cur: @unchecked
        val y = Sym(x.name, SymKind.MetaParam, x.span, x.owner)
        y.mtype = TypeU
        solved(y) = None
        spine += Left(y)
        cur = substMT(cod, Map(x -> Ref(y)))
    for a <- args if ok do
      peel()
      cur match
        case Pi(x, dom, cod, false) =>
          val domS = subst(dom)
          val unsolvedIn = solved.exists((k, v) => v.isEmpty && mentions(domS, k))
          val am: MExpr =
            if unsolvedIn then
              domS match
                case Code(_) if rc != null && !isMetaCode(a, sc) =>
                  quoteArg(a, sc, rc)
                case _ =>
                  val (am0, at) = argInfer(a, sc, rc)
                  matchM(domS, at, solved)
                  val domS2 = subst(domS)
                  subsumes(at, domS2).foreach(r => mismatch(domS2, at, a.span, r))
                  am0
            else
              domS match
                case Code(_) if rc != null => quoteArg(a, sc, rc)
                case _ if rc != null && objectVar(a, sc).isDefined =>
                  val v = objectVar(a, sc).get
                  ctx.report(Diagnostic.error("E0201", "runtime value used at compile time", v.span, s"object variable `${v.name}`")
                    .withNote(
                      s"this argument of `${Printer.show(headTree)}` has meta type `${showMT(domS)}` and must be known at compile time"
                    ))
                  rc.failed = true
                  MExpr.Err
                case _ => checkM(a, domS, sc, rc)
          spine += Right(am)
          cur = substMT(cod, Map(x -> am))
        case MType.Err => ok = false
        case other =>
          ctx.report(Diagnostic.error("E0207", s"too many arguments for `${Printer.show(headTree)}`", a.span, "unexpected argument")
            .withNote(s"`${Printer.show(headTree)}` has meta type `${showMT(ft)}`"))
          ok = false
    if !ok then return (MExpr.Err, MType.Err)
    val unsolved = solved.collect { case (k, None) => k }
    for u <- unsolved if mentions(cur, u) do
      ctx.report(Diagnostic.error("E0206", s"cannot infer implicit type parameter `${u.name}` of `${Printer.show(headTree)}`", span)
        .withNote("implicit parameters are inferred by first-order matching of the argument types"))
    val sol = solved.map((k, v) => k -> QuoteType(v.getOrElse(OType.Err))).toMap
    val result = spine.foldLeft(fm) {
      case (acc, Left(y)) => App(acc, sol(y), span)
      case (acc, Right(a)) => App(acc, a, span)
    }
    (result, substMT(cur, sol))

  /** The first object variable (an uppercase name that is not a captured meta variable) in a tree. */
  private def objectVar(t: Tree, sc: Scope): Option[VarRef] = t match
    case v @ VarRef(n) => if sc.lookup(n).exists(s => s.mtype != null && capturesVar(s)) then None else Some(v)
    case Apply(f, a) => objectVar(f, sc).orElse(objectVar(a, sc))
    case Select(q, _) => objectVar(q, sc)
    case Infix(_, l, r) => objectVar(l, sc).orElse(objectVar(r, sc))
    case Parens(i) => objectVar(i, sc)
    case Trees.Neg(x) => objectVar(x, sc)
    case _ => None

  private def isMetaCode(t: Tree, sc: Scope): Boolean = t match
    case VarRef(n) => sc.lookup(n).exists(s => s.mtype match { case Code(_) => true; case _ => false })
    case Parens(i) => isMetaCode(i, sc)
    case _ => false

  /** An object term passed where a meta argument of type ⇑τ is expected is quoted (Section 3.2, rule 4). */
  private def quoteArg(a: Tree, sc: Scope, rc: RuleCtx): MExpr =
    elabTerm(a, sc, rc) match
      case obj.Term.Splice(m @ Ref(s)) if s.mtype match { case Code(_) => true; case _ => false } => m
      case t => QuoteTerm(t)

  private def argInfer(a: Tree, sc: Scope, rc: RuleCtx | Null): (MExpr, MType) =
    a match
      case VarRef(n) if rc != null && !sc.lookup(n).exists(capturesVar) =>
        err("E0201", s"runtime value used at compile time", a.span, s"object variable `$n` cannot be a meta argument here")
        (MExpr.Err, MType.Err)
      case _ => inferM(a, sc)

  private def mentions(t: MType, s: Sym): Boolean =
    def m(e: MExpr): Boolean = e match
      case Ref(x) => x eq s
      case Proj(x, _) => m(x)
      case FactTypeOf(x) => m(x)
      case TApp(f, as) => m(f) || as.exists(o)
      case QuoteType(x) => o(x)
      case Rec(fs) => fs.exists(f => m(f._2))
      case _ => false
    def o(x: OType): Boolean = OType.exists(x) { case OType.Splice(e) => m(e); case _ => false }
    t match
      case Code(x) => o(x)
      case RelT(cols) => cols.exists(c => o(c.tpe))
      case Pi(_, d, c, _) => mentions(d, s) || mentions(c, s)
      case Sig(fs, _) => fs.exists(f => mentions(f._2, s))
      case _ => false

  /** First-order matching of a pattern meta type (with unsolved implicit parameters) against an actual one. */
  private def matchM(p: MType, a: MType, solved: mutable.LinkedHashMap[Sym, Option[OType]]): Unit = (p, a) match
    case (Code(x), Code(y)) => matchO(x, y, solved)
    case (RelT(xs), RelT(ys)) if xs.length == ys.length => xs.zip(ys).foreach((x, y) => matchO(x.tpe, y.tpe, solved))
    case (Pi(_, d1, c1, _), Pi(_, d2, c2, _)) => matchM(d1, d2, solved); matchM(c1, c2, solved)
    case (Sig(f1, _), Sig(f2, _)) =>
      for (g, gt) <- f1; (h, ht) <- f2.find(_._1.name == g.name) do matchM(gt, ht, solved)
    case _ =>

  private def matchO(p: OType, a: OType, solved: mutable.LinkedHashMap[Sym, Option[OType]]): Unit =
    (normO(p), normO(a)) match
      case (OType.Splice(Ref(x)), y) if solved.get(x).contains(None) => solved(x) = Some(y)
      case (OType.Splice(TApp(f, xs)), OType.Splice(TApp(g, ys))) if xs.length == ys.length =>
        xs.zip(ys).foreach((x, y) => matchO(x, y, solved))
      case (OType.Splice(FactTypeOf(TApp(f, xs))), OType.Splice(FactTypeOf(TApp(g, ys)))) if xs.length == ys.length =>
        xs.zip(ys).foreach((x, y) => matchO(x, y, solved))
      case _ =>

  // ---------------------------------------------------------------- checking

  def checkM(t: Tree, expected: MType, sc: Scope, rc: RuleCtx | Null = null): MExpr = (t, expected) match
    case (_, MType.Err) => inferM(t, sc)._1
    case (Parens(i), _) => checkM(i, expected, sc, rc)
    case (Lambda(p, None, body), Pi(x, dom, cod, false)) =>
      val psc = Scope(Some(sc), "lambda")
      val ps = Sym(paramName(p), SymKind.MetaParam, p.span, psc)
      ps.mtype = dom
      ps.state = Sym.State.Done
      psc.enter(ps)
      Lam(ps, checkM(body, substMT(cod, Map(x -> Ref(ps))), psc, rc))
    case (_, Pi(x, TypeU, cod, true)) =>
      val psc = Scope(Some(sc), "implicit parameters")
      val ps = Sym(x.name, SymKind.MetaParam, x.span, psc)
      ps.mtype = TypeU
      ps.state = Sym.State.Done
      psc.enter(ps)
      Lam(ps, checkM(t, substMT(cod, Map(x -> Ref(ps))), psc, rc))
    case (_, PropT) if !isMetaOfType(t, sc, PropT) =>
      val rc2 = if rc != null then rc else RuleCtx(allowVars = true)
      QuoteFormula(elabFormula(t, sc, rc2))
    case (_, Code(_)) if !isMetaCode(t, sc) =>
      val rc2 = if rc != null then rc else RuleCtx(allowVars = false)
      quoteArg(t, sc, rc2)
    case (_, TypeU) => QuoteType(elabOType(t, sc, TVars.NoTVars))
    case (RecordLit(fields, false), Sig(sfields, _)) =>
      val done = mutable.LinkedHashMap.empty[String, MExpr]
      var s = Map.empty[Sym, MExpr]
      for (f, ft) <- sfields do
        fields.find(_.label.name == f.name) match
          case None =>
            ctx.report(Diagnostic.error("E0204", s"signature mismatch: missing field `${f.name}`", t.span, s"field `${f.name}` is required")
              .withNote(s"expected signature `${showMT(expected)}`"))
          case Some(fld) =>
            val m = checkM(fld.value, substMT(ft, s), sc, rc)
            done(f.name) = m
            s += f -> m
      for fld <- fields if !done.contains(fld.label.name) do
        if done.keySet.contains(fld.label.name) then ()
        else
          done(fld.label.name) = inferM(fld.value, sc)._1
      Rec(done.toList)
    case _ =>
      val (m, mt) = inferM(t, sc)
      subsumes(mt, expected).foreach { r =>
        if expected.isInstanceOf[Sig] || mt.isInstanceOf[Sig] then
          var d = Diagnostic.error("E0204", "signature mismatch", t.span, s"expected `${showMT(expected)}`")
            .withNote(s"found `${showMT(mt)}`")
          if !r.startsWith("expected") then d = d.withNote(r)
          ctx.report(d)
        else mismatch(expected, mt, t.span, r)
      }
      m

  private def isMetaOfType(t: Tree, sc: Scope, mt: MType): Boolean = t match
    case Parens(i) => isMetaOfType(i, sc, mt)
    case Ident(n) => sc.lookup(n).exists(s => (s.kind == SymKind.MetaDef || s.kind == SymKind.MetaParam) && s.mtype == mt)
    case VarRef(n) => sc.lookup(n).exists(s => s.kind == SymKind.MetaParam && s.mtype == mt)
    case _ => false

  // ======================================================================= object code

  private def isPrimMeta(m: MExpr): Option[BaseType] = m match
    case Ref(s) => s.mtype match { case Prim(b) => Some(b); case _ => None }
    case MExpr.Lit(l) => Some(BaseType.of(l))
    case Op(_, l, _, _) => isPrimMeta(l)
    case MExpr.Neg(x, _) => isPrimMeta(x)
    case _ => None

  private def stage1(t: obj.Term): Option[MExpr] = t match
    case obj.Term.Splice(m) if isPrimMeta(m).isDefined => Some(m)
    case obj.Term.Lit(l) => Some(MExpr.Lit(l))
    case _ => None

  def elabTerm(t: Tree, sc: Scope, rc: RuleCtx): obj.Term = t match
    case Parens(i) => elabTerm(i, sc, rc)
    case Wildcard() => obj.Term.Var(rc.freshWild())(t.span)
    case Trees.Lit(l) => obj.Term.Lit(l)(t.span)
    case VarRef(n) =>
      sc.lookup(n) match
        case Some(s) if (s.kind == SymKind.MetaParam || s.kind == SymKind.MetaDef) && s.mtype != null && capturesVar(s) =>
          s.used = true
          s.mtype match
            case Code(_) | Prim(_) => obj.Term.Splice(Ref(s))(t.span)
            case other =>
              err("E0202", s"meta variable `$n` cannot be used as a term", t.span, s"has meta type `${showMT(other)}`")
              obj.Term.Var(n)(t.span)
        case _ =>
          if !rc.allowVars then
            ctx.report(Diagnostic.error("E0201", "runtime value used at compile time", t.span, s"object variable `$n`")
              .withNote("object variables only exist inside rules, queries and formula functions"))
          obj.Term.Var(n)(t.span)
    case Trees.Neg(x) =>
      val e = elabTerm(x, sc, rc)
      e match
        case obj.Term.Splice(m) if isPrimMeta(m).isDefined => obj.Term.Splice(MExpr.Neg(m, t.span))(t.span)
        case _ => obj.Term.Neg(e)(t.span)
    case inf @ Infix(op, l, r) if ArithOp.fromString(op).isDefined =>
      val el = elabTerm(l, sc, rc)
      val er = elabTerm(r, sc, rc)
      val aop = ArithOp.fromString(op).get
      (stage1(el), stage1(er)) match
        case (Some(ml), Some(mr)) if !(el.isInstanceOf[obj.Term.Lit] && er.isInstanceOf[obj.Term.Lit]) =>
          // all operands are compile-time primitives: evaluated at stage 1 (Section 3.2, rule 3)
          val (bl, br) = (isPrimMeta(ml).get, isPrimMeta(mr).get)
          if bl != br || (aop == ArithOp.Concat) != (bl == BaseType.StringT) then
            err("E0203", s"operator `$op` cannot be applied to `${bl.show}` and `${br.show}`", inf.opSpan)
          obj.Term.Splice(Op(aop, ml, mr, t.span))(t.span)
        case _ => obj.Term.Arith(aop, el, er)(t.span)
    case Infix(op, _, _) =>
      err("E0202", s"`$op` is a formula, not a term", t.span, "expected a term")
      obj.Term.Var(rc.freshWild())(t.span)
    case As(x, v) =>
      checkNotMeta(v, sc)
      obj.Term.As(elabTerm(x, sc, rc), v.name)(t.span)
    case Ascribe(x, tp) => obj.Term.Ascr(elabTerm(x, sc, rc), elabOType(tp, sc, TVars.NoTVars))(t.span)
    case With(v, fields) =>
      val vt = elabTerm(v, sc, rc)
      checkLabelsDistinct(fields.map(_.label))
      obj.Term.With(vt, fields.map(f => (f.label.name, elabTerm(f.value, sc, rc), f.label.span)))(t.span)
    case Select(q @ VarRef(n), l) if !sc.lookup(n).exists(s => s.mtype != null && capturesVar(s)) =>
      obj.Term.Proj(elabTerm(q, sc, rc), l)(t.span)
    case Select(q @ VarRef(n), l) if sc.lookup(n).exists(s => s.mtype match { case Code(_) => true; case _ => false }) =>
      obj.Term.Proj(elabTerm(q, sc, rc), l)(t.span)
    case _: Ident | _: Apply | _: Select =>
      val (head, args) = flattenApp(t)
      classify(head, sc, rc) match
        case Head.Obj(s) =>
          obj.Term.App(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = false, s.span))(t.span)
        case Head.Meta(m, RelT(cols)) =>
          obj.Term.App(RelRef.Spliced(m), elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = false, Span.NoSpan))(t.span)
        case Head.Meta(m, mt @ (Code(_) | Prim(_))) =>
          if args.nonEmpty then
            err("E0207", s"`${Printer.show(head)}` is not a function", args.head.span, s"has meta type `${showMT(mt)}`")
          obj.Term.Splice(m)(t.span)
        case Head.Meta(m, pi: Pi) =>
          val (am, at) = elabApp(m, pi, args, sc, rc, t.span, head)
          at match
            case Code(_) | Prim(_) | MType.Err => obj.Term.Splice(am)(t.span)
            case PropT =>
              err("E0202", s"formula function `${Printer.show(head)}` used as a term", t.span, "this is a formula")
              obj.Term.Var(rc.freshWild())(t.span)
            case other =>
              err("E0202", "expected a term", t.span, s"this has meta type `${showMT(other)}`")
              obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, MType.Err) => obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, PropT) =>
          err("E0202", s"formula `${Printer.show(head)}` used as a term", t.span)
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, other) =>
          ctx.report(Diagnostic.error("E0202", "expected a term", head.span, s"this has meta type `${showMT(other)}`")
            .withNote("only code (⇑τ), compile-time primitives and relations' facts can be used as terms"))
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.ObjVar(n) =>
          if args.nonEmpty then err("E0207", s"variable `$n` cannot be applied to arguments", t.span)
          obj.Term.Var(n)(t.span)
        case Head.TypeLike(s) =>
          err("E0202", s"type `${s.name}` used as a term", head.span, "expected a term")
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.Bad => obj.Term.Var(rc.freshWild())(t.span)
    case _: RecordLit =>
      err("E0202", "a record can only follow a relation (named pattern)", t.span)
      obj.Term.Var(rc.freshWild())(t.span)
    case ErrorTree() => obj.Term.Var(rc.freshWild())(t.span)
    case other =>
      err("E0202", "expected a term", other.span)
      obj.Term.Var(rc.freshWild())(t.span)

  private def checkNotMeta(v: VarRef, sc: Scope): Unit = ()

  private def checkLabelsDistinct(ls: List[Ident]): Unit =
    val seen = mutable.HashMap.empty[String, Span]
    for l <- ls do
      seen.get(l.name) match
        case Some(p) =>
          ctx.report(Diagnostic.error("E0307", s"duplicate label `${l.name}`", l.span, "duplicate").withLabel(p, "first used here"))
        case None => seen(l.name) = l.span

  /** Arguments of a relation atom / constructor term; named patterns are replaced by positional ones (Section 2.4). */
  private def elabArgs(
      rel: String,
      cols: List[Column],
      args: List[Tree],
      sc: Scope,
      rc: RuleCtx,
      span: Span,
      isHead: Boolean,
      declSpan: Span
  ): List[obj.Term] =
    args match
      case List(rl @ RecordLit(fields, rest)) if !(cols.length == 1 && cols.head.label.isEmpty) =>
        if rest && isHead then
          rc.failed = true
          ctx.report(Diagnostic.error("E0302", "`..` is not allowed in a rule head", rl.span, "rest pattern in head")
            .withNote("the omitted columns of a derived fact would be unknown"))
        checkLabelsDistinct(fields.map(_.label))
        val byLabel = fields.map(f => f.label.name -> f).toMap
        for f <- fields if !cols.exists(_.label.contains(f.label.name)) do
          rc.failed = true
          var d = Diagnostic.error("E0306", s"`$rel` has no column labelled `${f.label.name}`", f.label.span, "unknown label")
          val labels = cols.flatMap(_.label)
          if labels.isEmpty then d = d.withNote(s"the columns of `$rel` are not labelled")
          else d = d.withNote(s"labels of `$rel`: ${labels.mkString(", ")}")
          if declSpan.exists then d = d.withLabel(declSpan, "declared here")
          ctx.report(d)
        val missing = cols.flatMap(_.label).filterNot(byLabel.contains)
        if missing.nonEmpty && !rest && cols.forall(_.label.isDefined) then
          rc.failed = true
          ctx.report(Diagnostic.error(
            "E0301",
            s"missing label${if missing.length > 1 then "s" else ""} in named pattern for `$rel`",
            rl.span,
            s"missing ${missing.map(l => s"`$l`").mkString(", ")}"
          )
            .withHelp(if isHead then s"add ${missing.map(l => s"`$l = ...`").mkString(", ")}"
            else "add the missing labels, or end the pattern with `..` to ignore them"))
        if cols.exists(_.label.isEmpty) then
          rc.failed = true
          err("E0306", s"`$rel` does not label all of its columns, so it cannot be used with a named pattern", rl.span)
        cols.map { c =>
          c.label.flatMap(byLabel.get) match
            case Some(f) => elabTerm(f.value, sc, rc)
            case None => obj.Term.Var(rc.freshWild())(rl.span)
        }
      case _ =>
        if args.length != cols.length then
          rc.failed = true
          var d = Diagnostic.error(
            "E0207",
            s"`$rel` expects ${cols.length} argument${if cols.length == 1 then "" else "s"}, found ${args.length}",
            span,
            s"${args.length} argument${if args.length == 1 then "" else "s"} given"
          )
          if declSpan.exists then d = d.withLabel(declSpan, "declared here")
          ctx.report(d)
        args.map(elabTerm(_, sc, rc))

  def elabFormula(t: Tree, sc: Scope, rc: RuleCtx): List[obj.Formula] = t match
    case Parens(i) => elabFormula(i, sc, rc)
    case Conj(l, r) => elabFormula(l, sc, rc) ++ elabFormula(r, sc, rc)
    case Disj(_, _) =>
      def alts(t: Tree): List[Tree] = t match
        case Disj(l, r) => alts(l) ++ alts(r)
        case Parens(i @ Disj(_, _)) => alts(i)
        case other => List(other)
      List(obj.Formula.Disj(alts(t).map(elabFormula(_, sc, rc)))(t.span))
    case Trees.Not(x) =>
      elabFormula(x, sc, rc) match
        case List(a: obj.Formula.Atom) =>
          checkCompleteParam(a.rel, a.span, "negates")
          List(obj.Formula.Not(a)(t.span))
        case List(_: obj.Formula.Splice) =>
          ctx.report(Diagnostic.error("E0202", "`not` applies only to relation atoms", x.span, "this is a formula function use")
            .withNote("formula functions may expand to arbitrary formulas; declare a relation for the negated condition"))
          Nil
        case Nil => Nil
        case _ =>
          err("E0202", "`not` applies only to relation atoms", x.span, "not a relation atom")
          Nil
    case Infix("=", VarRef(v), agg @ Agg(kind, term, body)) =>
      val res = VarRef(v)(t.span)
      rc.aggDepth += 1
      val b =
        try elabFormula(body, sc, rc)
        finally rc.aggDepth -= 1
      for case a: obj.Formula.Atom <- b do checkCompleteParam(a.rel, a.span, "aggregates over")
      List(obj.Formula.Agg(v, kind, elabTerm(term, sc, rc), b)(t.span))
    case Infix(op, l, r) if CmpOp.fromString(op).isDefined =>
      if r.isInstanceOf[Agg] || l.isInstanceOf[Agg] then
        err("E0202", "an aggregate must be bound to a variable, `X = count { ... }`", t.span)
        Nil
      else List(obj.Formula.Cmp(CmpOp.fromString(op).get, elabTerm(l, sc, rc), elabTerm(r, sc, rc))(t.span))
    case As(inner, v) =>
      elabFormula(inner, sc, rc) match
        case List(a: obj.Formula.Atom) if a.as.isEmpty => List(obj.Formula.Atom(a.rel, a.args, Some(v.name))(t.span))
        case _ =>
          err("E0202", "`as` in a body applies to a relation atom", t.span)
          Nil
    case _: Ident | _: Apply | _: Select | _: VarRef =>
      val (head, args) = flattenApp(t)
      classify(head, sc, rc) match
        case Head.Obj(s) =>
          List(obj.Formula.Atom(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = false, s.span), None)(
            t.span
          ))
        case Head.Meta(m, RelT(cols)) =>
          List(obj.Formula.Atom(
            RelRef.Spliced(m),
            elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = false, Span.NoSpan),
            None
          )(t.span))
        case Head.Meta(m, PropT) =>
          if args.nonEmpty then err("E0207", s"`${Printer.show(head)}` is a formula, not a function", args.head.span)
          List(obj.Formula.Splice(m)(t.span))
        case Head.Meta(m, pi: Pi) =>
          val (am, at) = elabApp(m, pi, args, sc, rc, t.span, head)
          at match
            case PropT =>
              val bodySpan = head match
                case Ident(n) => sc.lookup(n).flatMap(_.decl).map(_.span).getOrElse(Span.NoSpan)
                case _ => Span.NoSpan
              rc.expansions += Expansion(Printer.show(head), t.span, bodySpan)
              List(obj.Formula.Splice(am)(t.span))
            case MType.Err => Nil
            case Pi(_, _, _, _) =>
              ctx.report(Diagnostic.error(
                "E0207",
                s"formula function `${Printer.show(head)}` is not fully applied",
                t.span,
                "missing arguments"
              )
                .withNote(s"`${Printer.show(head)}` has meta type `${showMT(pi)}`"))
              Nil
            case other =>
              err("E0202", "expected a formula", t.span, s"this has meta type `${showMT(other)}`")
              Nil
        case Head.Meta(_, MType.Err) | Head.Bad => Nil
        case Head.Meta(_, other) =>
          ctx.report(Diagnostic.error("E0202", "expected a formula", head.span, s"this has meta type `${showMT(other)}`")
            .withNote("a formula is a relation atom, a comparison, an aggregate or a formula function use"))
          Nil
        case Head.ObjVar(n) =>
          err("E0202", "expected a formula", t.span, s"variable `$n` is not a formula")
          Nil
        case Head.TypeLike(s) =>
          ctx.report(Diagnostic.error("E0202", "expected a formula", head.span, s"`${s.name}` is a type, not a relation")
            .withHelp(s"to test membership in a type, write an ascription `(X : ${s.name})` inside an atom"))
          Nil
    case ErrorTree() => Nil
    case other =>
      err("E0202", "expected a formula", other.span, "not a formula")
      Nil

  /** A functor that negates or aggregates over a relation parameter must require %complete (Section 11). */
  private def checkCompleteParam(r: RelRef, span: Span, what: String): Unit = r match
    case RelRef.Spliced(Proj(Ref(p), l)) if p.kind == SymKind.MetaParam =>
      p.mtype match
        case Sig(_, reqs) if !reqs.exists { case Req.Complete(`l`, _) => true; case _ => false } =>
          ctx.report(Diagnostic.error(
            "E0210",
            s"the functor $what the relation parameter `${p.name}.$l` without requiring `%complete $l`",
            span,
            s"`${p.name}.$l` may be bound to an incomplete relation"
          )
            .withLabel(p.span, s"parameter `${p.name}` declared here")
            .withHelp(s"add `%complete $l` to the signature of `${p.name}`"))
        case _ =>
    case RelRef.Spliced(Ref(p)) if p.kind == SymKind.MetaParam =>
      // a relation parameter `(r : A -> rel)` cannot carry requirements
      ctx.report(Diagnostic.error(
        "E0210",
        s"the function $what the relation parameter `${p.name}`",
        span,
        s"`${p.name}` may be bound to an incomplete relation"
      )
        .withLabel(p.span, s"parameter `${p.name}` declared here")
        .withHelp("pass the relation in a signature with `%complete`, e.g. `(m : { r : A -> rel, %complete r })`"))
    case _ =>

  def elabHead(t: Tree, sc: Scope, rc: RuleCtx): Option[obj.Term] =
    val (head, args) = flattenApp(t)
    classify(head, sc, rc) match
      case Head.Obj(s) =>
        Some(obj.Term.App(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = true, s.span))(t.span))
      case Head.Meta(m, RelT(cols)) =>
        Some(obj.Term.App(RelRef.Spliced(m), elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = true, Span.NoSpan))(t.span))
      case Head.Bad | Head.Meta(_, MType.Err) => None
      case Head.Meta(_, PropT) | Head.Meta(_, _: Pi) =>
        ctx.report(Diagnostic.error("E0103", "the head of a rule must be a relation", head.span, "formula function")
          .withNote("clauses of a formula function must be in the same scope as its declaration"))
        None
      case _ =>
        ctx.report(Diagnostic.error("E0103", "the head of a rule must be a relation atom", t.span, "not a relation atom")
          .withNote("rules have the form `c t1 ... tn :- body.` where `c` is a relation"))
        None

  // ======================================================================= items and bodies

  private def elabRule(r: Rule, sc: Scope): Option[obj.Rule] =
    val rc = RuleCtx(allowVars = true)
    val heads = r.heads.flatMap(elabHead(_, sc, rc))
    val body = r.body.map(elabFormula(_, sc, rc)).getOrElse(Nil)
    if heads.length != r.heads.length || rc.failed then None
    else Some(obj.Rule(r.name.map(_.name), heads, body)(r.span, Origin.Source, rc.expansions.toList))

  private def relTarget(t: Tree, sc: Scope, what: String): Option[RelRef] =
    classify(t, sc, null) match
      case Head.Obj(s) => Some(RelRef.Spliced(Ref(s)))
      case Head.Meta(m, RelT(_)) => Some(RelRef.Spliced(m))
      case Head.Bad | Head.Meta(_, MType.Err) => None
      case _ =>
        err("E0701", s"$what expects a relation", t.span, "not a relation")
        None

  private def elabDirective(d: Directive, sc: Scope): Option[obj.Directive] =
    def mk(k: DirKind, tgt: Tree) =
      relTarget(tgt, sc, s"`%${d.kind}`").map(r => obj.Directive(k, Some(r), None)(d.span, Origin.Source))
    d.args match
      case DirArgs.Mode(tgt, ms) =>
        // modes of formula functions are recorded on the symbol
        tgt match
          case Ident(n) if sc.lookup(n).exists(_.kind == SymKind.FormulaFn) =>
            val f = sc.lookup(n).get
            f.fnModes = f.fnModes :+ ((ms.map(_.input), d.span))
            None
          case _ => mk(DirKind.ModeD(ModeSpec(ms.map(m => (m.input, m.label.map(_.name), m.span)))), tgt)
      case DirArgs.TerminatesVar(v, tgt, args) =>
        val rc = RuleCtx(allowVars = true)
        mk(DirKind.TerminatesVar(v.name, args.map(elabTerm(_, sc, rc))), tgt)
      case DirArgs.TerminatesLabel(l, tgt) => mk(DirKind.TerminatesLabel(l.name), tgt)
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
  private def elabMetaDef(s: Sym): Option[MExpr] =
    s.state = Sym.State.InProgress
    val sc = s.owner
    val result: Option[MExpr] = s.decl.get match
      case d @ Decl(name, params, tpe, _, defn, _) =>
        tpe match
          case Keyword(Kw.Mod) =>
            val sig = elabMType(defn.get, sc, TVars.NoTVars)
            s.sigValue = Some(sig)
            s.mtype = ModU
            s.static = Some(SigV(sig))
            Some(SigV(sig))
          case _ =>
            val psc = Scope(Some(sc), s"parameters of ${name.name}")
            val coll = mutable.ListBuffer.empty[Sym]
            val tv = TVars.MetaImplicit(psc, coll)
            val ps = elabParams(params, psc, tv)
            val resT = elabMType(tpe, psc, tv)
            // implicit parameters from the declared type are bound outermost
            val explicitT = ps.foldRight(resT)((p, acc) => Pi(p, p.mtype.nn, acc, isImplicit = false))
            val fullT = coll.foldRight(explicitT)((a, acc) => Pi(a, TypeU, acc, isImplicit = true))
            s.mtype = fullT
            if s.kind == SymKind.FormulaFn then
              s.arity = arity(resT)
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
                  ctx.report(Diagnostic.warning("W0003", s"formula function `${name.name}` has no clauses", name.span, "always false"))
                Some(coll.foldRight(elabClauses(s, resT, psc))((a, acc) => Lam(a, acc)))
              case None => None
      case Def(name, params, rhs) =>
        val psc = Scope(Some(sc), s"parameters of ${name.name}")
        val coll = mutable.ListBuffer.empty[Sym]
        val ps = elabParams(params, psc, TVars.MetaImplicit(psc, coll))
        val (body, bt) = inferM(rhs, psc)
        val explicitT = ps.foldRight(bt)((p, acc) => Pi(p, p.mtype.nn, acc, isImplicit = false))
        s.mtype = coll.foldRight(explicitT)((a, acc) => Pi(a, TypeU, acc, isImplicit = true))
        if bt == ModU && ps.isEmpty then
          body match
            case SigV(sig) => s.sigValue = Some(sig)
            case _ =>
        Some(coll.foldRight(ps.foldRight(body)((p, acc) => Lam(p, acc)))((a, acc) => Lam(a, acc)))
      case _ => None
    result.foreach(r => if isStatic(r) then s.static = Some(r))
    if s.mtype == null then s.mtype = MType.Err
    s.state = Sym.State.Done
    result

  private def arity(t: MType): Int = t match
    case Pi(_, _, c, false) => 1 + arity(c)
    case Pi(_, _, c, true) => arity(c)
    case _ => 0

  private def endsInProp(t: MType): Boolean = t match
    case Pi(_, _, c, _) => endsInProp(c)
    case PropT => true
    case _ => false

  private def elabParams(params: List[Param], psc: Scope, tv: TVars): List[Sym] =
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
          val p = Sym(nm, SymKind.MetaParam, n.span, psc)
          p.mtype = mt
          p.state = Sym.State.Done
          psc.enter(p)
          Some(p)
      case Param.VarParam(v) =>
        ctx.report(Diagnostic.error("E0206", s"cannot infer the type of parameter `${v.name}`", v.span, "type needed")
          .withHelp(s"write `(${v.name} : T)` or declare the type of the definition"))
        None
    }

  /** Clauses `f t̄j :- ψj` define `f = [X̄] ⟨(X̄ = t̄1, ψ1) ; ... ; (X̄ = t̄k, ψk)⟩` (Section 4.8). */
  private def elabClauses(s: Sym, t: MType, sc: Scope): MExpr =
    val params = mutable.ListBuffer.empty[Sym]
    var cur = t
    val csc = Scope(Some(sc), s"clauses of ${s.name}")
    while cur.isInstanceOf[Pi] do
      val Pi(x, d, c, _) = cur: @unchecked
      val p = Sym(s"${s.name}#${params.length + 1}", SymKind.MetaParam, s.span, csc)
      p.mtype = d
      p.state = Sym.State.Done
      params += p
      cur = substMT(c, Map(x -> Ref(p)))
    val alts = s.clauses.toList.flatMap { cl =>
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

  /** Elaborates a module body (rule M-Body); returns the body and its signature of exports. */
  def elabBody(items: List[Item], sc: Scope, span: Span): (MExpr, MType) =
    val out = mutable.ListBuffer.empty[EItem]
    for (item, k) <- items.zipWithIndex do
      sc.processed = k
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
        case _: ErrorItem =>
    // exports
    val fields = sc.decls.values.toList.flatMap { s =>
      s.kind match
        case SymKind.ObjType if s.tparams.isEmpty => Some(s -> TypeU)
        case SymKind.Struct | SymKind.Rel | SymKind.Ctor if s.tparams.isEmpty && s.mtype != null => Some(s -> s.mtype.nn)
        case SymKind.TypeDef if s.typeDefParams.isEmpty && s.typeDefRhs.isDefined => Some(s -> TypeU)
        case SymKind.MetaDef | SymKind.FormulaFn if s.mtype != null && s.mtype != MType.Err => Some(s -> s.mtype.nn)
        case _ => None
    }
    (Body(out.toList, sc, span), Sig(fields, Nil))

/** Phase: stage inference and meta typing of the whole program. */
final class TyperPhase extends Phase:
  def phaseName = "typer"
  def description = "stage inference and meta typing; inserts quotes and splices"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null || u.rootScope == null then return
    val typer = Typer()
    val (body, _) = typer.elabBody(u.untpd.nn.items, u.rootScope.nn, u.untpd.nn.span)
    u.elab = body
    // unused meta definitions
    for s <- u.rootScope.nn.decls.values if (s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn) && !s.used && false do
      ctx.report(Diagnostic.warning("W0003", s"unused definition `${s.name}`", s.span))
  override def show(using Context): String = MetaPrinter.showBody(ctx.unit.elab.nn)
