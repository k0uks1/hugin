package hugin.meta
package typer

import hugin.syntax.TreeOps.flattenArrow
import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{OType, Column, TParam}
import hugin.obj
import scala.collection.mutable

/** Lazy elaboration of object declarations and type definitions (Sections 2.5, 4.7, 5.2). */
private[meta] trait Declarations extends TyperBase:
  self: Typer =>
  import MExpr.*
  import MType.*

  // ======================================================================= object declarations

  def info(s: Sym): DeclInfo =
    ensureDecl(s)
    syms.declInfo(s).getOrElse(DeclInfo(Nil, Nil, None, None))

  def relCols(s: Sym): List[Column] = info(s).cols

  /** Elaborates an object declaration (lazily: object declarations may be used before they occur). */
  def ensureDecl(s: Sym): Unit =
    if syms.state(s) == ElabState.Pending && s.kind.isObjectDecl then inItemOf(s)(elabDecl(s))

  private def elabDecl(s: Sym): Unit =
    syms(s).state = ElabState.InProgress
    val d = s.decl.get.asInstanceOf[Decl]
    val sc = s.owner
    val explicit = d.params.flatMap {
      case Param.VarParam(v) => Some(v.name -> TParam(v.name))
      case p =>
        err("E0004", "object declarations take only type parameters", p.span, "expected an uppercase type parameter")
        None
    }
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
    val (cols, result, typeKind): (List[Column], Option[OType], Option[TypeKindE]) = s.kind match
      case SymKind.ObjType =>
        val k = d.sup match
          case Some(sup) => TypeKindE.Refinement(elabOType(sup, sc, tv))
          case None => TypeKindE.Open
        syms(s).mtype = Some(TypeU)
        (Nil, None, Some(k))
      case SymKind.Struct =>
        val rt = d.defn.get.asInstanceOf[RecordType]
        val doms = rt.entries.flatMap {
          case SigEntry.FieldDecl(l, t, fact) =>
            if fact then err("E0004", "`%fact` is not allowed on the fields of a struct", l.span, "struct field")
            Some((Some(l), t))
          case SigEntry.Complete(_, sp) => err("E0004", "requirements are not allowed in struct declarations", sp); None
          case SigEntry.ModeReq(_, _, sp) => err("E0004", "requirements are not allowed in struct declarations", sp); None
        }
        val cols = columns(doms)
        // a data struct only builds values; a `%fact` struct is also the relation of its facts
        syms(s).mtype = Some(if s.fact then RelT(cols) else CtorT(cols, OType.Splice(FactTypeOf(Ref(s)))))
        (cols, None, None)
      case SymKind.Rel =>
        val (doms, _) = flattenArrow(d.tpe)
        val cols = columns(doms)
        syms(s).mtype = Some(RelT(cols))
        (cols, None, None)
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
        syms(s).mtype = Some(if s.fact then RelT(cols, Some(res)) else CtorT(cols, res))
        (cols, Some(res), None)
      case _ => (Nil, None, None)
    syms(s).declInfo = Some(DeclInfo(explicit.map(_._2) ++ implicits.values, cols, result, typeKind))
    syms(s).state = ElabState.Done

  private[meta] def isOpenType(t: OType): Boolean = normO(t) match
    case OType.Splice(Ref(s)) => s.kind == SymKind.ObjType && info(s).typeKind.contains(TypeKindE.Open)
    case OType.Splice(TApp(Ref(s), _)) => s.kind == SymKind.ObjType && info(s).typeKind.contains(TypeKindE.Open)
    case OType.Splice(m) =>
      // abstract types (parameters, module paths) of kind `type` may be open
      true
    case _ => false

  /** Elaborates a type definition (Section 4.7) with cycle detection. */
  def ensureTypeDef(s: Sym, useSpan: Span): Boolean =
    syms.state(s) match
      case ElabState.Done => true
      case ElabState.InProgress =>
        ctx.report(Diagnostic.error("E0104", s"cyclic type definition `${s.name}`", useSpan, "refers back to the definition")
          .withLabel(s.span, "type definition declared here")
          .withNote("type definitions are unfolded and must not form a cycle; declare an open type or struct instead"))
        false
      case ElabState.Pending => inItemOf(s)(elabTypeDef(s))

  private def elabTypeDef(s: Sym): Boolean =
    syms(s).state = ElabState.InProgress
    val d = s.decl.get.asInstanceOf[Decl]
    val psc = Scope(Some(s.owner), s"parameters of ${s.name}", ScopeKey.Params(s.key))
    val ps = d.params.flatMap {
      case Param.VarParam(v) =>
        val p = newParam(v.name, v.span, psc)
        syms.define(p, TypeU)
        psc.enter(p)
        Some(p)
      case p => err("E0004", "type definitions take only type parameters", p.span); None
    }
    val rhs = elabOType(d.defn.get, psc, TVars.NoTVars)
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
        .withHelp(s"mark it `%abbrev ${Printer.showItem(d).stripSuffix(".")}.` to have it always expanded")
        .withSuggestion("mark it `%abbrev`", d.span.startPoint, "%abbrev "))
    syms(s).typeDef = Some(TypeDefInfo(ps, rhs))
    syms(s).mtype = Some(TypeU)
    syms(s).state = ElabState.Done
    true

  private[meta] def unfoldTypeDef(s: Sym, args: List[OType], span: Span): OType =
    if !ensureTypeDef(s, span) then return OType.Err
    val td = syms.typeDef(s).get
    if args.length != td.params.length then
      err("E0207", s"type definition `${s.name}` expects ${td.params.length} type argument(s), found ${args.length}", span)
      return OType.Err
    normO(substO(td.rhs, td.params.zip(args.map(QuoteType(_))).toMap))
