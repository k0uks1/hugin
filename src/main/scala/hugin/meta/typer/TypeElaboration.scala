package hugin.meta
package typer

import hugin.syntax.TreeOps.{flattenApp, flattenArrow}
import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{OType, Column, TParam, Mode}
import hugin.obj
import scala.collection.mutable

/** Object types, meta types, signatures and meta subtyping (Sections 3.1, 4.2, 4.4). */
private[meta] trait TypeElaboration extends TyperBase:
  self: Typer =>
  import MExpr.*
  import MType.*

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
              noteUse(t.span, s)
              syms.mtype(s) match
                case Some(TypeU) => OType.Splice(Ref(s))
                case Some(RelT(_, _)) => OType.Splice(FactTypeOf(Ref(s)))
                case None => OType.Err
                case Some(other) =>
                  err("E0202", s"`$n` is not a type", t.span, s"has meta type ${other.show}")
                  OType.Err
            case _ =>
              tv match
                case TVars.Family(_, imp, true) =>
                  val p = TParam(n)
                  imp(n) = p
                  OType.Param(p)
                case TVars.MetaImplicit(isc, coll) =>
                  val p = newParam(n, t.span, isc)
                  syms.define(p, TypeU)
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
                case SymKind.BaseType =>
                  if args.nonEmpty then err("E0207", s"`$n` takes no type arguments", t.span)
                  OType.Base(s.base.get)
                case SymKind.TypeDef => unfoldTypeDef(s, argTypes, t.span)
                case SymKind.ObjType | SymKind.Struct | SymKind.Rel | SymKind.Ctor =>
                  ensureDecl(s)
                  val as = argTypes
                  val tparams = syms.tparams(s)
                  if syms.state(s) == ElabState.Done && as.length != tparams.length then
                    if tparams.nonEmpty && as.isEmpty then
                      err(
                        "E0207",
                        s"family `$n` needs ${tparams.length} type argument(s)",
                        t.span,
                        s"expected `$n ${tparams.map(_.name).mkString(" ")}`"
                      )
                    else err("E0207", s"`$n` expects ${tparams.length} type argument(s), found ${as.length}", t.span)
                    OType.Err
                  else
                    val m = if as.isEmpty then Ref(s) else TApp(Ref(s), as)
                    if s.kind == SymKind.ObjType then OType.Splice(m) else OType.Splice(FactTypeOf(m))
                case SymKind.MetaDef | SymKind.MetaParam =>
                  if !visible(s, id.span) then OType.Err
                  else if args.nonEmpty then
                    err("E0202", s"`$n` cannot be applied to type arguments", t.span); OType.Err
                  else
                    syms.mtype(s) match
                      case Some(TypeU) => OType.Splice(Ref(s))
                      case Some(RelT(_, _)) => OType.Splice(FactTypeOf(Ref(s)))
                      case other =>
                        err("E0202", s"`$n` is not a type", id.span, s"has meta type ${other.fold("?")(_.show)}")
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
              case RelT(_, _) => OType.Splice(FactTypeOf(m))
              case MType.Err => OType.Err
              case other => err("E0202", s"`${Printer.show(sel)}` is not a type", sel.span, s"has meta type ${other.show}"); OType.Err
        case other =>
          err("E0202", "expected an object type", other.span); OType.Err
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
    case Ident(n) if sc.lookup(n).exists(_.kind == SymKind.BaseType) => Prim(sc.lookup(n).get.base.get)
    case Ident(n)
        if sc.lookup(n).exists(s =>
          s.kind == SymKind.MetaDef && s.decl.exists {
            case Decl(_, _, Keyword(Kw.Mod), _, _, _) => true
            case Def(_, _, _: RecordType) => true
            case _ => false
          }
        ) =>
      val s = sc.lookup(n).get
      noteUse(t.span, s)
      if !visible(s, t.span) then MType.Err else syms.sigValue(s).getOrElse(MType.Err)
    case sel: Select =>
      val (m, mt) = inferM(sel, sc)
      mt match
        case ModU => normM(m) match
            case SigV(sig) => sig
            case _ => err("E0202", "signature paths must be statically known", sel.span); MType.Err
        case TypeU => Code(OType.Splice(m))
        case RelT(_, _) => Code(OType.Splice(FactTypeOf(m)))
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
          val psc = localScope(Some(sc), "formula function type")
          doms.foldRight(PropT: MType) { case ((l, d), acc) =>
            val x = newParam(l.map(_.name).getOrElse(fresh("_")), l.map(_.span).getOrElse(d.span), psc)
            val dt = Code(elabOType(d, sc, tv))
            syms.define(x, dt)
            Pi(x, dt, acc, isImplicit = false)
          }
        case _ =>
          val psc = localScope(Some(sc), "function type")
          def go(ds: List[(Option[Ident], Tree)]): MType = ds match
            case Nil => elabMType(cod, psc, tv)
            case (l, d) :: rest =>
              val dt = elabMType(d, psc, tv)
              val x = newParam(l.map(_.name).getOrElse(fresh("_")), l.map(_.span).getOrElse(d.span), psc)
              syms.define(x, dt)
              l.foreach(_ => psc.enter(x))
              Pi(x, dt, go(rest), isImplicit = false)
          go(doms)
    case _ => Code(elabOType(t, sc, tv))

  /** Whether a type tree denotes an object type (rather than a meta type such as a signature or function type). */
  private[meta] def isObjectTypeTree(t: Tree, sc: Scope): Boolean = t match
    case Parens(i) => isObjectTypeTree(i, sc)
    case _: Arrow | _: RecordType => false
    case Keyword(k) => k == Kw.Rel
    case Ident(n) =>
      sc.lookup(n) match
        case Some(s) if s.kind == SymKind.MetaDef && syms.sigValue(s).isDefined => false
        case Some(s) if s.kind == SymKind.MetaDef || s.kind == SymKind.MetaParam =>
          syms.mtype(s).exists(t => t == TypeU || t.isInstanceOf[RelT])
        case _ => true
    case _ => true

  /** A signature field `c : τ̄ -> a` with an object type `a` declares a constructor, as the same declaration
   *  does in a module body (Section 2.5): ⇑(τ̄ → a). A field `x : a` stays a value of code type ⇑a. */
  private def constructorField(t: Tree, sc: Scope, tv: TVars): Option[MType] = t match
    case _: Arrow =>
      val (doms, cod) = flattenArrow(t)
      cod match
        case Keyword(_) => None
        case _ if isObjectTypeTree(cod, sc) && doms.forall((_, d) => isObjectTypeTree(d, sc)) =>
          Some(RelT(doms.map((l, d) => Column(l.map(_.name), elabOType(d, sc, tv))), Some(elabOType(cod, sc, tv))))
        case _ => None
    case _ => None

  private[meta] def elabSig(rt: RecordType, sc: Scope, tv: TVars): MType =
    val ssc = localScope(Some(sc), "signature")
    val fields = mutable.ListBuffer.empty[(Sym, MType)]
    val reqs = mutable.ListBuffer.empty[Req]
    for e <- rt.entries do
      e match
        case SigEntry.FieldDecl(l, ft) =>
          if ssc.lookupLocal(l.name).isDefined then
            err("E0307", s"duplicate field `${l.name}` in signature", l.span)
          else
            val fty = constructorField(ft, ssc, tv).getOrElse(elabMType(ft, ssc, tv))
            val f = newParam(l.name, l.span, ssc)
            syms.define(f, fty)
            ssc.enter(f)
            fields += ((f, fty))
        case SigEntry.Complete(l, sp) =>
          fields.find(_._1.name == l.name) match
            case Some((_, RelT(_, _))) => reqs += Req.Complete(l.name, sp)
            case Some(_) => err("E0208", s"`%complete` requires a relation field, but `${l.name}` is not one", l.span)
            case None => unresolved(l.name, l.span, ssc, "field")
        case SigEntry.ModeReq(l, ms, sp) =>
          fields.find(_._1.name == l.name) match
            case Some((_, RelT(cols, _))) =>
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
    case (RelT(_, r1), RelT(_, r2)) if r1.isDefined != r2.isDefined =>
      Some(if r1.isDefined then "a constructor where a relation is expected" else "a relation where a constructor is expected")
    case (RelT(c1, _), RelT(c2, _)) =>
      // constructor results are checked at the object level after elaboration, like code types
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
      val self = newParam("self", Span.NoSpan, localScope(None, "signature"))
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
    case other => other.show.replace("~(", "(")
  private[meta] def showPath(m: MExpr): String = m match
    case Ref(s) => s.name
    case Proj(x, l) => s"${showPath(x)}.$l"
    case FactTypeOf(x) => showPath(x)
    case TApp(f, as) => (showPath(f) :: as.map(showO)).mkString(" ")
    case other => MExpr.show(other)

  def showMT(t: MType): String = t match
    case Code(o) => s"⇑${showO(o)}"
    case RelT(cols, res) =>
      s"⇑(${(cols.map(c => c.label.map(l => s"$l : ").getOrElse("") + showO(c.tpe)) :+ res.map(showO).getOrElse("rel")).mkString(" -> ")})"
    case Pi(x, d, c, imp) =>
      val dom = if imp then s"{${x.name} : ${showMT(d)}}" else if x.name.startsWith("_") then showMT(d) else s"(${x.name} : ${showMT(d)})"
      s"$dom -> ${showMT(c)}"
    case Sig(fs, _) => fs.map((s, ft) => s"${s.name} : ${showMT(ft)}").mkString("{ ", ", ", " }")
    case other => other.show

  private[meta] def mismatch(expected: MType, found: MType, span: Span, reason: String): Unit =
    var d = Diagnostic.error("E0203", "meta type mismatch", span, s"expected `${showMT(expected)}`")
      .withNote(s"found `${showMT(found)}`")
    if !reason.startsWith("expected") then d = d.withNote(reason)
    ctx.report(d)
