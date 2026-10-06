package hugin.meta
package typer

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{OType, Column, TParam, BaseType, Mode, ArithOp, CmpOp, RelRef, Expansion, ModeSpec, DirKind}
import hugin.obj
import scala.collection.mutable

/** Inference and checking of meta expressions, application with implicit parameters (Section 4.3). */
private[meta] trait MetaExpressions extends TyperBase:
  self: Typer =>
  import MExpr.*
  import MType.*

  // ======================================================================= meta expressions

  /** Classification of the head of an application spine. */
  private[meta] enum Head:
    case Obj(s: Sym) // object relation / constructor / struct
    case TypeLike(s: Sym) // object type, type definition or base type
    case Meta(m: MExpr, t: MType) // meta value
    case ObjVar(name: String)
    case Bad

  private[meta] def classify(t: Tree, sc: Scope, rc: RuleCtx | Null): Head =
    val h = classify0(t, sc, rc)
    if h == Head.Bad && rc != null then rc.failed = true
    h

  private[meta] def classify0(t: Tree, sc: Scope, rc: RuleCtx | Null): Head = t match
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
  private[meta] def capturesVar(s: Sym): Boolean = s.mtype match
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

  private[meta] def paramName(p: Tree): String = p match
    case Ident(n) => n
    case VarRef(n) => n
    case _ => "_"

  private[meta] def inferSelect(sel: Select, sc: Scope): (MExpr, MType) =
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
  private[meta] def elabApp(
      fm: MExpr,
      ft: MType,
      args: List[Tree],
      sc: Scope,
      rc: RuleCtx | Null,
      span: Span,
      headTree: Tree
  ): (MExpr, MType) =
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
  private[meta] def objectVar(t: Tree, sc: Scope): Option[VarRef] = t match
    case v @ VarRef(n) => if sc.lookup(n).exists(s => s.mtype != null && capturesVar(s)) then None else Some(v)
    case Apply(f, a) => objectVar(f, sc).orElse(objectVar(a, sc))
    case Select(q, _) => objectVar(q, sc)
    case Infix(_, l, r) => objectVar(l, sc).orElse(objectVar(r, sc))
    case Parens(i) => objectVar(i, sc)
    case Trees.Neg(x) => objectVar(x, sc)
    case _ => None

  private[meta] def isMetaCode(t: Tree, sc: Scope): Boolean = t match
    case VarRef(n) => sc.lookup(n).exists(s => s.mtype match { case Code(_) => true; case _ => false })
    case Parens(i) => isMetaCode(i, sc)
    case _ => false

  /** An object term passed where a meta argument of type ⇑τ is expected is quoted (Section 3.2, rule 4). */
  private[meta] def quoteArg(a: Tree, sc: Scope, rc: RuleCtx): MExpr =
    elabTerm(a, sc, rc) match
      case obj.Term.Splice(m @ Ref(s)) if s.mtype match { case Code(_) => true; case _ => false } => m
      case t => QuoteTerm(t)

  private[meta] def argInfer(a: Tree, sc: Scope, rc: RuleCtx | Null): (MExpr, MType) =
    a match
      case VarRef(n) if rc != null && !sc.lookup(n).exists(capturesVar) =>
        err("E0201", s"runtime value used at compile time", a.span, s"object variable `$n` cannot be a meta argument here")
        (MExpr.Err, MType.Err)
      case _ => inferM(a, sc)

  private[meta] def mentions(t: MType, s: Sym): Boolean =
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
  private[meta] def matchM(p: MType, a: MType, solved: mutable.LinkedHashMap[Sym, Option[OType]]): Unit = (p, a) match
    case (Code(x), Code(y)) => matchO(x, y, solved)
    case (RelT(xs), RelT(ys)) if xs.length == ys.length => xs.zip(ys).foreach((x, y) => matchO(x.tpe, y.tpe, solved))
    case (Pi(_, d1, c1, _), Pi(_, d2, c2, _)) => matchM(d1, d2, solved); matchM(c1, c2, solved)
    case (Sig(f1, _), Sig(f2, _)) =>
      for (g, gt) <- f1; (h, ht) <- f2.find(_._1.name == g.name) do matchM(gt, ht, solved)
    case _ =>

  private[meta] def matchO(p: OType, a: OType, solved: mutable.LinkedHashMap[Sym, Option[OType]]): Unit =
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

  private[meta] def isMetaOfType(t: Tree, sc: Scope, mt: MType): Boolean = t match
    case Parens(i) => isMetaOfType(i, sc, mt)
    case Ident(n) => sc.lookup(n).exists(s => (s.kind == SymKind.MetaDef || s.kind == SymKind.MetaParam) && s.mtype == mt)
    case VarRef(n) => sc.lookup(n).exists(s => s.kind == SymKind.MetaParam && s.mtype == mt)
    case _ => false
