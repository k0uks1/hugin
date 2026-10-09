package hugin.core
package elab

import hugin.syntax.{Literal, Tree}
import hugin.syntax.Trees.*
import hugin.util.*
import scala.collection.mutable

/** Quoted patterns (reference: reflection): a quote `'{ … }` in a pattern of a reflective type elaborates to a
 *  constructor pattern over the reflective types, so that coverage, termination and index unification
 *  apply unchanged. `$X` binds a meta variable, `$_` matches anything, `$..Xs` the rest of a sequence; a
 *  plain variable matches any object variable and `_` the object wildcard; object constants and literals
 *  are matched by identity ([[Pat.PAtom]]). A higher-order hole `$F[V]` (with `V` bound by an enclosing
 *  aggregate) binds `F : Term -> Formula`, the matched formula with `V` abstracted: a pattern variable for
 *  the formula and a definition of `F` added to the clause's `where` block. */
trait QuotedPatterns:
  self: Elaborator =>

  private var derived: Option[mutable.ListBuffer[Item]] = None

  /** Runs `f` (the elaboration of a clause's patterns) and returns the definitions its higher-order
   *  holes need. */
  def withDerivedBindings[A](f: => A): (A, List[Item]) =
    val saved = derived
    val buf = mutable.ListBuffer.empty[Item]
    derived = Some(buf)
    try (f, buf.toList)
    finally derived = saved

  def quotedPattern(t: Quote, k: RKind): Pat = patternOf(quotedContent(Cxt.empty, t, k))

  private def patternOf(q: Q): Pat =
    val r = reflective(spanOf(q))
    q match
      case Q.Hole(VarRef(n), _, sp) => Pat.PVar(n, sp)
      case Q.Hole(Wildcard(), _, sp) => Pat.PWild(sp)
      case Q.Hole(Parens(x), k, sp) => patternOf(Q.Hole(x, k, sp))
      case Q.Hole(x, _, _) => fail(ReflectionProblem.HoleNotVariable(x.span))
      case Q.EntryHole(x, k, sp) => patternOf(Q.Hole(x, k, sp))
      case Q.SeqHole(_, _, sp) => fail(ReflectionProblem.MisplacedSequenceHole(sp))
      case Q.HigherOrder(f, args, k, sp) => higherOrder(f, args, k, sp)
      case Q.Con(n @ ("tapp" | "fatom"), List(sym @ Q.SymC(id, _), Q.QList(elems, _, lsp)), _, sp) =>
        // the holes at the columns of a constant bind terms of the columns' types
        val cols = objtype.ObjEnv(core).relInfo(objtype.OHead.G(id), Nil).map(_.cols.map(_._2)).getOrElse(Vector.empty)
        val typedHoles: Int => Option[Pat] = i =>
          elems(i) match
            case Q.Hole(VarRef(x), RKind.Term, hs) => cols.lift(i).flatMap(typedHole(x, _, hs))
            case _ => None
        Pat.PCon(r.ctor(n), List(patternOf(sym), listPattern(elems, lsp, typedHoles)), sp)
      case Q.Con(n, args, _, sp) => Pat.PCon(r.ctor(n), args.map(patternOf), sp)
      case Q.QList(elems, _, sp) => listPattern(elems, sp, _ => None)
      case Q.Var(_, sp) => Pat.PCon(r.ctor("tvar"), List(Pat.PWild(sp)), sp)
      case Q.Bound(i, sp) => Pat.PCon(r.ctor("tbound"), List(Pat.PLit(i.toLong, sp)), sp)
      case Q.Wild(sp) => Pat.PCon(r.ctor("twild"), Nil, sp)
      case Q.QLit(l, sp) => Pat.PAtom(Tm.Lit(l, Stage.S1), sp)
      case Q.SymC(id, sp) => Pat.PAtom(Tm.Quote(Tm.Global(id)), sp)
      case Q.SymTm(_, sp) => fail(ReflectionProblem.Unsupported("a relation given by meta code", "a pattern", sp))
      case Q.Raw(_, sp) => fail(ReflectionProblem.Unsupported("this syntax", "a pattern", sp))

  private def listPattern(elems: List[Q], sp: Span, special: Int => Option[Pat]): Pat =
    val r = reflective(sp)
    elems.zipWithIndex.foldRight(Pat.PCon(r.nil, Nil, sp)) { case ((e, i), acc) =>
      e match
        case Q.SeqHole(x, k, hs) if i == elems.length - 1 => patternOf(Q.Hole(x, k, hs))
        case Q.SeqHole(_, _, hs) => fail(ReflectionProblem.SequenceHoleNotLast(hs))
        case _ => Pat.PCon(r.cons, List(special(i).getOrElse(patternOf(e)), acc), spanOf(e))
    }

  /** The hole `$X` at a column of the object type `ty`: a variable for its data, and `X = (qterm X' : quoted
   *  ty)` added to the clause's `where` block, if the type is a base type or a constant's. */
  private def typedHole(x: Name, ty: objtype.OTy, span: Span): Option[Pat] =
    import objtype.{OHead, OTy}
    val tyTree: Option[Tree] = ty match
      case OTy.Base(b) => Some(Ident(b.show)(span))
      case OTy.Con(OHead.G(id), Nil) => Some(SymRef(id, core.globals(id).name)(span))
      case OTy.Fact(OHead.G(id), Nil) => Some(SymRef(id, core.globals(id).name)(span))
      case _ => None
    for
      buf <- derived
      t <- tyTree
      quotedId <- typedGlobal("quoted")
      qtermId <- typedGlobal("qterm")
    yield
      val data = s"$x#data"
      val rhs =
        Ascribe(Apply(SymRef(qtermId, "qterm")(span), VarRef(data)(span))(span), Apply(SymRef(quotedId, "quoted")(span), t)(span))(span)
      buf += Def(Ident(x)(span), Nil, rhs)(span)
      Pat.PVar(data, span)

  /** `$F[V̄]`: a variable for the formula under the aggregates' binders, and `F = [w̄] openF i₁ w₁ (…)` (`openT` for a term). */
  private def higherOrder(f: Tree, args: List[Q], k: RKind, span: Span): Pat =
    val r = reflective(span)
    val name = f match
      case VarRef(n) => n
      case other => fail(ReflectionProblem.HoleNotVariable(other.span))
    val indices = args.map {
      case Q.Bound(i, _) => i
      case other => fail(ReflectionProblem.HigherOrderHoleArgument(spanOf(other)))
    }
    val body = s"$name#body"
    val params = indices.indices.map(j => s"$name#$j").toList
    val opened = indices.zip(params).foldRight(VarRef(body)(span): Tree) { case ((i, w), acc) =>
      val fn = if k == RKind.Term then SymRef(r.openT, "openT")(span) else SymRef(r.openF, "openF")(span)
      Apply(Apply(Apply(fn, Lit(Literal.IntL(i.toLong))(span))(span), VarRef(w)(span))(span), acc)(span)
    }
    val lambda = params.foldRight(opened)((w, acc) => Lambda(VarRef(w)(span), Some(SymRef(r.term, "term")(span)), acc)(span))
    derived.foreach(_ += Def(Ident(name)(f.span), Nil, lambda)(span))
    Pat.PVar(body, span)

  private def spanOf(q: Q): Span = q match
    case Q.Hole(_, _, s) => s
    case Q.EntryHole(_, _, s) => s
    case Q.SeqHole(_, _, s) => s
    case Q.HigherOrder(_, _, _, s) => s
    case Q.Con(_, _, _, s) => s
    case Q.QList(_, _, s) => s
    case Q.Var(_, s) => s
    case Q.Bound(_, s) => s
    case Q.Wild(s) => s
    case Q.QLit(_, s) => s
    case Q.SymC(_, s) => s
    case Q.SymTm(_, s) => s
    case Q.Raw(_, s) => s
