package hugin.core
package elab

import hugin.obj.{ArithOp, CmpOp}
import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Quoted object syntax, analysed: the reflective data it denotes, before it becomes a term (an
 *  expression, [[Quotes]]) or a pattern ([[QuotedPatterns]]). `Con` is a constructor of reflective data by
 *  name; `located` ones carry the position of their syntax (terms, formulas, rules). */
enum Q:
  case Hole(t: Tree, kind: RKind, span: Span)
  case SeqHole(t: Tree, kind: RKind, span: Span)
  case HigherOrder(fn: Tree, args: List[Q], kind: RKind, span: Span)
  case Con(name: Name, args: List[Q], located: Boolean, span: Span)
  case QList(elems: List[Q], kind: RKind, span: Span)
  case Var(name: Name, span: Span)
  case Bound(index: Int, span: Span)
  case Wild(span: Span)
  case QLit(l: Literal, span: Span)
  case SymC(id: Int, span: Span)

  /** A symbol given by meta code of a relation type (a functor's parameter, a module body's member, a
   *  clause's variable `R : ⇑(A -> rel)`): only in expressions. */
  case SymTm(tm: Tm, span: Span)

  /** Data built directly (a declaration's empty attributes, a measure): only in expressions. */
  case Raw(tm: Tm, span: Span)

/** Reification (reference: reflection): object syntax written where a reflective type is expected denotes
 *  data, with `$x` holes for meta values of reflective types and `$..xs` for sequences. Names of object
 *  constants resolve to their symbols. A plain uppercase variable is an object variable (in a pattern:
 *  any object variable); the variable an aggregate's term names is bound by it (locally nameless).
 *  Also the meta lists `[ē]` and `e :: es`. */
trait Quotes:
  self: Elaborator =>
  import core.*

  private val quotedArith: Map[String, ArithOp] =
    Map("+" -> ArithOp.Add, "-" -> ArithOp.Sub, "*" -> ArithOp.Mul, "/" -> ArithOp.Div, "^" -> ArithOp.Concat)
  private val quotedCmp: Map[String, CmpOp] =
    Map("=" -> CmpOp.Eq, "<>" -> CmpOp.Ne, "<" -> CmpOp.Lt, "<=" -> CmpOp.Le, ">" -> CmpOp.Gt, ">=" -> CmpOp.Ge)

  /** Whether `t`, expected of kind `k`, is quoted object syntax rather than meta code. */
  def quotedSyntax(t: Tree, k: RKind, c: Cxt = Cxt.empty): Boolean = (t, k) match
    case (Parens(i), _) => quotedSyntax(i, k, c)
    case (_: SpliceSeq, _) => true
    case (_, RKind.List(_)) => false
    case (_: SpliceE | _: SpliceHO, _) => true
    case (_: RuleRef, RKind.Decl) => true
    case (_, RKind.Decl | RKind.Sym) => symbolOf(c, t).isDefined
    case (_, RKind.Measure) => measureSyntax(c, t)
    case (_: RuleQuote, RKind.Rule | RKind.Item) => true
    case (_: Conj | _: Disj | _: Not | _: Agg, RKind.Formula | RKind.Rule | RKind.Item) => true
    case (Infix(op, _, _), RKind.Formula | RKind.Rule | RKind.Item) => quotedCmp.contains(op)
    case (Infix(op, _, _), RKind.Term) => quotedArith.contains(op)
    case (_: Lit | _: Neg, RKind.Term) => true
    case _ =>
      TreeOps.flattenApp(t) match
        case (SpliceE(_), args) => args.nonEmpty
        case (h, _) => symbolOf(c, h).isDefined

  /** The object constant (relation, constructor, type, or family of them) a head denotes. */
  def objectConstant(c: Cxt, h: Tree): Option[Int] = h match
    case Parens(i) => objectConstant(c, i)
    case Ident(n) if !c.scope.contains(n) => lookupGlobal(n).filter(isObjectConstant)
    case SymRef(id, _) => Some(id).filter(isObjectConstant)
    case s: Select =>
      try undoOnFailure(constantOf(ev(c, infer(c, s)._1)))
      catch case _: ElabError => None
    case _ => None

  /** The symbol a head denotes: an object constant, or meta code of a relation (or fact constructor)
   *  type in `c`. */
  def symbolOf(c: Cxt, h: Tree): Option[Q] =
    objectConstant(c, h).map(Q.SymC(_, h.span)).orElse(symbolCode(c, h).map(Q.SymTm(_, h.span)))

  private def symbolCode(c: Cxt, h: Tree): Option[Tm] = h match
    case Parens(i) => symbolCode(c, i)
    case Ident(n) if c.scope.contains(n) => symbolTyped(c, h)
    case VarRef(n) if c.scope.contains(n) => symbolTyped(c, h)
    case s: Select if hugin.syntax.TreeOps.headName(s).exists(n => c.scope.contains(n.name)) => symbolTyped(c, h)
    case _ => None

  private def symbolTyped(c: Cxt, h: Tree): Option[Tm] =
    try
      undoOnFailure {
        val (tm, ty, st) = infer(c, h)
        force(ty) match
          case Val.Lift(x) if st == Stage.S1 && isFactConstantType(x) => Some(tm)
          case _ => None
      }
    catch case _: ElabError => None

  /** Whether `t` is a measure as written in `%terminates`: a variable, a label, or a parenthesised tuple
   *  of them (not meta code of type `measure`). */
  private def measureSyntax(c: Cxt, t: Tree): Boolean = t match
    case Parens(i) => measureSyntax(c, i)
    case Conj(a, b) => measureSyntax(c, a) && measureSyntax(c, b)
    case VarRef(n) => !c.scope.contains(n)
    case Ident(n) =>
      !c.scope.contains(n) && !lookupGlobal(n).exists(id => reflectiveKind(globals(id).ty).contains(RKind.Measure))
    case _ => false

  private def isObjectConstant(id: Int): Boolean =
    globals(id).stage == Stage.S0 || globals(id).kind.isInstanceOf[GlobalKind.Family]

  private def constantOf(v: Val): Option[Int] = forceData(v) match
    case Val.Rigid(Head.Glob(id), Nil) if isObjectConstant(id) => Some(id)
    case Val.Quote(x) => constantOf(x)
    case _ => None

  // ---------------------------------------------------------------- analysis

  /** The quoted syntax `t` of kind `k`; `bound` are the variables bound by enclosing aggregates (innermost
   *  first). */
  def quoted(c: Cxt, t: Tree, k: RKind, bound: List[Name]): Q =
    val sp = t.span
    def q(x: Tree, k2: RKind, b: List[Name] = bound) = quoted(c, x, k2, b)
    (k, t) match
      case (_, Parens(i)) => q(i, k)
      case (_, SpliceE(x)) => Q.Hole(x, k, sp)
      case (_, _: SpliceSeq) => fail(ReflectionProblem.MisplacedSequenceHole(sp))
      case (_, SpliceHO(f, args)) => Q.HigherOrder(f, args.map(q(_, RKind.Term)), k, sp)
      case (RKind.Item, _) => Q.Con("irule", List(q(t, RKind.Rule)), false, sp)
      case (RKind.Rule, RuleQuote(hs, b)) =>
        Q.Con(
          "horn",
          List(sequence(c, hs, RKind.Formula, bound, sp), sequence(c, b.toList.flatMap(conjuncts), RKind.Formula, bound, sp)),
          true,
          sp
        )
      case (RKind.Rule, _) =>
        Q.Con("horn", List(Q.QList(List(q(t, RKind.Formula)), RKind.Formula, sp), Q.QList(Nil, RKind.Formula, sp)), true, sp)
      case (RKind.Formula, Conj(a, b)) => Q.Con("fconj", List(q(a, k), q(b, k)), true, sp)
      case (RKind.Formula, Disj(a, b)) => Q.Con("fdisj", List(q(a, k), q(b, k)), true, sp)
      case (RKind.Formula, Not(a)) => Q.Con("fnot", List(q(a, k)), true, sp)
      case (RKind.Formula, Infix("=", x, Agg(kind, term, body))) =>
        val inner = varName(term).getOrElse("") :: bound
        val parts = List(Q.Con(aggCtor(kind), Nil, false, sp), q(x, RKind.Term), q(term, RKind.Term, inner), q(body, RKind.Formula, inner))
        Q.Con("fagg", parts, true, sp)
      case (RKind.Formula, Infix(op, l, r)) if quotedCmp.contains(op) =>
        Q.Con("fcmp", List(Q.Con(cmpCtor(quotedCmp(op)), Nil, false, sp), q(l, RKind.Term), q(r, RKind.Term)), true, sp)
      case (RKind.Formula, Wildcard()) => Q.Hole(t, k, sp)
      case (RKind.Formula, _: Agg) => fail(ReflectionProblem.Unsupported("an aggregate without `X =`", "a formula", sp))
      case (RKind.Formula, _) => application(c, t, "fatom", bound)
      case (RKind.Term, VarRef(n)) =>
        bound.indexOf(n) match
          case -1 => Q.Var(n, sp)
          case i => Q.Bound(i, sp)
      case (RKind.Term, Wildcard()) => Q.Wild(sp)
      case (RKind.Term, Lit(l)) =>
        val ctor = l match
          case Literal.IntL(_) => "tint"
          case Literal.FloatL(_) => "tfloat"
          case Literal.StrL(_) => "tstr"
        Q.Con(ctor, List(Q.QLit(l, sp)), true, sp)
      case (RKind.Term, Neg(a)) => Q.Con("tneg", List(q(a, k)), true, sp)
      case (RKind.Term, Infix(op, l, r)) if quotedArith.contains(op) =>
        Q.Con("tarith", List(Q.Con(arithCtor(quotedArith(op)), Nil, false, sp), q(l, k), q(r, k)), true, sp)
      case (RKind.Term, _) => application(c, t, "tapp", bound)
      case (RKind.Sym, _) => symbol(c, t, "a reference to an object constant")
      case (RKind.Decl, RuleRef(n)) => Q.Con("drule", List(Q.QLit(Literal.StrL(n), sp), noAttributes(sp)), true, sp)
      case (RKind.Decl, _) => Q.Con("dconst", List(symbol(c, t, "a declaration"), noAttributes(sp)), true, sp)
      case (RKind.Measure, _) => measure(t)
      case (RKind.List(e), _) => fail(ReflectionProblem.NotObjectSyntax(kindName(k), sp))

  private def noAttributes(sp: Span): Q =
    val r = reflective(sp)
    Q.Raw(Tm.App(Tm.Global(r.snil), Tm.Global(r.ctor("attr")), Icit.Impl), sp)

  /** `X`, `(X, Y)`: `mvars`; `l`, `(l, m)`: `mlabels`. */
  private def measure(t: Tree): Q =
    def parts(t: Tree): List[Tree] = t match
      case Parens(i) => parts(i)
      case Conj(a, b) => parts(a) ++ parts(b)
      case other => List(other)
    val ps = parts(t)
    val ctor =
      if ps.forall(_.isInstanceOf[VarRef]) then "mvars"
      else if ps.forall(_.isInstanceOf[Ident]) then "mlabels"
      else fail(ReflectionProblem.NotObjectSyntax("a measure (variables or labels)", t.span))
    val names = ps.map(p => Left(Tm.Lit(Literal.StrL(nameOf(p)), Stage.S1)))
    Q.Raw(con(ctor, listData(Tm.Base(hugin.obj.BaseType.StringT, Stage.S1), names)), t.span)

  private def varName(t: Tree): Option[Name] = t match
    case VarRef(n) => Some(n)
    case Parens(i) => varName(i)
    case _ => None

  /** An object constant (or a hole) applied to terms: an atom (`fatom`) or a term (`tapp`). */
  private def application(c: Cxt, t: Tree, ctor: Name, bound: List[Name]): Q =
    val (h, written) = TreeOps.flattenApp(t)
    val args = namedArguments(c, h, written).getOrElse(written)
    unsupportedForm(t).foreach(w =>
      fail(ReflectionProblem.Unsupported(w, kindName(if ctor == "fatom" then RKind.Formula else RKind.Term), t.span))
    )
    args.collectFirst { case r: RecordLit => r }.foreach(r => fail(ReflectionProblem.Unsupported("a named pattern", "data", r.span)))
    val sym = h match
      case SpliceE(x) => Q.Hole(x, RKind.Sym, h.span)
      case _ => symbol(c, h, if ctor == "fatom" then "a formula" else "a term")
    Q.Con(ctor, List(sym, sequence(c, args, RKind.Term, bound, t.span)), true, t.span)

  /** `r { l₁ = e₁, … }` (a named pattern, Section 2.4) as the positional arguments of `r` (a column not
   *  named is `_` with `..`); `None` if the arguments are not one record or `r` has no such labels. */
  private def namedArguments(c: Cxt, h: Tree, args: List[Tree]): Option[List[Tree]] = args match
    case List(rl: RecordLit) =>
      objectConstant(c, h).flatMap { id =>
        val labels = objectColumns(globals(id).ty).map(_._1)
        val byLabel = rl.fields.map(f => f.label.name -> f.value).toMap
        Option.when(labels.nonEmpty && !labels.contains("_") && byLabel.keySet.subsetOf(labels.toSet) &&
          (rl.rest || labels.forall(byLabel.contains)))(labels.map(l => byLabel.getOrElse(l, Wildcard()(rl.span))))
      }
    case _ => None

  private def symbol(c: Cxt, h: Tree, what: String): Q =
    symbolOf(c, h) match
      case Some(q @ Q.SymC(id, _)) =>
        h match
          case Ident(_) =>
            state.used += id
            recordUse(h.span, id)
          case _ =>
        q
      case Some(q) => q
      case None => fail(ReflectionProblem.NotObjectSyntax(what, h.span))

  private def unsupportedForm(t: Tree): Option[String] = t match
    case _: As => Some("`as`")
    case _: Ascribe => Some("an ascription")
    case _: With => Some("a functional update `with`")
    case _: Lambda => Some("a lambda")
    case _: RecordLit | _: RecordType | _: ModuleBody => Some("a record")
    case _: ListLit | _: ConsE => Some("a meta list")
    case _ => None

  private def sequence(c: Cxt, elems: List[Tree], k: RKind, bound: List[Name], span: Span): Q =
    Q.QList(
      elems.map {
        case s @ SpliceSeq(x) => Q.SeqHole(x, k, s.span)
        case e => quoted(c, e, k, bound)
      },
      k,
      span
    )

  def conjuncts(t: Tree): List[Tree] = t match
    case Conj(a, b) => conjuncts(a) ++ conjuncts(b)
    case Parens(i @ Conj(_, _)) => conjuncts(i)
    case other => List(other)

  def kindName(k: RKind): String = k match
    case RKind.Sym => "a reference to an object constant"
    case RKind.Term => "a term"
    case RKind.Formula => "a formula"
    case RKind.Rule => "a rule"
    case RKind.Item => "an item"
    case RKind.Decl => "a declaration"
    case RKind.Measure => "a measure"
    case RKind.List(e) => s"a list of ${kindName(e).dropWhile(_ != ' ').drop(1)}s"

  // ---------------------------------------------------------------- expressions

  /** Quoted syntax `t` checked against the reflective type of kind `k`: its data. */
  def reify(c: Cxt, t: Tree, k: RKind): Tm = reifyQ(c, quoted(c, t, k, Nil))

  private def reifyQ(c: Cxt, q: Q): Tm = q match
    case Q.Hole(x, k, _) => check(c, x, ev(c, kindType(k)), Stage.S1)
    case Q.SeqHole(_, _, sp) => fail(ReflectionProblem.MisplacedSequenceHole(sp))
    case Q.HigherOrder(f, args, k, sp) =>
      val r = reflective(sp)
      val fty = args.foldRight(kindType(k))((_, acc) => Tm.Pi("_", Icit.Expl, Tm.Global(r.term), acc))
      args.foldLeft(check(c, f, eval(Nil, fty), Stage.S1))((acc, a) => Tm.App(acc, reifyQ(c, a), Icit.Expl))
    case Q.Con(n, args, located, sp) =>
      val t = con(n, args.map(reifyQ(c, _))*)
      if located then Tm.loc(sp, t) else t
    case Q.QList(elems, k, _) =>
      listData(
        kindType(k),
        elems.map {
          case Q.SeqHole(x, k2, _) => Right(check(c, x, ev(c, kindType(RKind.List(k2))), Stage.S1))
          case e => Left(reifyQ(c, e))
        }
      )
    case Q.Var(n, sp) => Tm.loc(sp, con("tvar", Tm.Lit(Literal.StrL(n), Stage.S1)))
    case Q.Bound(i, sp) => Tm.loc(sp, con("tbound", indexData(i)))
    case Q.Wild(sp) => Tm.loc(sp, con("twild"))
    case Q.QLit(l, _) => Tm.Lit(l, Stage.S1)
    case Q.SymC(id, sp) => Tm.loc(sp, Tm.Quote(Tm.Global(id)))
    case Q.SymTm(tm, sp) => Tm.loc(sp, tm)
    case Q.Raw(tm, _) => tm

  // ---------------------------------------------------------------- meta lists

  /** `[ē]` or `e :: es` against `ty` (a list type, or unknown). */
  def checkList(c: Cxt, t: Tree, ty: Val): Tm =
    val r = reflective(t.span)
    val elem = listElement(ty).getOrElse {
      val m = ev(c, freshType(c, Stage.S1, t.span, "the type of the list's elements"))
      unifyAt(c, t.span, ty, listOf(m))
      m
    }
    val elemTm = quote(c.lvl, elem)
    t match
      case ListLit(es) =>
        listData(
          elemTm,
          es.map {
            case SpliceSeq(x) => Right(check(c, x, listOf(elem), Stage.S1))
            case e => Left(check(c, e, elem, Stage.S1))
          }
        )
      case ConsE(h, tl) =>
        Tm.App(
          Tm.App(Tm.App(Tm.Global(r.scons), elemTm, Icit.Impl), check(c, h, elem, Stage.S1), Icit.Expl),
          check(c, tl, listOf(elem), Stage.S1),
          Icit.Expl
        )
      case other => unsupported(other)

  /** A list with an inferred element type. */
  def inferList(c: Cxt, t: Tree): (Tm, Val, Stage) =
    reflective(t.span)
    val m = ev(c, freshType(c, Stage.S1, t.span, "the type of the list's elements"))
    (checkList(c, t, listOf(m)), listOf(m), Stage.S1)
