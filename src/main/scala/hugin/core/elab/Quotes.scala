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

  /** A hole that is a whole entry of a quote (`'{ $r }`, `'{ a. $i. }`) of kind `kind` (a rule or an
   *  item): in an expression, a meta value of that kind, or of type `formula` (a fact) or `rule` (for an
   *  item); in a pattern, a variable for the whole entry. */
  case EntryHole(t: Tree, kind: RKind, span: Span)
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

/** Reflection quotes (reference: reflection): `'{ … }` checked against a reflective type denotes data of
 *  that type, read in the category the type gives (a module or a sequence of rules: entries with their
 *  periods; a rule or an item: one entry; a formula, a term, a reference to a constant, a declaration, a
 *  measure: one entry without `:-` or period), with `$x` holes for meta values, `$..xs` for sequences and
 *  `$f[V]` in patterns. Names of object constants resolve to their symbols. A plain uppercase variable is
 *  an object variable (in a pattern: any object variable); the variable an aggregate's term names is bound
 *  by it (locally nameless). The same analysis reads a directive's arguments, which are quoted
 *  implicitly ([[QuoteTerms]]), and the rules and queries of a file that a module-wide directive rewrites.
 */
trait Quotes:
  self: Elaborator =>
  import core.*

  private val quotedArith: Map[String, ArithOp] =
    Map("+" -> ArithOp.Add, "-" -> ArithOp.Sub, "*" -> ArithOp.Mul, "/" -> ArithOp.Div, "^" -> ArithOp.Concat)
  private val quotedCmp: Map[String, CmpOp] =
    Map("=" -> CmpOp.Eq, "<>" -> CmpOp.Ne, "<" -> CmpOp.Lt, "<=" -> CmpOp.Le, ">" -> CmpOp.Gt, ">=" -> CmpOp.Ge)

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

  def isObjectConstant(id: Int): Boolean =
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
      case (_, qt: Quote) => fail(ReflectionProblem.Unsupported("a quote", kindName(k), qt.span))
      case (RKind.Item | RKind.Rule, _) => entry(c, Rule(None, List(t), None)(sp), k)
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
      case (RKind.Formula, _) if metaValueAt(c, t) => metaValue(c, t, k)
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
      // a rule of the file reified for a module-wide directive: an ascription has no representation, the
      // term is reflected without it (its type is checked again where the rule is elaborated)
      case (RKind.Term, Ascribe(e, _)) if reifyingRules => q(e, k)
      case (RKind.Term, _) if metaValueAt(c, t) => metaValue(c, t, k)
      case (RKind.Term, _) => application(c, t, "tapp", bound)
      case (RKind.Sym, _) => symbol(c, t, "a reference to an object constant")
      case (RKind.Decl, RuleRef(n)) => Q.Con("drule", List(Q.QLit(Literal.StrL(n), sp), noAttributes(sp)), true, sp)
      case (RKind.Decl, _) => Q.Con("dconst", List(symbol(c, t, "a declaration"), noAttributes(sp)), true, sp)
      case (RKind.Measure, _) => measure(t)
      case (RKind.List(e), _) => fail(ReflectionProblem.NotObjectSyntax(kindName(k), sp))

  /** The content of the quote `qt` read at kind `k`. */
  def quotedContent(c: Cxt, qt: Quote, k: RKind): Q = k match
    case RKind.List(e @ (RKind.Item | RKind.Rule)) => Q.QList(qt.entries.map(entry(c, _, e)), e, qt.span)
    case RKind.List(_) => fail(ReflectionProblem.QuoteCategory(kindName(k), qt.span))
    case _ =>
      qt.entries match
        case List(one) if k == RKind.Item || k == RKind.Rule =>
          entry(c, one, k) match
            case Q.SeqHole(_, _, sp) => fail(ReflectionProblem.MisplacedSequenceHole(sp))
            case other => other
        case List(Rule(None, List(e), None)) if !qt.terminated => quoted(c, e, k, Nil)
        case entries => fail(ReflectionProblem.QuoteShape(kindName(k), entriesFound(entries, qt.terminated), qt.span))

  private def entriesFound(entries: List[Item], terminated: Boolean): String = entries match
    case Nil => "nothing"
    case List(_: Query) => "a query"
    case List(Rule(Some(_), _, _)) => "a named rule"
    case List(Rule(_, _, Some(_))) => "a rule"
    case List(_) if terminated => "an item ending with a period"
    case es => s"${es.length} items"

  /** An entry of a quote (or a rule or query of the file) as data of kind `k`, a rule or an item: a
   *  whole-entry hole, a sequence hole (in a sequence), a rule, a named rule or a query (items only). */
  def entry(c: Cxt, e: Item, k: RKind): Q =
    val sp = e.span
    e match
      case Rule(None, List(Parens(h)), None) if isHole(h) => entry(c, Rule(None, List(h), None)(sp), k)
      case Rule(None, List(SpliceE(x)), None) => Q.EntryHole(x, k, sp)
      case Rule(None, List(SpliceSeq(x)), None) => Q.SeqHole(x, k, sp)
      case Rule(name, heads, body) =>
        val hs = if body.isEmpty then heads.flatMap(conjuncts) else heads
        val parts = List(sequence(c, hs, RKind.Formula, Nil, sp), sequence(c, body.toList.flatMap(conjuncts), RKind.Formula, Nil, sp))
        val horn = Q.Con("horn", parts, true, sp)
        (k, name) match
          case (RKind.Rule, None) => horn
          case (RKind.Rule, Some(n)) => fail(ReflectionProblem.Unsupported("a rule name", "a rule (a named rule is an item)", n.span))
          case (_, None) => Q.Con("irule", List(horn), false, sp)
          case (_, Some(n)) => Q.Con("inamed", List(Q.QLit(Literal.StrL(n.name), n.span), horn), false, sp)
      case Query(body) if k == RKind.Item => Q.Con("iquery", List(sequence(c, conjuncts(body), RKind.Formula, Nil, sp)), false, sp)
      case other => fail(ReflectionProblem.NotObjectSyntax(kindName(k), sp))

  private def isHole(t: Tree): Boolean = t match
    case _: SpliceE | _: SpliceSeq => true
    case _ => false

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
    args.collectFirst { case r: RecordLit => r }.foreach(r =>
      fail(ReflectionProblem.Unsupported("a record that does not name the columns of the constant", "data", r.span))
    )
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
      case None =>
        h match
          // a name whose declaration has a syntax error
          case Ident(n) if state.erroneous(n) || state.unelaborated(n) => syntaxError(h.span)
          // a member of a module whose declaration has a syntax error
          case Select(q, _) if rootName(q).exists(n => state.erroneous(n) || state.unelaborated(n)) => syntaxError(h.span)
          case _: Ident | _: Select if rootName(h).isDefined =>
            // an unresolved name is reported as such (E0101, with similar names)
            infer(c, h)
            fail(ReflectionProblem.NotObjectSyntax(what, h.span))
          case _ => fail(ReflectionProblem.NotObjectSyntax(what, h.span))

  private def rootName(t: Tree): Option[Name] = t match
    case Ident(n) => Some(n)
    case Select(q, _) => rootName(q)
    case Parens(i) => rootName(i)
    case _ => None

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
