package hugin.core

import hugin.obj.{ArithOp, CmpOp}
import hugin.syntax.{AggKind, Literal}

/** The code bridge (reference: reflection, "The code bridge"; #186 P7a): the primitives of `std/quote` that
 *  convert between object code `⇑A` and the reflective syntax of `std/reflect`.
 *
 *  - `quote : {A : ⇑type} -> ⇑A -> quoted A` and `quoteF : ⇑prop -> formula` are structural homomorphisms on
 *    canonical code: object constants to symbols, literals to `tint`/`tfloat`/`tstr`, arithmetic to
 *    `tarith`/`tneg`, `as`, ascriptions, projections and updates to their constructors, formulas to
 *    `fatom`, `fcmp`, `fnot`, `fconj`, `fdisj`, `fas` and `fagg` (the aggregate's variable as a `tbound`
 *    index). Positions are dropped. A variable that hygiene named (`X#k`) is renamed by its first
 *    occurrence (`X#0`, `Y#1`, …), so the result does not depend on the hygiene counter. Both are stuck on
 *    code that is not canonical (a variable of type `⇑A`, a stuck splice, a family not instantiated).
 *  - `unquote : {A : ⇑type} -> quoted A -> ⇑A` and `unquoteF : formula -> ⇑prop` are the structural inverses
 *    on closed data; they type nothing (reflected and staged code is typed where it is staged). On a stuck
 *    `quote c` (`quoteF c`), they reduce to `c`: `unquote (quote c) ≡ c` is a conversion rule, like
 *    `$⟨t⟩ = t`.
 *  - `symOf : {R : ⇑type} -> ⇑R -> sym` is the symbol of the code of an object constant.
 *
 *  The constructors the primitives build and read are found from their declared types, by name
 *  ([[CodeBridge.names]]), when the primitive is declared. */
trait CodeBridge:
  self: Core =>
  import Val.*

  /** The constructors of a bridge primitive by name (`-1` where its type does not reach the constructor). */
  final class BridgeCtors(ctors: List[Int]):
    def apply(n: String): Int = ctors(CodeBridge.names.indexOf(n))
    def has(n: String): Boolean = apply(n) >= 0
    private lazy val byId: Map[Int, String] = CodeBridge.names.zip(ctors).collect { case (n, id) if id >= 0 => id -> n }.toMap
    def nameOf(id: Int): Option[String] = byId.get(id)

  /** Renames the variables that hygiene named (`X#k`) by their first occurrence. */
  private final class HygieneNames:
    private val seen = scala.collection.mutable.LinkedHashMap.empty[String, String]
    def apply(n: String): String = n match
      case CodeBridge.Hygienic(hint, _) => seen.getOrElseUpdate(n, s"$hint#${seen.size}")
      case _ => n

  def reduceBridge(op: PrimOp, ctors: List[Int], args: List[Val]): Option[Val] =
    val k = BridgeCtors(ctors)
    (op, args) match
      case (PrimOp.Quote, List(a, Quote(code))) =>
        quoteTerm(k, code, Nil, HygieneNames()).map(d =>
          Rigid(Head.Glob(k("qterm")), List(Elim.EApp(d, Icit.Expl), Elim.EApp(a, Icit.Impl)))
        )
      case (PrimOp.QuoteF, List(Quote(code))) => quoteFormula(k, code, Nil, HygieneNames())
      case (PrimOp.Unquote, List(q)) =>
        cancelled(q, PrimOp.Quote).orElse(dataOf(k, q) match
          case Some(("qterm", List(t))) => unquoteTerm(k, t, Nil).map(Quote(_))
          case _ => None
        )
      case (PrimOp.UnquoteF, List(f)) => cancelled(f, PrimOp.QuoteF).orElse(unquoteFormula(k, f, Nil).map(Quote(_)))
      case (PrimOp.SymOf, List(Quote(code))) =>
        forceData(code) match
          case Rigid(Head.Glob(id), Nil) if objectConstant(id) => Some(Quote(Rigid(Head.Glob(id), Nil)))
          case _ => None
      case _ => None

  /** `c` if `v` is the stuck application of the primitive `op` to `c` (`unquote (quote c) = c`). */
  private def cancelled(v: Val, op: PrimOp): Option[Val] = forceData(v) match
    case Rigid(Head.Glob(id), Elim.EApp(c, Icit.Expl) :: _) =>
      globals(id).kind match
        case GlobalKind.Primitive(`op`, _) => Some(c)
        case _ => None
    case _ => None

  /** Whether `id` is an object constant that object code names: not a family (whose instances are). */
  private def objectConstant(id: Int): Boolean = globals(id).stage == Stage.S0 && globals(id).kind.isInstanceOf[GlobalKind.Object]

  // ---------------------------------------------------------------- code to data

  private def data(id: Int, args: Val*): Val = Rigid(Head.Glob(id), args.reverse.map(Elim.EApp(_, Icit.Expl)).toList)

  private def listOf(k: BridgeCtors, elem: Val, xs: List[Val]): Val =
    xs.foldRight(Rigid(Head.Glob(k("nil")), List(Elim.EApp(elem, Icit.Impl))): Val) { (x, acc) =>
      Rigid(Head.Glob(k("cons")), List(Elim.EApp(acc, Icit.Expl), Elim.EApp(x, Icit.Expl), Elim.EApp(elem, Icit.Impl)))
    }

  /** The type a constructor builds, as a value (the element type of a list of its values). */
  private def typeOf(ctor: Int): Val = globals(ctor).kind match
    case GlobalKind.Constructor(fam) => Rigid(Head.Glob(fam), Nil)
    case other => throw Impossible(s"not a constructor: $other")

  private def str(s: String): Val = Lit(Literal.StrL(s), Stage.S1)

  private def indexOf(k: BridgeCtors, n: Int): Val =
    globals(k("izero")).kind match
      case GlobalKind.Constructor(fam) if natLike(fam).isDefined => Nat(fam, BigInt(n))
      case _ => (0 until n).foldLeft(data(k("izero")))((acc, _) => data(k("isuc"), acc))

  private def all[A](xs: List[Option[A]]): Option[List[A]] = Option.when(xs.forall(_.isDefined))(xs.map(_.get))

  private def quoteTerm(k: BridgeCtors, v: Val, bound: List[String], names: HygieneNames): Option[Val] =
    def go(x: Val) = quoteTerm(k, x, bound, names)
    forceData(v) match
      case Lit(l, Stage.S0) => Some(literalData(k, l))
      case Persist(x) =>
        forceData(x) match
          case IntNum(n) => Some(data(k("tint"), IntNum(n)))
          case Lit(l, Stage.S1) => Some(literalData(k, l))
          case _ => None
      case Obj(ObjForm.Named(n), Nil) =>
        Some(bound.indexOf(n) match
          case -1 => data(k("tvar"), str(names(n)))
          case i => data(k("tbound"), indexOf(k, i))
        )
      case Obj(ObjForm.Wild, Nil) => Some(data(k("twild")))
      case Arith(op, a, b, Stage.S0) => for x <- go(a); y <- go(b) yield data(k("tarith"), data(k(arithName(op))), x, y)
      case Negate(a, Stage.S0) => go(a).map(data(k("tneg"), _))
      case Obj(ObjForm.As, List(a, x)) => for t <- go(a); y <- go(x) yield data(k("tas"), t, y)
      case Obj(ObjForm.Ascribe, List(a, ty)) => go(a).map(data(k("tascribe"), _, Quote(ty)))
      case Obj(ObjForm.Proj(l), List(a)) => go(a).map(data(k("tproj"), _, str(l)))
      case Obj(ObjForm.With(ls), a :: es) =>
        for
          t <- go(a)
          fs <- all(es.map(go))
        yield
          val updates = ls.map(_._1).zip(fs).map((l, f) => data(k("uset"), str(l), f))
          data(k("twith"), t, listOf(k, typeOf(k("uset")), updates))
      case Rigid(Head.Glob(id), spine) =>
        application(k, id, spine, bound, names).map((sym, args) => data(k("tapp"), sym, listOf(k, typeOf(k("tvar")), args)))
      case _ => None

  private def literalData(k: BridgeCtors, l: Literal): Val = l match
    case Literal.IntL(n) => data(k("tint"), IntNum(BigInt(n)))
    case Literal.FloatL(_) => data(k("tfloat"), Lit(l, Stage.S1))
    case Literal.StrL(_) => data(k("tstr"), Lit(l, Stage.S1))

  /** The symbol and the argument terms of an object constant applied to object code. */
  private def application(k: BridgeCtors, id: Int, spine: Spine, bound: List[String], names: HygieneNames): Option[(Val, List[Val])] =
    val oid = globals(id).shared match
      case Some(l) if l.side != Stage.S0 => l.counterpart
      case _ => id
    if !objectConstant(oid) || !spine.forall {
        case Elim.EApp(_, Icit.Expl) => true
        case _ => false
      }
    then None
    else
      val args = spine.reverse.collect { case Elim.EApp(a, _) => quoteTerm(k, a, bound, names) }
      all(args).map(as => (Quote(Rigid(Head.Glob(oid), Nil)), as))

  private def quoteFormula(k: BridgeCtors, v: Val, bound: List[String], names: HygieneNames): Option[Val] =
    def go(x: Val) = quoteFormula(k, x, bound, names)
    // left-nested, as `a, b, c` parses
    def binary(ctor: String, as: List[Val]): Option[Val] = as match
      case first :: rest => rest.foldLeft(go(first))((acc, b) => for x <- acc; y <- go(b) yield data(k(ctor), x, y))
      case Nil => None
    forceData(v) match
      case Obj(ObjForm.And, as) => binary("fconj", as)
      case Obj(ObjForm.Or, as) => binary("fdisj", as)
      case Obj(ObjForm.Not, List(a)) => go(a).map(data(k("fnot"), _))
      case Obj(ObjForm.Compare(op), List(a, b)) =>
        for x <- quoteTerm(k, a, bound, names); y <- quoteTerm(k, b, bound, names)
        yield data(k("fcmp"), data(k(cmpName(op))), x, y)
      case Obj(ObjForm.As, List(a, x)) => for f <- go(a); y <- quoteTerm(k, x, bound, names) yield data(k("fas"), f, y)
      case Obj(ObjForm.Agg(kind), List(x, t, body)) =>
        // the variable that the aggregate's term is binds in the term and the body (locally nameless)
        val inner = forceData(t) match
          case Obj(ObjForm.Named(n), Nil) => n :: bound
          case _ => "" :: bound
        for
          r <- quoteTerm(k, x, bound, names)
          tt <- quoteTerm(k, t, inner, names)
          b <- quoteFormula(k, body, inner, names)
        yield data(k("fagg"), data(k(aggName(kind))), r, tt, b)
      case Rigid(Head.Glob(id), spine) =>
        application(k, id, spine, bound, names).map((sym, args) => data(k("fatom"), sym, listOf(k, typeOf(k("tvar")), args)))
      case _ => None

  private def arithName(op: ArithOp): String = op match
    case ArithOp.Add => "oadd"
    case ArithOp.Sub => "osub"
    case ArithOp.Mul => "omul"
    case ArithOp.Div => "odiv"
    case ArithOp.Concat => "ocat"

  private def cmpName(op: CmpOp): String = op match
    case CmpOp.Eq => "ceq"
    case CmpOp.Ne => "cne"
    case CmpOp.Lt => "clt"
    case CmpOp.Le => "cle"
    case CmpOp.Gt => "cgt"
    case CmpOp.Ge => "cge"

  private def aggName(kind: AggKind): String = kind match
    case AggKind.Count => "acount"
    case AggKind.Sum => "asum"
    case AggKind.Min => "amin"
    case AggKind.Max => "amax"

  // ---------------------------------------------------------------- data to code

  /** A constructor application of the bridge's data: its name and explicit arguments. */
  private def dataOf(k: BridgeCtors, v: Val): Option[(String, List[Val])] = natView(forceData(v)) match
    case Rigid(Head.Glob(id), spine) => k.nameOf(id).map(n => (n, spine.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }))
    case _ => None

  private def elementsOf(k: BridgeCtors, v: Val): Option[List[Val]] =
    val out = List.newBuilder[Val]
    var cur = v
    var result: Option[List[Val]] | Null = null
    while result == null do
      dataOf(k, cur) match
        case Some(("nil", Nil)) => result = Some(out.result())
        case Some(("cons", List(x, xs))) =>
          out += x
          cur = xs
        case _ => result = None
    result.nn

  private def stringOf(v: Val): Option[String] = forceData(v) match
    case Lit(Literal.StrL(s), Stage.S1) => Some(s)
    case _ => None

  private def indexValue(k: BridgeCtors, v: Val): Option[Int] = forceData(v) match
    case Nat(_, n) if n.isValidInt => Some(n.toInt)
    case _ =>
      dataOf(k, v) match
        case Some(("izero", Nil)) => Some(0)
        case Some(("isuc", List(i))) => indexValue(k, i).map(_ + 1)
        case _ => None

  private def constantOf(v: Val): Option[Int] = forceData(v) match
    case Quote(x) =>
      forceData(x) match
        case Rigid(Head.Glob(id), Nil) if objectConstant(id) => Some(id)
        case _ => None
    case _ => None

  private def opOf[A](k: BridgeCtors, v: Val, name: A => String, all: Iterable[A]): Option[A] =
    dataOf(k, v).flatMap((n, _) => all.find(name(_) == n))

  private def unquoteTerm(k: BridgeCtors, v: Val, bound: List[Val]): Option[Val] =
    def go(x: Val) = unquoteTerm(k, x, bound)
    dataOf(k, v) match
      case Some(("tvar", List(n))) => stringOf(n).filter(_.nonEmpty).map(s => Obj(ObjForm.Named(s), Nil))
      case Some(("tbound", List(i))) => indexValue(k, i).flatMap(bound.lift)
      case Some(("twild", Nil)) => Some(Val.Wild)
      case Some(("tint", List(n))) =>
        forceData(n) match
          case IntNum(m) => Some(persist(IntNum(m)))
          case Lit(Literal.IntL(m), Stage.S1) => Some(Lit(Literal.IntL(m), Stage.S0))
          case _ => None
      case Some(("tfloat" | "tstr", List(l))) =>
        forceData(l) match
          case Lit(lit, Stage.S1) => Some(Lit(lit, Stage.S0))
          case _ => None
      case Some(("tapp", List(s, ts))) => applied(k, s, ts, bound)
      case Some(("tarith", List(o, a, b))) =>
        // as evaluation builds object arithmetic (on two literals it is computed)
        for op <- opOf(k, o, arithName, ArithOp.values); x <- go(a); y <- go(b) yield arith(op, x, y, Stage.S0)
      case Some(("tneg", List(a))) => go(a).map(negate(_, Stage.S0))
      case Some(("tas", List(a, x))) => for t <- go(a); y <- go(x) yield Obj(ObjForm.As, List(t, y))
      case Some(("tascribe", List(a, ty))) =>
        forceData(ty) match
          case Quote(t) => go(a).map(x => Obj(ObjForm.Ascribe, List(x, t)))
          case _ => None
      case Some(("tproj", List(a, l))) => for t <- go(a); label <- stringOf(l) yield Obj(ObjForm.Proj(label), List(t))
      case Some(("twith", List(a, us))) =>
        for
          t <- go(a)
          fields <- elementsOf(k, us)
          pairs <- all(fields.map(u =>
            dataOf(k, u) match
              case Some(("uset", List(l, e))) => for label <- stringOf(l); x <- go(e) yield (label, x)
              case _ => None
          ))
        yield Obj(ObjForm.With(pairs.map(p => (p._1, hugin.util.Span.NoSpan))), t :: pairs.map(_._2))
      case _ => None

  private def applied(k: BridgeCtors, s: Val, ts: Val, bound: List[Val]): Option[Val] =
    for
      id <- constantOf(s)
      elems <- elementsOf(k, ts)
      args <- all(elems.map(unquoteTerm(k, _, bound)))
    yield Rigid(Head.Glob(id), args.reverse.map(Elim.EApp(_, Icit.Expl)))

  private def unquoteFormula(k: BridgeCtors, v: Val, bound: List[Val]): Option[Val] =
    def go(x: Val) = unquoteFormula(k, x, bound)
    def term(x: Val) = unquoteTerm(k, x, bound)
    dataOf(k, v) match
      case Some(("fatom", List(s, ts))) => applied(k, s, ts, bound)
      case Some(("fcmp", List(o, a, b))) =>
        for op <- opOf(k, o, cmpName, CmpOp.values); x <- term(a); y <- term(b) yield Obj(ObjForm.Compare(op), List(x, y))
      case Some(("fnot", List(f))) => go(f).map(x => Obj(ObjForm.Not, List(x)))
      case Some(("fconj", List(f, g))) => for x <- go(f); y <- go(g) yield Obj(ObjForm.And, List(x, y))
      case Some(("fdisj", List(f, g))) => for x <- go(f); y <- go(g) yield Obj(ObjForm.Or, List(x, y))
      case Some(("fas", List(f, x))) => for a <- go(f); y <- term(x) yield Obj(ObjForm.As, List(a, y))
      case Some(("fagg", List(o, x, t, f))) =>
        // the aggregate's variable: a name that neither source syntax nor `quote` writes
        val inner = Obj(ObjForm.Named(s"V#b${bound.length}"), Nil) :: bound
        for
          kind <- opOf(k, o, aggName, AggKind.values)
          r <- term(x)
          tt <- unquoteTerm(k, t, inner)
          b <- unquoteFormula(k, f, inner)
        yield Obj(ObjForm.Agg(kind), List(r, tt, b))
      case _ => None

object CodeBridge:
  /** The constructors the bridge primitives build and read, by name (`std/reflect`'s). */
  val names: List[String] = List(
    "qterm",
    "tvar",
    "tbound",
    "twild",
    "tint",
    "tfloat",
    "tstr",
    "tapp",
    "tarith",
    "tneg",
    "tas",
    "tascribe",
    "tproj",
    "twith",
    "uset",
    "oadd",
    "osub",
    "omul",
    "odiv",
    "ocat",
    "nil",
    "cons",
    "izero",
    "isuc",
    "fatom",
    "fcmp",
    "fnot",
    "fconj",
    "fdisj",
    "fas",
    "fagg",
    "ceq",
    "cne",
    "clt",
    "cle",
    "cgt",
    "cge",
    "acount",
    "asum",
    "amin",
    "amax"
  )

  /** The names of terms (what `quote` and `unquote` need), and of formulas in addition (`quoteF`, `unquoteF`). */
  val termNames: List[String] =
    names.filterNot(n => n == "qterm" || n.startsWith("f") || n.startsWith("c") && n != "cons" || n.startsWith("a"))
  val formulaNames: List[String] = names.filterNot(_ == "qterm")

  /** A name that hygiene gave a variable: a hint and a number (`X#3`). */
  val Hygienic: scala.util.matching.Regex = "(.*)#([0-9]+)".r
