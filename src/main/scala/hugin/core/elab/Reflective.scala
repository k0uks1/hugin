package hugin.core
package elab

import hugin.obj.{ArithOp, CmpOp}
import hugin.syntax.AggKind
import hugin.util.*

/** The reflective types of the prelude (reference: reflection) and their constructors, by global id. */
final case class ReflectiveGlobals(
    list: Int,
    nil: Int,
    cons: Int,
    append: Int,
    sym: Int,
    term: Int,
    formula: Int,
    rule: Int,
    item: Int,
    decl: Int,
    measure: Int,
    index: Int,
    openF: Int,
    openT: Int,
    ctors: Map[Name, Int]
):
  def ctor(n: Name): Int = ctors(n)

/** What a reflective type is: the kinds of object syntax as data. */
enum RKind:
  case Sym, Term, Formula, Rule, Item

  /** A declaration with its attributes (what local directives change, reference: directives) and the measure
   *  of `%terminates`. */
  case Decl, Measure
  case List(elem: RKind)

/** The reflective embedding (reference: reflection): the prelude's types `term`, `formula`, `rule`, `item` (and
 *  `list` of them, `module = list item`), found by name in the prelude (or, without it, in the file),
 *  how expected types are classified, and the constructors of reflective data. */
trait Reflective:
  self: Elaborator =>
  import core.*

  private val names = List(
    "list",
    "nil",
    "cons",
    "append",
    "sym",
    "term",
    "formula",
    "rule",
    "item",
    "inamed",
    "ierror",
    "irelation",
    "colof",
    "decl",
    "attr",
    "dconst",
    "drule",
    "derror",
    "measure",
    "mvars",
    "mlabels",
    "index",
    "openF",
    "openT",
    "tvar",
    "tbound",
    "twild",
    "tint",
    "tfloat",
    "tstr",
    "tapp",
    "tarith",
    "tneg",
    "fatom",
    "fcmp",
    "fnot",
    "fconj",
    "fdisj",
    "fagg",
    "horn",
    "irule",
    "iquery",
    "izero",
    "isuc",
    "oadd",
    "osub",
    "omul",
    "odiv",
    "ocat",
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

  private var loaded: Option[Option[ReflectiveGlobals]] = None

  /** The version of the scope in which a lookup last missed a name: it is repeated only after the names
   *  changed (the parent's names are fixed; whether all are found depends on nothing else). */
  private var missedAt = -1L

  /** The reflective globals, if the prelude (or the file) declares them all. */
  def reflectiveGlobals: Option[ReflectiveGlobals] =
    if loaded.forall(_.isEmpty) && missedAt != scope.version then
      val found = names.map(n => n -> file.parent.get(n).orElse(scope.get(n))).collect { case (n, Some(id)) => n -> id }.toMap
      if found.size < names.size then missedAt = scope.version
      loaded = Some(Option.when(found.size == names.size && globals(found("sym")).kind == GlobalKind.Symbols) {
        ReflectiveGlobals(
          found("list"),
          found("nil"),
          found("cons"),
          found("append"),
          found("sym"),
          found("term"),
          found("formula"),
          found("rule"),
          found("item"),
          found("decl"),
          found("measure"),
          found("index"),
          found("openF"),
          found("openT"),
          found
        )
      })
    loaded.flatten

  /** The reflective globals, or an error at `span` if they are not declared. */
  def reflective(span: Span): ReflectiveGlobals =
    reflectiveGlobals.getOrElse(fail(ReflectionProblem.NoReflectiveTypes(span)))

  /** The kind of a reflective type. */
  def reflectiveKind(ty: Val): Option[RKind] = reflectiveGlobals.flatMap { r =>
    forceData(ty) match
      case Val.Rigid(Head.Glob(id), Nil) if id == r.sym => Some(RKind.Sym)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.term => Some(RKind.Term)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.formula => Some(RKind.Formula)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.rule => Some(RKind.Rule)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.item => Some(RKind.Item)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.decl => Some(RKind.Decl)
      case Val.Rigid(Head.Glob(id), Nil) if id == r.measure => Some(RKind.Measure)
      case Val.Rigid(Head.Glob(id), List(Elim.EApp(a, _))) if id == r.list => reflectiveKind(a).map(RKind.List(_))
      case _ => None
  }

  /** The element type of a list type `list A` (the meta list). */
  def listElement(ty: Val): Option[Val] = reflectiveGlobals.flatMap { r =>
    forceData(ty) match
      case Val.Rigid(Head.Glob(id), List(Elim.EApp(a, _))) if id == r.list => Some(a)
      case _ => None
  }

  def listOf(elem: Val): Val = Val.Rigid(Head.Glob(reflectiveGlobals.get.list), List(Elim.EApp(elem, Icit.Expl)))

  /** The type of a reflective kind. */
  def kindType(k: RKind): Tm =
    val r = reflectiveGlobals.get
    k match
      case RKind.Sym => Tm.Global(r.sym)
      case RKind.Term => Tm.Global(r.term)
      case RKind.Formula => Tm.Global(r.formula)
      case RKind.Rule => Tm.Global(r.rule)
      case RKind.Item => Tm.Global(r.item)
      case RKind.Decl => Tm.Global(r.decl)
      case RKind.Measure => Tm.Global(r.measure)
      case RKind.List(e) => Tm.App(Tm.Global(r.list), kindType(e), Icit.Expl)

  // ---------------------------------------------------------------- data

  /** A constructor of reflective data applied to its explicit arguments. */
  def con(n: Name, args: Tm*): Tm = args.foldLeft(Tm.Global(reflectiveGlobals.get.ctor(n)): Tm)(Tm.App(_, _, Icit.Expl))

  /** A list of elements of type `elem`: single elements (`Left`) and lists spliced in (`Right`). */
  def listData(elem: Tm, parts: List[Either[Tm, Tm]]): Tm =
    val r = reflectiveGlobals.get
    def nil = Tm.App(Tm.Global(r.nil), elem, Icit.Impl)
    parts.foldRight(Option.empty[Tm]) { (part, acc) =>
      part match
        case Left(e) => Some(Tm.App(Tm.App(Tm.App(Tm.Global(r.cons), elem, Icit.Impl), e, Icit.Expl), acc.getOrElse(nil), Icit.Expl))
        case Right(l) =>
          acc match
            case None => Some(l)
            case Some(rest) => Some(Tm.App(Tm.App(Tm.App(Tm.Global(r.append), elem, Icit.Impl), l, Icit.Expl), rest, Icit.Expl))
    }.getOrElse(nil)

  /** `n` as an `Index`. */
  def indexData(n: Int): Tm = natTerm(reflectiveGlobals.get.ctor("izero"), reflectiveGlobals.get.ctor("isuc"), n.toLong)

  val arithCtor: Map[ArithOp, Name] =
    Map(ArithOp.Add -> "oadd", ArithOp.Sub -> "osub", ArithOp.Mul -> "omul", ArithOp.Div -> "odiv", ArithOp.Concat -> "ocat")
  val cmpCtor: Map[CmpOp, Name] =
    Map(CmpOp.Eq -> "ceq", CmpOp.Ne -> "cne", CmpOp.Lt -> "clt", CmpOp.Le -> "cle", CmpOp.Gt -> "cgt", CmpOp.Ge -> "cge")
  val aggCtor: Map[AggKind, Name] = Map(AggKind.Count -> "acount", AggKind.Sum -> "asum", AggKind.Min -> "amin", AggKind.Max -> "amax")
