package hugin.core

/** Numerals of nat-like families (reference: meta/families, numerals): a family with exactly two
 *  constructors, one without arguments and one with a single explicit argument of the family itself. The
 *  numeral `n` is the successor applied `n` times to the constant, and `e + k` the successor applied `k`
 *  times to `e`. Every construction and every view of numerals goes through this trait, so that a
 *  representation other than unary terms can replace it without changing the rules that use it. */
trait Naturals:
  self: Core =>

  /** The largest literal of a nat-like family (E0901): numerals are unary terms. */
  val maxNatLiteral: Long = 100000L

  /** For a nat-like family: its constant and successor constructors. */
  def natLike(fam: Int): Option[(Int, Int)] = globals(fam).kind match
    case GlobalKind.Inductive(List(a, b)) if !isPi(globals(fam).ty) =>
      (natShape(fam, a), natShape(fam, b)) match
        case (Some(false), Some(true)) => Some((a, b))
        case (Some(true), Some(false)) => Some((b, a))
        case _ => None
    case _ => None

  /** The nat-like family a type is, with its constructors. */
  def natType(ty: Val): Option[(Int, Int)] = force(ty) match
    case Val.Rigid(Head.Glob(f), Nil) => natLike(f)
    case _ => None

  /** `e + k`: the successor `suc` applied `k` times to `e`. */
  def natSucc(suc: Int, e: Tm, k: Long): Tm =
    (1L to k).foldLeft(e)((acc, _) => Tm.App(Tm.Global(suc), acc, Icit.Expl))

  /** The numeral `n` of the family with the constructors `zero` and `suc`. */
  def natTerm(zero: Int, suc: Int, n: Long): Tm = natSucc(suc, Tm.Global(zero), n)

  /** A term as `e + k` (`None` for `e` if it is the numeral `k`), if it is an application of a successor:
   *  how numerals are printed. */
  def numeralView(t: Tm): Option[(Option[Tm], Long)] = t match
    case Tm.App(Tm.Global(s), a, Icit.Expl) if successorOf(s).isDefined =>
      val zero = successorOf(s).get
      var k = 1L
      var e = a
      var more = true
      while more do
        e match
          case Tm.App(Tm.Global(`s`), b, Icit.Expl) => k += 1; e = b
          case _ => more = false
      e match
        case Tm.Global(`zero`) => Some((None, k))
        case _ => Some((Some(e), k))
    case Tm.Global(z) if constantOf(z) => Some((None, 0L))
    case _ => None

  /** For the successor constructor of a nat-like family: the constant constructor. */
  private def successorOf(id: Int): Option[Int] = familyOf(id).flatMap(natLike).collect { case (z, s) if s == id => z }

  private def constantOf(id: Int): Boolean = familyOf(id).flatMap(natLike).exists(_._1 == id)

  private def familyOf(id: Int): Option[Int] =
    if id < 0 || id >= globals.length then None
    else
      globals(id).kind match
        case GlobalKind.Constructor(f) => Some(f)
        case _ => None

  private def isPi(ty: Val): Boolean = force(ty).isInstanceOf[Val.Pi]

  /** `Some(false)` for a constant of `fam`, `Some(true)` for a constructor with one explicit argument of
   *  type `fam`. */
  private def natShape(fam: Int, c: Int): Option[Boolean] = force(globals(c).ty) match
    case Val.Pi(_, Icit.Expl, a, cl) if isFam(a, fam) && isFam(inst(cl, Val.local(0)), fam) => Some(true)
    case Val.Pi(_, _, _, _) => None
    case r => Option.when(isFam(r, fam))(false)

  private def isFam(a: Val, fam: Int): Boolean = force(a) match
    case Val.Rigid(Head.Glob(f), Nil) => f == fam
    case _ => false
