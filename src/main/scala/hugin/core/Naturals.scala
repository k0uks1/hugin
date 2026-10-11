package hugin.core

/** Numerals of nat-like families (reference: meta/families, numerals): a family with exactly two
 *  constructors, one without arguments and one with a single explicit argument of the family itself. The
 *  numeral `n` is the successor applied `n` times to the constant, and `e + k` the successor applied `k`
 *  times to `e`. Every construction and every view of numerals goes through this trait. A closed numeral
 *  is represented as a number ([[Val.Nat]], [[Tm.Nat]], as in Agda and Lean 4), and code that inspects
 *  constructors sees it through [[natView]]: the unary model stays the definition (issue #131). */
trait Naturals:
  self: Core =>

  /** The nat-like families found so far, with the constructor list they were decided for (a family gets
   *  its constructors one declaration at a time). */
  private val natFamilies = scala.collection.mutable.HashMap.empty[Int, (List[Int], Option[(Int, Int)])]

  /** For a nat-like family: its constant and successor constructors. */
  def natLike(fam: Int): Option[(Int, Int)] = globals(fam).kind match
    case GlobalKind.Inductive(cs @ List(a, b)) =>
      natFamilies.get(fam) match
        case Some((`cs`, r)) => r
        case _ =>
          val r =
            if isPi(globals(fam).ty) then None
            else
              (natShape(fam, a), natShape(fam, b)) match
                case (Some(false), Some(true)) => Some((a, b))
                case (Some(true), Some(false)) => Some((b, a))
                case _ => None
          natFamilies(fam) = (cs, r)
          r
    case _ => None

  /** The nat-like family a type is, with its constructors. */
  def natType(ty: Val): Option[(Int, Int)] = force(ty) match
    case Val.Rigid(Head.Glob(f), Nil) => natLike(f)
    case _ => None

  /** The numeral 0 of `fam`, if constructor `c` is the constant of the nat-like family `fam`. */
  def natZero(fam: Int, c: Int): Option[Val] = natLike(fam) match
    case Some((`c`, _)) => Some(Val.Nat(fam, BigInt(0)))
    case _ => None

  /** The successor `c` of the nat-like family `fam` applied to `a`: the next numeral if `a` is a numeral
   *  (closed numerals are never constructor chains, as Agda's `reduceNat`), and an offset otherwise. */
  def natSuccessorOf(fam: Int, c: Int, a: Val): Option[Val] = natLike(fam) match
    case Some((_, `c`)) =>
      numeral(a) match
        case Val.Nat(`fam`, n) => Some(Val.Nat(fam, n + 1))
        case Val.NatAdd(`fam`, b, k) => Some(Val.NatAdd(fam, b, k + 1))
        // over anything else: an offset of 1, the one form of an open successor
        case _ => Some(Val.NatAdd(fam, a, BigInt(1)))
    case _ => None

  /** `base + k` of the nat-like family `fam`: the numeral if `base` is one, offsets added up, else
   *  [[Val.NatAdd]] (the successor applied `k` times, without a term of that depth). */
  def natAdd(fam: Int, base: Val, k: BigInt): Val =
    if k == 0 then base
    else
      numeral(base) match
        case Val.Nat(f, n) => Val.Nat(f, n + k)
        case Val.NatAdd(f, b, j) => Val.NatAdd(f, b, j + k)
        case _ => Val.NatAdd(fam, base, k)

  /** `v` with folded definitions and solved metas at its head unfolded, without reducing applications:
   *  forcing the argument of every successor would make a chain over a neutral quadratic. */
  private def numeral(v: Val): Val = v match
    case Val.Top(_, _, u) => numeral(u.value)
    case Val.Flex(m, Nil) =>
      metas(m).solution match
        case Some(s) => numeral(s)
        case None => v
    case Val.Obj(ObjForm.Loc(_), List(x)) => numeral(x)
    case Val.NatAdd(f, b, k) =>
      // an offset over a value that has become a numeral or an offset
      numeral(b) match
        case Val.Nat(_, n) => Val.Nat(f, n + k)
        case Val.NatAdd(_, b2, j) => Val.NatAdd(f, b2, j + k)
        case _ => v
    case other => other

  /** A value seen as a constructor application, one constructor at a time: the numeral 0 is the
   *  constant, the numeral `n + 1` the successor applied to the numeral `n` (Agda's `constructorForm`,
   *  Lean's `toCtorIfLit`). Every other value is itself. */
  def natView(v: Val): Val = v match
    case Val.Nat(fam, n) =>
      natLike(fam) match
        case Some((z, s)) =>
          if n == 0 then Val.Rigid(Head.Glob(z), Nil)
          else Val.Rigid(Head.Glob(s), List(Elim.EApp(Val.Nat(fam, n - 1), Icit.Expl)))
        case None => v
    case Val.NatAdd(fam, b, k) =>
      natLike(fam) match
        case Some((_, s)) => Val.Rigid(Head.Glob(s), List(Elim.EApp(if k == 1 then b else Val.NatAdd(fam, b, k - 1), Icit.Expl)))
        case None => v
    case other => other

  /** A value as a numeral (`Left`), or as the successor of its nat-like family applied `i` times to a value
   *  that is neither a numeral nor a successor application (`Right`, forced). */
  def natChain(v: Val): Either[BigInt, (BigInt, Val)] =
    var i = BigInt(0)
    var cur = force(v)
    var result: Either[BigInt, (BigInt, Val)] | Null = null
    while result == null do
      cur match
        case Val.Nat(_, m) => result = Left(m + i)
        case Val.NatAdd(_, b, k) =>
          i += k
          cur = force(b)
        case Val.Rigid(Head.Glob(c), List(Elim.EApp(a, Icit.Expl))) if isSuccessor(c) =>
          i += 1
          cur = force(a)
        case Val.Rigid(Head.Glob(c), Nil) if constantOf(c) => result = Left(i)
        case other => result = Right((i, other))
    result.nn

  /** Whether `c` is the successor of a nat-like family. */
  def isSuccessor(c: Int): Boolean = successorOf(c).isDefined

  /** The successor `suc` applied `k` times to the value `v`. */
  def natSuccs(suc: Int, v: Val, k: BigInt): Val = natAdd(familyOf(suc).get, v, k)

  /** [[force]], then [[natView]]: what code that matches constructor applications inspects. */
  def forceView(v: Val): Val = natView(force(v))

  /** [[natView]] on terms. */
  def natViewTm(t: Tm): Tm = t match
    case Tm.Nat(fam, n) =>
      natLike(fam) match
        case Some((z, s)) => if n == 0 then Tm.Global(z) else Tm.App(Tm.Global(s), Tm.Nat(fam, n - 1), Icit.Expl)
        case None => t
    case Tm.NatAdd(fam, b, k) =>
      natLike(fam) match
        case Some((_, s)) => Tm.App(Tm.Global(s), if k == 1 then b else Tm.NatAdd(fam, b, k - 1), Icit.Expl)
        case None => t
    case other => other

  /** `e + k`: the successor `suc` applied `k` times to `e`; a numeral if `e` is one. */
  def natSucc(suc: Int, e: Tm, k: BigInt): Tm = e match
    case Tm.Nat(fam, n) => Tm.Nat(fam, n + k)
    case Tm.Global(z) if familyOf(z).flatMap(natLike).exists(_._1 == z) => Tm.Nat(familyOf(z).get, k)
    case Tm.NatAdd(fam, b, j) => Tm.NatAdd(fam, b, j + k)
    case _ => if k == 0 then e else Tm.NatAdd(familyOf(suc).get, e, k)

  /** The numeral `n` of the family with the constructors `zero` and `suc`. */
  def natTerm(zero: Int, suc: Int, n: BigInt): Tm = Tm.Nat(familyOf(zero).get, n)

  /** A term as `e + k` (`None` for `e` if it is the numeral `k`), if it is a numeral or an application of a
   *  successor: how numerals are printed. */
  def numeralView(t: Tm): Option[(Option[Tm], BigInt)] = t match
    case Tm.Nat(_, n) => Some((None, n))
    case Tm.NatAdd(_, b, k) =>
      numeralView(b) match
        case Some((e, j)) => Some((e, j + k))
        case None => Some((Some(b), k))
    case Tm.App(Tm.Global(s), a, Icit.Expl) if successorOf(s).isDefined =>
      val zero = successorOf(s).get
      var k = BigInt(1)
      var e = a
      var more = true
      while more do
        e match
          case Tm.App(Tm.Global(`s`), b, Icit.Expl) => k += 1; e = b
          case _ => more = false
      e match
        case Tm.Global(`zero`) => Some((None, k))
        case Tm.Nat(_, n) => Some((None, k + n))
        case Tm.NatAdd(_, b, j) =>
          numeralView(b) match
            case Some((e2, j2)) => Some((e2, k + j + j2))
            case None => Some((Some(b), k + j))
        case _ => Some((Some(e), k))
    case Tm.Global(z) if constantOf(z) => Some((None, BigInt(0)))
    case _ => None

  /** For the successor constructor of a nat-like family: the constant constructor. */
  private def successorOf(id: Int): Option[Int] = familyOf(id).flatMap(natLike).collect { case (z, s) if s == id => z }

  def constantOf(id: Int): Boolean = familyOf(id).flatMap(natLike).exists(_._1 == id)

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
