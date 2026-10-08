package hugin.core

import scala.collection.mutable

/** Families of object constants (REDESIGN §6.7): `list A : type.` is the meta function `list : ⇑type ->
 *  ⇑type`, `nil : list A.` the meta constant `nil : {A : ⇑type} -> ⇑$(list A)`. An application to closed
 *  object types reduces to an *instance*: an object constant created once per family and normalised
 *  arguments (memoised, which gives applicative sharing: one `len[int]` per program), named after the
 *  family and its arguments (`len[int]`, `pair[int, string]`), as the old monomorphization named them.
 *
 *  Instances are created by evaluation (the only effect of evaluation besides module instances); an
 *  instance created during an elaboration that was undone stays, which is harmless (it is an object
 *  constant nothing refers to). */
trait Families:
  self: Core =>

  private val familyMemo = mutable.LinkedHashMap.empty[(Int, List[Tm]), Int]

  /** The instances of all families, in creation order. */
  def instances: List[Int] = familyMemo.values.toList

  /** The instance of family `fam` (with `arity` arguments) at `args`, if they are closed: its code
   *  `⟨inst⟩`, the value of the family's application. */
  def familyInstance(fam: Int, args: List[Val]): Option[Val] =
    closedKey(args).map(_.map(stripPositions)).map { key =>
      val id = familyMemo.getOrElseUpdate((fam, key), createInstance(fam, args, key))
      Val.Quote(Val.Rigid(Head.Glob(id), Nil))
    }

  private def createInstance(fam: Int, args: List[Val], key: List[Tm]): Int =
    val g = globals(fam)
    val decl = g.kind match
      case GlobalKind.Family(d, _) => d
      case other => throw Impossible(s"instance of $other")
    val ty = args.foldLeft(g.ty)((t, a) =>
      force(t) match
        case Val.Pi(_, _, _, cl) => inst(cl, a)
        case other => throw Impossible(s"family type $other")
    )
    val objTy = force(ty) match
      case Val.Lift(t) => t
      case other => throw Impossible(s"family result $other")
    val name = s"${g.name}[${key.map(showInstanceArg).mkString(", ")}]"
    val tyTm = quote(0, objTy)
    addGlobal(GlobalEntry(
      name,
      eval(Nil, tyTm),
      tyTm,
      Stage.S0,
      GlobalKind.Object(decl),
      g.span,
      g.declSpan,
      instanceOf = Some((fam, key))
    ))

  def isInstanceOf(inst: Int, fam: Int): Boolean = globals(inst).instanceOf.exists(_._1 == fam)

  /** `inst sp =? fam ā $ sp2` where `inst` is an instance of `fam` (a family applied to unknown types
   *  denotes the instance at the types that solve them): the arguments are unified with the instance's,
   *  the rest of the spines with each other. */
  def unifyInstance(l: Int, inst: Int, sp: Spine, famSp: Spine): Unit =
    val key = globals(inst).instanceOf.get._2
    famSp.reverse.splitAt(key.length) match
      case (args, Elim.ESplice :: rest) if args.forall(_.isInstanceOf[Elim.EApp]) =>
        args.zip(key).foreach { case (Elim.EApp(a, _), k) => unify(l, a, eval(Nil, k)); case _ => }
        unifySp(l, sp, rest.reverse)
      case _ => throw UnifyError(UnifyFailure.Mismatch)

  private def showInstanceArg(t: Tm): String = t match
    case Tm.Quote(u) => showTm(Nil, u)
    case other => showTm(Nil, other)

  /** A term without positions (instances are keyed by their arguments up to positions). */
  def stripPositions(t: Tm): Tm = t match
    case Tm.Obj(ObjForm.Loc(_), List(u)) => stripPositions(u)
    case Tm.App(f, a, i) => Tm.App(stripPositions(f), stripPositions(a), i)
    case Tm.Quote(a) => Tm.Quote(stripPositions(a))
    case Tm.Obj(f, as) => Tm.Obj(f, as.map(stripPositions))
    case Tm.FactTy(a) => Tm.FactTy(stripPositions(a))
    case other => other
