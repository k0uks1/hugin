package hugin.core

import CoreTesting.*

/** The memo keys of closed meta applications ([[MemoKeys]], issue #60): the cached read-back gives the
 *  normal forms `quote` gives, closedness is the definition's, and the hash-consed ids are equal exactly
 *  when the normal forms are. */
class MemoKeysSuite extends munit.FunSuite:
  /** The definition of closed keys before the cache (`Matching.closedKey`), as the reference. */
  private def closed(t: Tm): Boolean = t match
    case Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, _) | Tm.U0 | Tm.U1(_) | Tm.RelT | Tm.PropT => true
    case Tm.App(f, a, _) => closed(f) && closed(a)
    case Tm.Rec(fs) => fs.forall(f => closed(f._2))
    case Tm.Quote(a) => closedObject(a)
    case Tm.Obj(ObjForm.Loc(_), List(a)) => closed(a)
    case Tm.Arith(_, a, b, _) => closed(a) && closed(b)
    case _ => false

  private def closedObject(t: Tm): Boolean = t match
    case Tm.Var(_) | Tm.Meta(_) | Tm.AppPruning(_, _) | Tm.Lam(_, _, _) | Tm.Splice(_) => false
    case Tm.App(f, a, _) => closedObject(f) && closedObject(a)
    case Tm.Arith(_, a, b, _) => closedObject(a) && closedObject(b)
    case Tm.Obj(_, as) => as.forall(closedObject)
    case Tm.Negate(a, _) => closedObject(a)
    case Tm.Proj(a, _) => closedObject(a)
    case _ => true

  private val program =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |vlist : Type.
      |vnil : vlist.
      |vcons : nat -> vlist -> vlist.
      |up : nat -> vlist.
      |up zero = vnil.
      |up (suc N) = vcons N (up N).
      |p : int -> rel.
      |r : { a : nat, b : vlist }.
      |l3 = up (suc (suc (suc zero))).
      |l2 = up (suc (suc zero)).
      |again = up (suc (suc (suc zero))).
      |rec = { a = suc zero, b = l2 }.
      |node : type.
      |edge : node -> node -> rel.
      |code : node -> prop = [X] edge X X.
      |num : int = 3.
      |f : nat -> nat = [x] suc x.
      |""".stripMargin

  test("cached keys are the normal forms, closedness and id equality are the reference's") {
    val e = ok(program)
    val core = e.core
    val names = List("l3", "l2", "again", "rec", "code", "num", "f", "zero")
    val values = names.map(n =>
      e.global(n).kind match
        case GlobalKind.Definition(_, v) => v
        case _ => Val.Rigid(Head.Glob(e.elab.scope(n)), Nil)
    )
    // twice: the second time from the caches
    for _ <- 1 to 2; v <- values do
      val nf = core.quote(0, v)
      assertEquals(core.closedKey(List(v)), Option.when(closed(nf))(List(nf)), core.showTm(Nil, nf))
    for (v, i) <- values.zipWithIndex; (w, j) <- values.zipWithIndex do
      (core.closedKeyIds(List(v)), core.closedKeyIds(List(w))) match
        case (Some(a), Some(b)) => assertEquals(a == b, core.quote(0, v) == core.quote(0, w), s"${names(i)} ${names(j)}")
        case _ =>
    assertEquals(core.closedKeyIds(List(values(0))), core.closedKeyIds(List(values(2))))
    assertNotEquals(core.closedKeyIds(List(values(0))), core.closedKeyIds(List(values(1))))
  }
