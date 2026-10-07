package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Universes and sorts: `type` (object types, U₀), `Type` (meta types, levels inferred and cumulative,
 *  REDESIGN §11 Q1), the object sorts `rel` and `prop`, builtin base types; elaborating types and the
 *  stage of a type's values. */
trait Universes:
  self: Elaborator =>
  import core.*

  /** `Type` at a fresh level: `Type l : Type (l+1)`. */
  def inferMetaUniverse(): (Tm, Val, Stage) =
    val l = levels.fresh()
    (Tm.U1(l), Val.U1(l.succ), Stage.S1)

  def inferKeyword(k: Keyword): (Tm, Val, Stage) = k.kw match
    case Kw.Type => (Tm.U0, Val.U0, Stage.S0)
    case Kw.Rel => (Tm.RelT, Val.U0, Stage.S0)
    case Kw.Prop => (Tm.PropT, Val.U0, Stage.S0)
    case Kw.Mod =>
      fail(
        Diagnostic.error("E0907", "`mod` is not part of the new meta level", k.span, "not supported")
          .withNote("signatures are record types: they live in a meta universe `Type`, which is inferred")
      )

  def inferBuiltin(n: Ident): (Tm, Val, Stage) = builtinTypes.get(n.name) match
    case Some(b) => (Tm.Base(b, Stage.S0), Val.U0, Stage.S0)
    case None => error("E0101", s"unknown builtin type `${n.name}`", n.span, "expected int, float or string")

  /** The universe of a stage (at a fresh level for the meta stage). */
  def universe(st: Stage): Val = st match
    case Stage.S0 => Val.U0
    case Stage.S1 => Val.U1(levels.fresh())

  /** Infers a type: its term, its stage and its universe. A meta value of type `⇑type` (an object type
   *  computed at compile time) used as a type is spliced. */
  def inferU(c: Cxt, t: Tree): (Tm, Stage, Val) =
    val (tm, ty, s) = infer(c, t)
    force(ty) match
      case Val.U0 => (tm, Stage.S0, Val.U0)
      case u @ Val.U1(_) => (tm, Stage.S1, u)
      case Val.Lift(x) if force(x) == Val.U0 => (Tm.splice(tm), Stage.S0, Val.U0)
      case rel if isRelationType(rel) => (Tm.FactTy(tm), Stage.S0, Val.U0)
      case Val.Flex(_, _) if s == Stage.S1 && state.unknownTypesAre == Stage.S0 =>
        unifyAt(c, t.span, Val.Lift(Val.U0), ty)
        (Tm.splice(tm), Stage.S0, Val.U0)
      case Val.Flex(_, _) =>
        val u = universe(s)
        unifyAt(c, t.span, u, ty)
        (tm, s, u)
      case other =>
        fail(Diagnostic.error("E0901", "expected a type", t.span, s"this is a term of type `${show(c, other)}`"))

  /** Checks a type at a stage (at any level, for the meta stage). */
  def checkType(c: Cxt, t: Tree, st: Stage): Tm = check(c, t, universe(st), st)

  /** Requires the universe `u` (of some type) to be contained in `Type l` (cumulativity). */
  def requireLe(c: Cxt, span: Span, u: Val, l: Level): Unit = force(u) match
    case Val.U1(k) =>
      if !levels.le(k, l) then fail(mismatch(c, span, Val.U1(l), Stage.S1, u, Stage.S1, UnifyFailure.Universe))
    case _ =>

  def isUniverse(v: Val): Boolean = force(v) match
    case Val.U0 | Val.U1(_) => true
    case _ => false

  /** The stage of the values of a type. */
  def stageOfType(a: Val): Stage = force(a) match
    case Val.Rigid(_, Elim.ESplice :: _) | Val.Flex(_, Elim.ESplice :: _) => Stage.S0
    case Val.Lift(_) => Stage.S1
    case Val.Base(_, st) => st
    case Val.RelT | Val.PropT | Val.FactTy(_) | Val.U0 => Stage.S0
    case Val.Pi(_, _, d, _) => stageOfType(d)
    case Val.Rigid(Head.Glob(id), _) if isObjectType(id) => Stage.S0
    case _ => Stage.S1

  /** `A₁ -> … -> rel` at the object level: a relation, which used as a type is its fact type. */
  def isRelationType(v: Val): Boolean = force(v) match
    case Val.RelT => true
    case Val.Pi(_, _, d, cl) => stageOfType(d) == Stage.S0 && isRelationType(inst(cl, Val.Wild))
    case _ => false

  /** Whether a type is the type of an object constant: an object type (`type`), a relation type, or a
   *  constructor type whose result is a declared (or computed) object type — not a base type or `prop`. */
  def isObjectConstantType(v: Val): Boolean = force(v) match
    case Val.U0 | Val.RelT | Val.FactTy(_) => true
    case Val.Pi(_, _, d, cl) => stageOfType(d) == Stage.S0 && isObjectConstantType(inst(cl, Val.Wild))
    case Val.Rigid(Head.Glob(id), Nil) => isObjectType(id)
    case Val.Rigid(_, Elim.ESplice :: _) | Val.Flex(_, Elim.ESplice :: _) => true
    case _ => false

  /** In a meta type, every lifted object arrow `⇑(A -> B)` is the type of a relation or constructor
   *  (the object level has no other functions). */
  def objectPartsValid(v: Val): Boolean = force(v) match
    case Val.Lift(a) => force(a) match
        case p: Val.Pi => isObjectConstantType(p)
        case _ => true
    case Val.Pi(_, _, d, cl) => objectPartsValid(d) && objectPartsValid(inst(cl, Val.Wild))
    case _ => true

  /** Whether a global is a declared object type (`expr : type.`). */
  def isObjectType(id: Int): Boolean = globals(id).stage == Stage.S0 && force(globals(id).ty) == Val.U0
