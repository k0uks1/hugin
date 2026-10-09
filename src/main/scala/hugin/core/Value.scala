package hugin.core

import hugin.obj.{ArithOp, BaseType}
import hugin.syntax.Literal

/** A closure: a term under one binder, with the environment of its free variables (innermost first). */
final case class Closure(env: List[Val], body: Tm)

/** The head of a neutral value: a bound variable (a de Bruijn *level*) or a global without a definition
 *  (a postulate, an object constant, an inductive type or constructor, or a function stuck on its
 *  arguments). */
enum Head:
  case Local(lvl: Int)
  case Glob(id: Int)

  /** A module body in an environment that is not closed, not instantiated ([[Modules]]). */
  case Module(body: ModuleBody, env: List[Val])

/** Eliminations of a neutral value; a spine lists them innermost (most recent) first. */
enum Elim:
  case EApp(a: Val, i: Icit)
  case ESplice
  case EProj(label: Name)

type Spine = List[Elim]

/** The unfolded value of a [[Val.Top]], compared by identity (so that comparing values never compares
 *  both forms). It is computed when the `Top` is built, not on demand: evaluation has effects (module
 *  bodies are generative, object variables are fresh), so the unfolded value must be computed exactly
 *  when evaluation without folding computed it. */
final class Unfold(val value: Val)

object Unfold:
  def of(v: Val): Unfold = Unfold(v)

/** Values in weak head normal form (normalisation by evaluation, as in elaboration-zoo). */
enum Val:
  case Rigid(h: Head, sp: Spine)

  /** A definition (`GlobalKind.Definition`) applied to `sp` (applications and splices), kept folded for
   *  printing and meta solutions, with its value `unfolded`: *glued* evaluation (smalltt, Kovács's
   *  elaboration-zoo `GluedEval`), with the unfolded value computed eagerly ([[Unfold]]).
   *  [[Evaluation.force]] unfolds it, so code that forces a value before matching on it never sees it. */
  case Top(id: Int, sp: Spine, unfolded: Unfold)
  case Flex(m: Int, sp: Spine)
  case Lam(x: Name, i: Icit, cl: Closure)
  case Pi(x: Name, i: Icit, dom: Val, cl: Closure)
  case U0
  case U1(l: Level)
  case Lift(a: Val)
  case Quote(t: Val)

  /** A record type: its labels and the telescope of field types, closed over `env`. */
  case RecTy(
      labels: List[Name],
      env: List[Val],
      tys: List[Tm],
      reqs: List[SigReq] = Nil,
      decls: List[(hugin.util.Span, hugin.util.Span)] = Nil
  )
  case Rec(fields: List[(Name, Val)])
  case Lit(l: Literal, st: Stage)
  case Base(b: BaseType, st: Stage)
  case RelT
  case PropT

  /** Object arithmetic, or meta arithmetic stuck on a neutral operand. */
  case Arith(op: ArithOp, a: Val, b: Val, st: Stage)
  case Negate(a: Val, st: Stage)
  case Obj(form: ObjForm, args: List[Val])
  case Persist(t: Val)
  case FactTy(r: Val)

object Val:
  def local(l: Int): Val = Rigid(Head.Local(l), Nil)

  /** `_` in object code; also a placeholder for the (irrelevant) column variables of object arrows. */
  val Wild: Val = Obj(ObjForm.Wild, Nil)

  /** `v` without the positions around it. */
  def unloc(v: Val): Val = v match
    case Obj(ObjForm.Loc(_), List(u)) => unloc(u)
    case u => u
