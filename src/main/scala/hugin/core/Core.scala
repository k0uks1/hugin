package hugin.core

import hugin.util.Span
import scala.collection.mutable

/** What a global is. */
enum GlobalKind:
  /** A meta-level declaration without definition that is not an inductive type, a constructor or a
   *  function: stuck at compile time. */
  case Postulate

  /** An object constant (stage 0): an object type, a relation, a constructor or a struct. */
  case Object(decl: ObjDecl)

  /** A family of object constants (`list A : type.`, `nil : list A.`, `len : list A -> int -> rel.`): a
   *  meta function over `arity` object types whose applications to closed types are instances, object
   *  constants created once per normalised arguments ([[Families]]). */
  case Family(decl: ObjDecl, arity: Int)

  /** A definition `x : A = e.`; unfolded by evaluation. */
  case Definition(tm: Tm, value: Val)

  /** A meta inductive family with its constructors (in declaration order). */
  case Inductive(ctors: List[Int])

  /** A constructor of the family `family`. */
  case Constructor(family: Int)

  /** A function defined by clauses: its case tree over its first `arity` arguments (both known once its
   *  clauses are elaborated; arity -1 before). */
  case Function(arity: Int, tree: Option[CaseTree])

/** What an object constant declares (REDESIGN §3.1). The core only needs to know that it is an object
 *  constant; the handover to the object level ([[hugin.core.handover]]) needs the rest. */
enum ObjDecl:
  /** `a : type.` */
  case OpenType

  /** `a : type <: b.`, a nominal refinement of the object type `base`. */
  case Refinement(base: Tm)

  /** `r : τ̄ -> rel.` */
  case Relation

  /** `c : τ̄ -> a.`; `fact` if declared `%fact` (a fact constructor, readable as a relation). */
  case Constructor(fact: Boolean)

  /** `s : type = { l : τ, … }.`: a relation whose fact type is `s`. */
  case Struct(fact: Boolean)

/** A top-level entity. `ty` is its type (closed), `stage` the stage of its type's universe, `span` the
 *  position of its name and `declSpan` that of its whole declaration.
 *
 *  An object relation, constructor or struct may be *pending*: declared before its declaration is
 *  elaborated, so that object declarations can refer to each other in cycles (`abs : (body : term) ->
 *  rel.  term : type = var | abs.`). A pending constant can only be used as a type (its fact type); its
 *  type is the placeholder `rel` until its declaration sets the real one (see
 *  [[elab.ObjectDecls.predeclare]]). Only the declaration phase sees pending constants. */
final class GlobalEntry(
    val name: Name,
    var ty: Val,
    var tyTm: Tm,
    val stage: Stage,
    var kind: GlobalKind,
    val span: Span,
    val declSpan: Span = Span.NoSpan,
    var pending: Boolean = false,
    /** For an instance of a family: the family and the (closed, normal) arguments. */
    val instanceOf: Option[(Int, List[Tm])] = None
)

/** A metavariable: its type is closed (a Π over the context it was created in, as in elaboration-zoo).
 *  `what` describes it for diagnostics; metas with `allowUnsolved` (the types of object variables, which
 *  the object typer infers) may stay unsolved. */
final class MetaEntry(val ty: Val, val stage: Stage, val span: Span, val what: String, var allowUnsolved: Boolean):
  var solution: Option[Val] = None

/** The state shared by evaluation, unification and elaboration: globals, metavariables and universe
 *  levels. One `Core` elaborates one program. */
final class Core extends Evaluation with Matching with Families with Readback with Renaming with Unification with Printing:
  val levels: Levels = Levels()
  val globals: mutable.ArrayBuffer[GlobalEntry] = mutable.ArrayBuffer.empty
  val metas: mutable.ArrayBuffer[MetaEntry] = mutable.ArrayBuffer.empty

  def addGlobal(e: GlobalEntry): Int =
    globals += e
    globals.length - 1

  def newMeta(ty: Val, st: Stage, span: Span, what: String, allowUnsolved: Boolean = false): Int =
    metas += MetaEntry(ty, st, span, what, allowUnsolved)
    metas.length - 1

  def solveMeta(m: Int, v: Val): Unit = metas(m).solution = Some(v)

  /** Runs `f` and restores the metas and universe levels afterwards, whatever happens: for staging a
   *  generic item at an instance (its unknowns are solved for the instance only). */
  def tentatively[A](f: => A): A =
    val count = metas.length
    val solutions = metas.map(_.solution).toVector
    val lv = levels.snapshot()
    try f
    finally
      metas.dropRightInPlace(metas.length - count)
      metas.zip(solutions).foreach((m, s) => m.solution = s)
      levels.restore(lv)

  /** Runs `f`; if it throws, the metas and universe levels are restored to their state before (metas
   *  created by `f` are removed, solutions it found are undone), and the exception is rethrown. */
  def undoOnFailure[A](f: => A): A =
    val count = metas.length
    val solutions = metas.map(_.solution).toVector
    val lv = levels.snapshot()
    try f
    catch
      case e: Throwable =>
        metas.dropRightInPlace(metas.length - count)
        metas.zip(solutions).foreach((m, s) => m.solution = s)
        levels.restore(lv)
        throw e
