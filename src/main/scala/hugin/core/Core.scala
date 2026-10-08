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
 *  position of its name and `declSpan` that of its whole declaration. */
final class GlobalEntry(
    val name: Name,
    val ty: Val,
    val tyTm: Tm,
    val stage: Stage,
    var kind: GlobalKind,
    val span: Span,
    val declSpan: Span = Span.NoSpan
)

/** A metavariable: its type is closed (a Π over the context it was created in, as in elaboration-zoo).
 *  `what` describes it for diagnostics; metas with `allowUnsolved` (the types of object variables, which
 *  the object typer infers) may stay unsolved. */
final class MetaEntry(val ty: Val, val stage: Stage, val span: Span, val what: String, val allowUnsolved: Boolean):
  var solution: Option[Val] = None

/** The state shared by evaluation, unification and elaboration: globals, metavariables and universe
 *  levels. One `Core` elaborates one program. */
final class Core extends Evaluation with Matching with Readback with Renaming with Unification with Printing:
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
