package hugin.core

import hugin.util.Span
import scala.collection.mutable

/** What a global is. */
enum GlobalKind:
  /** A meta-level constant without a value: stuck at compile time. After elaboration, it is a deliberate
   *  axiom `x : A = %postulate.` ([[GlobalEntry.axiom]]); during elaboration it is also the state of a
   *  formula function before its rules, and of a definition whose body is withheld. */
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

  /** `Sym`, the builtin meta type of references to object constants (reference: reflection): its
   *  values are quoted object constants `⟨r⟩`, compared by identity (`Sym : Type = %builtin symbol.`). */
  case Symbols

  /** A function defined by clauses: its case tree over its first `arity` arguments, with its clauses
   *  (both known once its clauses are elaborated; arity -1 before). */
  case Function(arity: Int, tree: Option[FunctionBody])

  /** A definition or a function by clauses made opaque by `%opaque x.` (reference: meta/index): checked
   *  once, then neutral like a postulate. It never unfolds, and a definition's value is never computed.
   *  `term` is a definition's term, `function` a function's arity and case tree: kept for the checks that
   *  follow calls through definitions (termination), for tooling and for the summary of declarations. */
  case Opaque(term: Option[Tm], function: Option[(Int, FunctionBody)])

  /** A primitive operation of the prelude (`eqsym : sym -> sym -> bool = %builtin eqsym.`), reduced by
   *  [[Primitives]]; `ctors` are the constructors of its result type it builds (`true`, `false`; `nil`,
   *  `cons`). */
  case Primitive(op: PrimOp, ctors: List[Int])

/** What an object constant declares (reference: object/index). The core only needs to know that it is an object
 *  constant; the handover to the object level ([[hugin.core.handover]]) needs the rest. */
enum ObjDecl:
  /** `a : type.` */
  case OpenType

  /** `a : type <: b.`, a nominal refinement of the object type `base`. */
  case Refinement(base: Tm)

  /** `r : τ̄ -> rel.` */
  case Relation

  /** `c : τ̄ -> a.`: a fact constructor (reference: object/facts), also the relation of its facts. */
  case Constructor

  /** `s : type = { l : τ, … }.`: a relation whose fact type is `s`. */
  case Struct

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
    val instanceOf: Option[(Int, List[Tm])] = None,
    /** Where the constant is placed in the object program (the object level orders the members of a
     *  closed type by symbol id): its declaration, or the item that created a module instance. */
    val placedAt: Span = Span.NoSpan,
    /** For a lambda-lifted function (of a `where` block or a module body, [[elab.Lifting]]): the number
     *  of its leading arguments that are the variables of the context it was lifted from. Users do not
     *  write them, so diagnostics and printing leave them out. */
    val hidden: Int = 0,
    /** For the function a `match` elaborates to ([[elab.Matches]]): printed as the `match` it stands for. */
    val matchFunction: Boolean = false
):
  /** For a constant of a shared data declaration (`list A : data.`): its side and the constant of the
   *  same name at the other stage ([[SharedLink]]). */
  var shared: Option[SharedLink] = None

  /** A function, definition or formula function of the component of the file's dependency graph being
   *  elaborated: its body does not unfold until the component is done ([[elab.ElabOrder]]; reference:
   *  meta/index, "Order of elaboration"). Its definition or case tree is withheld until then (it is a
   *  postulate or a function without a case tree, [[elab.DependencyOrder.withheld]]), so evaluation
   *  needs no test. */
  var inCycle: Boolean = false

  /** A deliberate axiom `x : A = %postulate.` (a [[GlobalKind.Postulate]]): rejected by `--safe` and
   *  listed by `--print-assumptions` (reference: meta/functions, "Postulates"). */
  var axiom: Boolean = false

  /** For an inductive family: the number of its leading arguments that every constructor keeps fixed, its
   *  parameters (reference: meta/families, "Parameters"); -1 while it has no constructors (then all its
   *  arguments are). */
  var parameters: Int = -1

/** The link between the two constants a shared data declaration declares under one name (reference:
 *  meta/families, shared data): the meta inductive family (or meta constructor) at `side` S1, the
 *  object family, type or constructor at `side` S0. On the meta family, `lift` and `reify` are the
 *  derived functions `T.lift` and `T.reify` once they are declared (-1 before; `reify` stays -1 without
 *  the reflective types of the prelude). */
final class SharedLink(val side: Stage, val counterpart: Int):
  var lift: Int = -1
  var reify: Int = -1

/** A metavariable: its type is closed (a Π over the context it was created in, as in elaboration-zoo).
 *  `what` describes it for diagnostics; metas with `allowUnsolved` (the types of object variables, which
 *  object typing infers) may stay unsolved. */
final class MetaEntry(val ty: Val, val stage: Stage, val span: Span, val what: String, initiallyAllowUnsolved: Boolean):
  private var solved: Option[Val] = None
  private var allowed = initiallyAllowUnsolved
  def solution: Option[Val] = solved
  def allowUnsolved: Boolean = allowed

  /** Only [[Core]] changes entries (it copies an entry shared with a fork first). */
  private[core] def solution_=(v: Option[Val]): Unit = solved = v
  private[core] def allowUnsolved_=(b: Boolean): Unit = allowed = b

  private[core] def copy(): MetaEntry =
    val e = MetaEntry(ty, stage, span, what, allowed)
    e.solved = solved
    e

/** The state shared by evaluation, unification and elaboration: globals, metavariables and universe
 *  levels. One `Core` elaborates one program. */
final class Core private (val levels: Levels) extends Evaluation with Machine with Matching with Families with Modules with Requirements
    with Readback with Renaming with Unification with Printing with Primitives with MemoKeys
    with Naturals
    with Integers
    with NatArithmetic:
  def this() = this(Levels())

  /** The reads of a program's declarations made in this core (the fork in which one object item is
   *  elaborated, [[ProgramElab.item]]), if they are observed ([[DeclarationReads]]). */
  var reads: DeclarationReads | Null = null

  /** Observes the reads of the declarations made in this core (and its universe levels), or stops. */
  def observe(r: DeclarationReads | Null): Unit =
    reads = r
    levels.reads = if r == null then Levels.ignore else r.level

  /** Reports a read of a whole table of the core to the observer, if any. */
  def readAll(channel: String): Unit = { val r = reads; if r != null then r.all(channel) }

  val globals: Entries[GlobalEntry] = Entries(i => { val r = reads; if r != null then r.global(i) }, () => readAll("globals"))
  val metas: Entries[MetaEntry] = Entries(i => { val r = reads; if r != null then r.meta(i) }, () => readAll("metas"))

  /** A copy of this core that can be extended independently (the elaboration of one item against the
   *  declarations of its program, [[ProgramElab]]). The globals are shared: an elaboration only changes
   *  the globals it declares (a fork's own), so the entries of this core stay as they are. The metas are
   *  shared copy-on-write ([[ownMeta]]): both cores copy an entry before they change it, so neither sees
   *  the other's solutions, as with a full copy, at the cost of the entries changed. */
  def fork(): Core =
    val c = Core(levels.copy())
    c.globals ++= globals
    c.edges = edges
    c.relInfoCache ++= relInfoCache
    c.metas ++= metas
    sharedBelow = metas.length
    owned.clear()
    c.sharedBelow = metas.length
    c.copyFamilies(this)
    c.copyModules(this)
    c.copyRequirements(this)
    c.copyEvaluation(this)
    c.copyPrimitives(this)
    c.copyIntegers(this)
    c

  /** The metas below this index may be shared with forks (or with the core this one was forked from),
   *  except those in [[owned]], already copied by this core. */
  private var sharedBelow = 0
  private val owned = mutable.BitSet.empty

  /** The entry of meta `m`, copied first if it is shared: the entry this core may change. */
  private def ownMeta(m: Int): MetaEntry =
    if m < sharedBelow && !owned(m) then
      metas(m) = metas(m).copy()
      owned += m
    metas(m)

  /** Lets meta `m` stay unsolved (the unknown types of object variables). */
  def allowUnsolved(m: Int): Unit = ownMeta(m).allowUnsolved = true

  /** The subtyping edges `τ <: a` of the program and its libraries (closed `τ`, the open type `a`), for
   *  object typing ([[objtype.ObjEnv]]); the handover adds those of module instances. */
  private var edges: List[(Val, Int)] = Nil
  def objEdges: List[(Val, Int)] =
    readAll("objEdges")
    edges
  def objEdges_=(es: List[(Val, Int)]): Unit = edges = es
  private[core] def edgesTable: List[(Val, Int)] = edges

  /** The columns of object constants as object typing sees them ([[objtype.ObjEnv.relInfo]]). */
  val relInfoCache: mutable.HashMap[Int, Option[AnyRef]] = mutable.HashMap.empty

  private var relationIds: List[Int] = Nil
  private var relationsSeen = 0

  /** The relations, constructors and structs among the globals (also instances of families). */
  def relationGlobals: List[Int] =
    if relationsSeen < globals.length then
      val more = (relationsSeen until globals.length).filter { id =>
        globals(id).kind match
          case GlobalKind.Object(d) => d != ObjDecl.OpenType && !d.isInstanceOf[ObjDecl.Refinement]
          case _ => false
      }
      relationIds = relationIds ++ more
      relationsSeen = globals.length
    relationIds.filterNot(globals(_).pending)

  def addGlobal(e: GlobalEntry): Int =
    globals += e
    globals.length - 1

  def newMeta(ty: Val, st: Stage, span: Span, what: String, allowUnsolved: Boolean = false): Int =
    metas += MetaEntry(ty, st, span, what, allowUnsolved)
    metas.length - 1

  // ------------------------------------------------------------------ blocks and frozen metas

  /** Metas below this index are *frozen*: created before the top-level block being elaborated (a
   *  declaration, a clause group, an object item), so unification never solves or prunes them; they are
   *  rigid unknowns (reference: meta/functions, a hole is constrained by its item only). 0 outside blocks:
   *  staging solves the unknowns of a generic item for an instance. */
  private var frozen = 0
  private var blockDepth = 0

  /** The number of metas when the current (or last) block started: unknowns print relative to it. */
  var blockStart = 0

  def isFrozen(m: Int): Boolean = m < frozen

  /** Runs `f` as a block: the metas that exist now are frozen while it runs. Blocks nest (the clauses of
   *  a function of a module body are a block inside the item of the body): when an inner block ends, the
   *  frozen metas and the start of the enclosing block are restored. */
  def inBlock[A](f: => A): A =
    val (savedFrozen, savedStart) = (frozen, blockStart)
    blockDepth += 1
    frozen = metas.length
    blockStart = metas.length
    try f
    finally
      blockDepth -= 1
      frozen = savedFrozen
      // after a top-level block, unknowns keep printing relative to it (the last block)
      if blockDepth > 0 then blockStart = savedStart

  def solveMeta(m: Int, v: Val): Unit =
    if m < frozen then throw UnifyError(UnifyFailure.Frozen(m))
    if openCheckpoints > 0 then trail += ((m, metas(m).solution))
    ownMeta(m).solution = Some(v)

  // ------------------------------------------------------------------ backtracking

  /** The solutions changed since the oldest open checkpoint, with their values before: undoing them
   *  restores the metas (a trail, as in Prolog's WAM and Lean 4's restorable meta context; a snapshot of
   *  every solution cost the number of metas at every checkpoint). */
  private val trail = mutable.ArrayBuffer.empty[(Int, Option[Val])]
  private var openCheckpoints = 0

  private final class Checkpoint(val metaCount: Int, val at: Int, val levels: Levels.Checkpoint, val logged: Int)

  private def checkpoint(): Checkpoint =
    openCheckpoints += 1
    Checkpoint(metas.length, trail.length, levels.checkpoint(), toolingLog.length)

  /** What the elaborator records for tooling once the unknowns of the item are solved (types shown with
   *  their solutions, inserted implicit arguments, goals): run by the elaborator at the end of each item
   *  (`true` if it succeeded). Rolled back with the metas, so that an attempt that was undone (a
   *  declaration tried at the other stage) leaves nothing behind. A fork starts with an empty log. */
  val toolingLog: mutable.ArrayBuffer[Boolean => Unit] = mutable.ArrayBuffer.empty

  /** Returns to the state at `c`: metas created since are removed, solutions found since undone. */
  private def rollback(c: Checkpoint): Unit =
    while trail.length > c.at do
      val (m, old) = trail.remove(trail.length - 1)
      if m < c.metaCount then ownMeta(m).solution = old
    metas.dropRightInPlace(metas.length - c.metaCount)
    toolingLog.dropRightInPlace(toolingLog.length - c.logged.min(toolingLog.length))
    owned.filterInPlace(_ < c.metaCount)
    levels.rollback(c.levels)
    close()

  private def commit(c: Checkpoint): Unit =
    levels.commit(c.levels)
    close()

  private def close(): Unit =
    openCheckpoints -= 1
    if openCheckpoints == 0 then trail.clear()

  /** Runs `f` and restores the metas and universe levels afterwards, whatever happens: for staging a
   *  generic item at an instance (its unknowns are solved for the instance only). */
  def tentatively[A](f: => A): A =
    val c = checkpoint()
    try f
    finally rollback(c)

  /** Runs `f`; if it throws, the metas and universe levels are restored to their state before (metas
   *  created by `f` are removed, solutions it found are undone), and the exception is rethrown. */
  def undoOnFailure[A](f: => A): A =
    val c = checkpoint()
    val result =
      try f
      catch
        case e: Throwable =>
          rollback(c)
          throw e
    commit(c)
    result

/** The globals or metas of a core: entries by position whose reads are reported to the core's observer
 *  ([[Core.reads]]): one entry by `read`, all of them (an iteration) by `readAll`. */
final class Entries[A](read: Int => Unit, readAll: () => Unit):
  private val buf = mutable.ArrayBuffer.empty[A]
  def apply(i: Int): A =
    read(i)
    buf(i)
  def update(i: Int, a: A): Unit = buf(i) = a
  def length: Int = buf.length
  def indices: Range = buf.indices
  def +=(a: A): this.type =
    buf += a
    this
  def ++=(other: Entries[A]): this.type =
    buf ++= other.buf
    this
  def dropRightInPlace(n: Int): Unit = buf.dropRightInPlace(n)
  def toList: List[A] =
    readAll()
    buf.toList
  def filter(p: A => Boolean): List[A] = toList.filter(p)
