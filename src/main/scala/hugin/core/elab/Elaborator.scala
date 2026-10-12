package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** An elaboration error: reported, and the item it occurred in is dropped. `unresolved` names the name
 *  whose resolution failed, for errors that a later declaration may fix. */
final class ElabError(val diag: Diagnostic, val unresolved: Option[Name] = None, val silent: Boolean = false)
    extends Exception(diag.message, null, false, false)

/** The module value of an imported file: a record of its declarations (closed terms); `dropped` are the
 *  names whose declarations were dropped for an error in the file (their uses are not reported again);
 *  `operators` are its operators bound to meta functions (`%infix + plus.`), each symbol with the global
 *  it denotes: a file in which that global is in scope may use the symbol for it ([[Overloading]]). */
final case class ImportedModule(value: Tm, ty: Tm, dropped: Set[Name] = Set.empty, operators: List[(String, Int)] = Nil)

/** Where the items of a file are elaborated: its path, the qualifier of its object constants' names
 *  (`shapes.dot` in the imported file `shapes.hgn`; none in the program and the prelude), the names of
 *  the enclosing scope (the prelude's), and the module values of the files it may import. */
final case class FileEnv(
    path: String = "",
    qualifier: String = "",
    parent: Map[Name, Int] = Map.empty,
    imports: Map[String, ImportedModule] = Map.empty,
    /** Whether unused definitions are reported (W0003, in the program, not in libraries). */
    lintUnused: Boolean = false,
    /** Whether `int`, `float` and `string` are in scope without a declaration: in core tests, not in a
     *  compilation without the prelude (which declares them). */
    builtinNames: Boolean = true,
    /** Whether only the declarations are elaborated, without the clauses of functions and `%export`: their
     *  kinds and types, which tell whether a file declares object constants (a lazy re-export,
     *  [[hugin.compiler.LazyStdlib]]). */
    signaturesOnly: Boolean = false
):
  /** The name of an object constant declared as `n`. */
  def objectName(n: Name): Name =
    if qualifier.isEmpty then n else s"$qualifier.$n"

/** What an elaboration has produced so far: the top-level names in scope and the elaborated items. */
final class ElabState(val scope: NameScope = NameScope()):
  val items: mutable.ListBuffer[CoreItem] = mutable.ListBuffer.empty

  /** What a term whose type is still unknown denotes when it is used as a type: a meta type (the
   *  default) or an object type. Declarations try both for their implicit binders (see
   *  [[Declarations.declType]]). */
  var unknownTypesAre: Stage = Stage.S1

  /** The reads of the declarations made in this state (the fork in which one item is elaborated), if
   *  they are observed ([[hugin.core.DeclarationReads]]). */
  private var reads: hugin.core.DeclarationReads | Null = null

  /** The tables of the state, without reporting a read ([[hugin.core.DeclarationsSummary]]). */
  private[core] def tables: (
      Map[Name, List[(Int, hugin.util.Span)]],
      Option[(hugin.util.Span, ImportedModule)],
      Map[Name, hugin.syntax.Trees.RecordType],
      Option[Option[Set[Name]]],
      List[(String, Name)]
  ) =
    (opened0, exported0, signatures0, droppedUses0, operatorNames0)

  def observe(r: hugin.core.DeclarationReads | Null): Unit =
    reads = r
    scope.reads = r

  private def readAll(channel: String): Unit = { val r = reads; if r != null then r.all(channel) }

  /** A set of names of the state whose membership tests are reads of the declarations, name by name. */
  final class Names(channel: String):
    private[ElabState] var names: Set[Name] = Set.empty
    def apply(n: Name): Boolean =
      val r = reads
      if r != null then r.name(channel, n)
      names(n)
    def +=(n: Name): Unit = names += n
    def ++=(ns: IterableOnce[Name]): Unit = names ++= ns
    def set(ns: Set[Name]): Unit = names = ns
    def toSet: Set[Name] =
      readAll(channel)
      names
    def foreach[U](f: Name => U): Unit = toSet.foreach(f)
    private[ElabState] def copyFrom(other: ElabState#Names): Unit = names = other.names

    /** The names, without reporting a read ([[hugin.core.DeclarationsSummary]]). */
    private[core] def unobserved: Set[Name] = names

  /** The names the file's declarations and definitions declare (they shadow the prelude's in the whole
   *  file, also before their declarations). */
  val declaredHere: Names = Names("declaredHere")

  /** The names the members of the module bodies being elaborated declare: they shadow the file's in the
   *  whole body, also before their declarations ([[ModuleBodies]]). */
  var bodyDeclared: Set[Name] = Set.empty

  /** Why a name of the file or of a body being elaborated is program-dependent, if it is: its declaration
   *  is elaborated after the scope's object items, and a use before is E0962 ([[ProgramPhase]]). A read
   *  of the declarations, name by name. */
  def dependence(n: Name): Option[ProgramPhase.Dependence] =
    val r = reads
    if r != null then r.name("programDependent", n)
    programDependent0.get(n)
  def programDependent: Map[Name, ProgramPhase.Dependence] = programDependent0
  def programDependent_=(m: Map[Name, ProgramPhase.Dependence]): Unit = programDependent0 = m
  private[core] var programDependent0: Map[Name, ProgramPhase.Dependence] = Map.empty

  /** The members (name, level) of the module bodies being elaborated that are left out although bound: the
   *  formula functions of a cycle (E0105). Their uses drop the items using them without further errors. */
  var leftOutMembers: Set[(Name, Int)] = Set.empty

  /** The names that the file's `%opaque` directives name (reference: meta/index): its definitions and
   *  functions of these names are opaque. */
  var opaque: Set[Name] = Set.empty

  /** The file's operators bound to meta functions, `%infix op f.` (reference: lexical-structure): each
   *  symbol with the name of the file's function it denotes, in source order ([[Overloading]]). */
  def operatorNames: List[(String, Name)] =
    readAll("operators")
    operatorNames0
  def operatorNames_=(o: List[(String, Name)]): Unit = operatorNames0 = o
  private var operatorNames0: List[(String, Name)] = Nil

  /** The names defined by clauses in the module: their declarations declare functions. */
  val functionNames: Names = Names("functionNames")

  /** The names of the file's declarations without a definition, clauses or rules: one that declares a meta
   *  function (not a family or a constructor) declares a function defined by no clauses, which must cover
   *  its arguments as any other ([[Items.checkClauseless]]; reference: meta/clauses). */
  var clauseless: Set[Name] = Set.empty

  /** The names opened by `%use` (reference: modules), with the globals they denote and the `%use` items
   *  that opened them: between the file's declarations and the enclosing scope. A name opened for two
   *  different globals is ambiguous ([[Uses]]). */
  def opened: Map[Name, List[(Int, hugin.util.Span)]] =
    readAll("opened")
    opened0
  def opened_=(o: Map[Name, List[(Int, hugin.util.Span)]]): Unit = opened0 = o
  private var opened0: Map[Name, List[(Int, hugin.util.Span)]] = Map.empty

  /** The file's `%export` (reference: modules): its span, and the module value and type it exports. */
  def exported: Option[(hugin.util.Span, ImportedModule)] =
    readAll("exported")
    exported0
  def exported_=(e: Option[(hugin.util.Span, ImportedModule)]): Unit = exported0 = e
  private var exported0: Option[(hugin.util.Span, ImportedModule)] = None

  /** The signatures declared in the file as written (`g : Type = { … }.`), for suggestions. */
  def signatures: Map[Name, hugin.syntax.Trees.RecordType] =
    readAll("signatures")
    signatures0
  def signatures_=(s: Map[Name, hugin.syntax.Trees.RecordType]): Unit = signatures0 = s
  private var signatures0: Map[Name, hugin.syntax.Trees.RecordType] = Map.empty

  /** Names whose declarations were dropped for an error (reported, or an erroneous import): their uses
   *  drop the items using them without further errors. */
  val erroneous: Names = Names("erroneous")

  /** Functions of the file whose clauses failed (a syntax error, or an error reported for them), and what
   *  expands to them: their uses drop the items using them without further errors. */
  val unelaborated: Names = Names("unelaborated")

  /** What the `%use` items that were dropped for an error might have opened: `None` if none was dropped,
   *  `Some(None)` for any name (a `%use m.`), `Some(Some(ns))` for the names `ns` (`%use m (x, y).`). A
   *  name they might have opened is not reported as unresolved: the error is the `%use`'s. */
  def droppedUses: Option[Option[Set[Name]]] =
    readAll("droppedUses")
    droppedUses0
  def droppedUses_=(d: Option[Option[Set[Name]]]): Unit = droppedUses0 = d
  private var droppedUses0: Option[Option[Set[Name]]] = None

  /** Whether an unresolved name `n` might have been opened by a dropped `%use`. */
  def mightBeOpened(n: Name): Boolean = droppedUses.exists(_.forall(_(n)))

  /** What the object items elaborated so far contribute to the module (for module-wide directives). */
  val parts: mutable.ListBuffer[ModulePart] = mutable.ListBuffer.empty

  /** The globals that names resolved to (for W0003, unused definitions). */
  var used: Set[Int] = Set.empty

  /** Whether a type (rather than a term) is being elaborated: a struct family is a type family in a type
   *  (`pair int string`) and a constructor with implicit type arguments in a term (`pair 1 "x"`). */
  var typePosition: Boolean = false

  /** The shared families the file declares, whose `T.lift` and `T.reify` are derived once their
   *  constructors are declared ([[DerivedFunctions]]). */
  var sharedDeclared: List[Int] = Nil

  /** The stage of the position being elaborated (set by `check` and `inferS`, meta outside them): a name
   *  of a shared data declaration denotes its constant at this stage ([[SharedData]]). */
  var stage: Stage = Stage.S1

  /** The subtyping edges of the module body being elaborated (closed over its context), for object
   *  typing ([[ObjectTyping]]). */
  var localEdges: List[(Val, Val)] = Nil

  /** The expansion chain of the code being elaborated (reflected code), for the diagnostics that object
   *  typing reports ([[ObjectTyping]]). */
  var origin: hugin.util.Origin = hugin.util.Origin.Source

  /** Whether a rule head is being elaborated (named patterns in heads must give every column). */
  var objectHead: Boolean = false

  /** A copy for the elaboration of one item against the declarations elaborated so far (its own items
   *  start empty). The names and sets are persistent, so a copy is cheap (issue #60). */
  def fork(): ElabState =
    val s = ElabState(scope.copy())
    s.functionNames.copyFrom(functionNames)
    s.declaredHere.copyFrom(declaredHere)
    s.opaque = opaque
    s.operatorNames0 = operatorNames0
    s.opened0 = opened0
    s.exported0 = exported0
    s.signatures0 = signatures0
    s.erroneous.copyFrom(erroneous)
    s.unelaborated.copyFrom(unelaborated)
    s.droppedUses0 = droppedUses0
    s.programDependent0 = programDependent0
    s.used = used
    s

/** Bidirectional elaboration of surface trees into the core (reference: meta/index), following Kovács's
 *  elaboration-zoo and his staged elaborator. The concerns are split into traits:
 *
 *  - [[Bidirectional]]: `check`/`infer` dispatch; [[PiTypes]]: object arrows, meta and implicit Π;
 *    [[Applications]]: lambdas, applications and the insertion of implicit applications (implicit
 *    arguments are metas solved by higher-order pattern unification, [[hugin.core.Unification]]);
 *  - [[Coercions]]: **stage inference** — every term has a stage (the stage of its type's universe); where
 *    the expected stage differs, quotes `⟨t⟩`, splices `$t` and lifts `⇑A` are inserted, and checking
 *    against `⇑A` checks object code at stage 0 under a quote (Kovács, ICFP 2022, §4); the rule **Lift**
 *    ([[Liftings]]) turns meta values of base and shared types into object code; record subtyping by
 *    coercion;
 *  - [[SharedData]]: shared data declarations `T ā : data.`, a meta family and an object family under one
 *    name, with the derived `T.lift` and `T.reify`;
 *  - [[Universes]]: `type` (object types) and `Type` (meta types, levels inferred and cumulative);
 *  - [[Records]]: dependent records and projections; [[Operators]]: arithmetic and formulas;
 *  - [[Items]], [[Declarations]], [[ObjectItems]]: items, declarations and definitions, rules and queries;
 *  - [[Inductives]]: inductive families, constructors, positivity, nat literals; [[Patterns]],
 *    [[Clauses]], [[IndexUnifier]]: functions defined by clauses, elaborated into case trees with
 *    coverage checking; [[SizeChange]]: their termination;
 *  - [[Contexts]], [[Names]], [[ElabErrors]]: contexts and metas, name resolution, diagnostics;
 *  - [[Reflective]], [[Quotes]], [[QuoteTerms]], [[QuotedPatterns]], [[Reflection]]: object syntax as data
 *    (reference: reflection): the prelude's reflective types, quotes `'( … )` in expressions and
 *    patterns, reflection of data back into object code.
 */
class Elaborator(
    val core: Core,
    val reporter: Reporter,
    val file: FileEnv = FileEnv(),
    val index: hugin.compiler.SemanticIndex = hugin.compiler.SemanticIndex(),
    val state: ElabState = ElabState()
) extends Contexts
    with ElabErrors
    with Names
    with Coercions
    with Bidirectional
    with Universes
    with PiTypes
    with Applications
    with Records
    with Operators
    with Overloading
    with Items
    with ProgramOf
    with Judgments
    with JudgmentCoercion
    with LocaleMembers
    with DependencyOrder
    with Declarations
    with Inductives
    with Patterns
    with IndexUnifier
    with Clauses
    with SizeChange
    with Lifting
    with Where
    with Matches
    with ObjectDecls
    with ObjectCode
    with ObjectTyping
    with NamedPatterns
    with FormulaFunctions
    with ModuleBodies
    with MemberFunctions
    with Imports
    with Uses
    with CompleteParameters
    with ObjectItems
    with Reflective
    with Quotes
    with QuoteTerms
    with QuotedPatterns
    with TypedQuotes
    with Reflection
    with Directives
    with ModuleDirectives
    with SharedData
    with DerivedFunctions
    with Liftings
    with Tooling
    with MetaTooling
    with Holes
    with Literals
    with NativeOperations:
  /** An elaborator over `core` (a fork of this one's) that continues from this one's declarations. */
  def fork(core: Core, reporter: Reporter, index: hugin.compiler.SemanticIndex): Elaborator =
    Elaborator(core, reporter, file, index, state.fork())
  def scope: NameScope = state.scope
  def items: mutable.ListBuffer[CoreItem] = state.items
