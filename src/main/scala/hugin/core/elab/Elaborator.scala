package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** An elaboration error: reported, and the item it occurred in is dropped. `unresolved` names the name
 *  whose resolution failed, for errors that a later declaration may fix. */
final class ElabError(val diag: Diagnostic, val unresolved: Option[Name] = None, val silent: Boolean = false)
    extends Exception(diag.message, null, false, false)

/** The module value of an imported file: a record of its declarations (closed terms); `dropped` are the
 *  names whose declarations were dropped for an error in the file (their uses are not reported again). */
final case class ImportedModule(value: Tm, ty: Tm, dropped: Set[Name] = Set.empty)

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
    builtinNames: Boolean = true
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

  /** The names the file's declarations and definitions declare (they shadow the prelude's in the whole
   *  file, also before their declarations). */
  var declaredHere: Set[Name] = Set.empty

  /** The names defined by clauses in the module: their declarations declare functions. */
  var functionNames: Set[Name] = Set.empty

  /** The signatures declared in the file as written (`g : Type = { … }.`), for suggestions. */
  var signatures: Map[Name, hugin.syntax.Trees.RecordType] = Map.empty

  /** Names whose declarations were dropped for an error (reported, or an erroneous import): their uses
   *  drop the items using them without further errors. */
  var erroneous: Set[Name] = Set.empty

  /** What the object items elaborated so far contribute to the module (for module-wide directives). */
  val parts: mutable.ListBuffer[ModulePart] = mutable.ListBuffer.empty

  /** The globals that names resolved to (for W0003, unused definitions). */
  var used: Set[Int] = Set.empty

  /** Whether a type (rather than a term) is being elaborated: a struct family is a type family in a type
   *  (`pair int string`) and a constructor with implicit type arguments in a term (`pair 1 "x"`). */
  var typePosition: Boolean = false

  /** Whether a rule head is being elaborated (named patterns in heads must give every column). */
  var objectHead: Boolean = false

  /** A copy for the elaboration of one item against the declarations elaborated so far (its own items
   *  start empty). The names and sets are persistent, so a copy is cheap (issue #60). */
  def fork(): ElabState =
    val s = ElabState(scope.copy())
    s.functionNames = functionNames
    s.declaredHere = declaredHere
    s.signatures = signatures
    s.erroneous = erroneous
    s.used = used
    s

/** Bidirectional elaboration of surface trees into the core (docs/REDESIGN.md §6), following Kovács's
 *  elaboration-zoo and his staged elaborator. The concerns are split into traits:
 *
 *  - [[Bidirectional]]: `check`/`infer` dispatch; [[PiTypes]]: object arrows, meta and implicit Π;
 *    [[Applications]]: lambdas, applications and the insertion of implicit applications (implicit
 *    arguments are metas solved by higher-order pattern unification, [[hugin.core.Unification]]);
 *  - [[Coercions]]: **stage inference** — every term has a stage (the stage of its type's universe); where
 *    the expected stage differs, quotes `⟨t⟩`, splices `$t` and lifts `⇑A` are inserted, and checking
 *    against `⇑A` checks object code at stage 0 under a quote (Kovács, ICFP 2022, §4); **cross-stage
 *    persistence** of primitive values; record subtyping by coercion;
 *  - [[Universes]]: `type` (object types) and `Type` (meta types, levels inferred and cumulative);
 *  - [[Records]]: dependent records and projections; [[Operators]]: arithmetic and formulas;
 *  - [[Items]], [[Declarations]], [[ObjectItems]]: items, declarations and definitions, rules and queries;
 *  - [[Inductives]]: inductive families, constructors, positivity, nat literals; [[Patterns]],
 *    [[Clauses]], [[IndexUnifier]]: functions defined by clauses, elaborated into case trees with
 *    coverage checking; [[SizeChange]]: their termination;
 *  - [[Contexts]], [[Names]], [[ElabErrors]]: contexts and metas, name resolution, diagnostics;
 *  - [[Reflective]], [[Quotes]], [[QuotedPatterns]], [[Reflection]]: object syntax as data (REDESIGN
 *    §6.8–6.9): the prelude's reflective types, reification of quoted syntax in expressions and
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
    with Items
    with Declarations
    with Inductives
    with Patterns
    with IndexUnifier
    with Clauses
    with SizeChange
    with Where
    with ObjectDecls
    with ObjectCode
    with NamedPatterns
    with FormulaFunctions
    with ModuleBodies
    with Imports
    with CompleteParameters
    with ObjectItems
    with Reflective
    with Quotes
    with QuotedPatterns
    with Reflection
    with Directives
    with ModuleDirectives
    with Tooling:
  /** An elaborator over `core` (a fork of this one's) that continues from this one's declarations. */
  def fork(core: Core, reporter: Reporter, index: hugin.compiler.SemanticIndex): Elaborator =
    Elaborator(core, reporter, file, index, state.fork())
  def scope: NameScope = state.scope
  def items: mutable.ListBuffer[CoreItem] = state.items
