package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** An elaboration error: reported, and the item it occurred in is dropped. `unresolved` names the name
 *  whose resolution failed, for errors that a later declaration may fix. */
final class ElabError(val diag: Diagnostic, val unresolved: Option[Name] = None)
    extends Exception(diag.message, null, false, false)

/** The module value of an imported file: a record of its declarations (closed terms). */
final case class ImportedModule(value: Tm, ty: Tm)

/** Where the items of a file are elaborated: its path, the qualifier of its object constants' names
 *  (`shapes.dot` in the imported file `shapes.hgn`; none in the program and the prelude), the names
 *  qualified with `prelude` instead (the prelude's declarations the program redeclares), the names of
 *  the enclosing scope (the prelude's), and the module values of the files it may import. */
final case class FileEnv(
    path: String = "",
    qualifier: String = "",
    shadowed: Set[Name] = Set.empty,
    parent: Map[Name, Int] = Map.empty,
    imports: Map[String, ImportedModule] = Map.empty,
    /** Whether unused definitions are reported (W0003, in the program, not in libraries). */
    lintUnused: Boolean = false
):
  /** The name of an object constant declared as `n`. */
  def objectName(n: Name): Name =
    val q = if shadowed(n) then "prelude" else qualifier
    if q.isEmpty then n else s"$q.$n"

/** What an elaboration has produced so far: the top-level names in scope and the elaborated items. */
final class ElabState:
  val scope: mutable.LinkedHashMap[Name, Int] = mutable.LinkedHashMap.empty
  val items: mutable.ListBuffer[CoreItem] = mutable.ListBuffer.empty

  /** What a term whose type is still unknown denotes when it is used as a type: a meta type (the
   *  default) or an object type. Declarations try both for their implicit binders (see
   *  [[Declarations.declType]]). */
  var unknownTypesAre: Stage = Stage.S1

  /** The names defined by clauses in the module: their declarations declare functions. */
  var functionNames: Set[Name] = Set.empty

  /** The signatures declared in the file as written (`g : Type = { … }.`), for suggestions. */
  var signatures: Map[Name, hugin.syntax.Trees.RecordType] = Map.empty

  /** The globals that names resolved to (for W0003, unused definitions). */
  val used: mutable.Set[Int] = mutable.HashSet.empty

  /** Whether a type (rather than a term) is being elaborated: a struct family is a type family in a type
   *  (`pair int string`) and a constructor with implicit type arguments in a term (`pair 1 "x"`). */
  var typePosition: Boolean = false

  /** Whether a rule head is being elaborated (named patterns in heads must give every column). */
  var objectHead: Boolean = false

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
 *  - [[Contexts]], [[Names]], [[ElabErrors]]: contexts and metas, name resolution, diagnostics.
 */
class Elaborator(val core: Core, val reporter: Reporter, val file: FileEnv = FileEnv())
    extends Contexts
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
    with DataConstructors
    with FormulaFunctions
    with ModuleBodies
    with Imports
    with CompleteParameters
    with ObjectItems:
  val state: ElabState = ElabState()
  def scope: mutable.LinkedHashMap[Name, Int] = state.scope
  def items: mutable.ListBuffer[CoreItem] = state.items
