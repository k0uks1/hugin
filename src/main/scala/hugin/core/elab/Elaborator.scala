package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** An elaboration error: reported, and the item it occurred in is dropped. `unresolved` names the name
 *  whose resolution failed, for errors that a later declaration may fix. */
final class ElabError(val diag: Diagnostic, val unresolved: Option[Name] = None)
    extends Exception(diag.message, null, false, false)

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
class Elaborator(val core: Core, val reporter: Reporter)
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
    with ObjectItems:
  val state: ElabState = ElabState()
  def scope: mutable.LinkedHashMap[Name, Int] = state.scope
  def items: mutable.ListBuffer[CoreItem] = state.items
