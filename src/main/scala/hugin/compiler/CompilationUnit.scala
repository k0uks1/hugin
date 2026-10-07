package hugin.compiler

import hugin.util.SourceFile
import hugin.syntax.Program
import hugin.meta.{MExpr, Scope, ScopeKey, SymKeys, TypingResults}
import hugin.obj.*
import scala.collection.mutable

/** Everything the compiler knows about one source program; each phase fills in its part. */
final class CompilationUnit(val source: SourceFile):
  var untpd: Program | Null = null

  /** The prelude and the imported files, keyed by resolved path, in dependency order (prelude first). */
  val libraries: mutable.LinkedHashMap[String, Library] = mutable.LinkedHashMap.empty

  /** Resolved paths of imports that were not found. */
  val missingImports: mutable.Set[String] = mutable.HashSet.empty

  var rootScope: Scope | Null = null

  /** The program's top level after naming (its scope is `rootScope`). */
  var named: NamedProgram | Null = null

  /** Scopes of nested module bodies, in elaboration order. */
  val scopes: mutable.LinkedHashMap[ScopeKey, Scope] = mutable.LinkedHashMap.empty

  /** The keys of all meta-level symbols created so far, to check that they are unique. */
  val symKeys: SymKeys = SymKeys()
  var elab: MExpr | Null = null

  /** Typing results of the meta level (filled by the typer). */
  var symbols: TypingResults = TypingResults.empty

  /** Object program after meta evaluation (may still contain families). */
  var generic: ObjProgram | Null = null

  /** The object program, transformed in place by the object-level phases. */
  var prog: ObjProgram | Null = null

  /** Directives of the relations of `prog` (from `directives` on; see [[ProgramFacts]]). */
  var facts: ProgramFacts = ProgramFacts.empty

  /** Typing contexts computed by `objTyper`, keyed by rule/query identity. */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, OType]] = java.util.IdentityHashMap()

  /** Signature requirements (Section 4.4) recorded by `metaEval`, checked by `directives`. */
  var requirements: List[RequirementCheck] = Nil

  /** Relations that may be incomplete (Section 6.5), computed by `completeness`. */
  var incomplete: Set[RelSym] = Set.empty
  var core: hugin.ir.CoreProgram | Null = null
  var components: List[List[RelSym]] = Nil

  /** The split rules of Proposition 8.8 added by `stratify` (by identity; see `StratifyPhase.splitRules`). */
  val splitRules: java.util.Set[AnyRef] = java.util.Collections.newSetFromMap(java.util.IdentityHashMap())

  /** Positions → symbols and types, for tooling. */
  val index: SemanticIndex = SemanticIndex()

  /** Reports requested by settings (`--explain-termination`), printed with the compiler's output. */
  val explanations: mutable.ListBuffer[String] = mutable.ListBuffer.empty

  /** Rules named by `%derivations @r`. */
  val derivationRules: mutable.Set[String] = mutable.LinkedHashSet.empty
