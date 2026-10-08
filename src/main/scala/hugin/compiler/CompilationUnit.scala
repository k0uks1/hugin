package hugin.compiler

import hugin.util.SourceFile
import hugin.syntax.Program
import hugin.obj.*
import scala.collection.mutable

/** Everything the compiler knows about one source program; each phase fills in its part. */
final class CompilationUnit(val source: SourceFile):
  var untpd: Program | Null = null

  /** The prelude and the imported files, keyed by resolved path, in dependency order (prelude first). */
  val libraries: mutable.LinkedHashMap[String, Library] = mutable.LinkedHashMap.empty

  /** Resolved paths of imports that were not found. */
  val missingImports: mutable.Set[String] = mutable.HashSet.empty

  /** The program elaborated by the meta level (filled by `elaborate`). */
  var elaborated: hugin.core.Elaborated | Null = null

  /** The object program, transformed in place by the object-level phases (from `stage` on). */
  var prog: ObjProgram | Null = null

  /** Directives of the relations of `prog` (from `directives` on; see [[ProgramFacts]]). */
  var facts: ProgramFacts = ProgramFacts.empty

  /** Typing contexts computed by `objTyper`, keyed by rule/query identity. */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, OType]] = java.util.IdentityHashMap()

  /** Signature requirements (REDESIGN §6.7) recorded by staging, checked by `directives`. */
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
