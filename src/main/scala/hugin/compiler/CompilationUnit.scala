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

  /** The rules and queries of the object program as staging produced them (for tooling: the expansion
   *  of directives, functor applications and families, `hugin.query.Expansion`). */
  var staged: (Vector[Rule], Vector[Query]) = (Vector.empty, Vector.empty)

  /** Directives of the relations of `prog` (from `directives` on; see [[ProgramFacts]]). */
  var facts: ProgramFacts = ProgramFacts.empty

  /** Typing contexts computed by object typing at the handover (`core/handover/StagedTyping`), keyed by rule/query identity. */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, OType]] = java.util.IdentityHashMap()

  /** The meta global of every object symbol (type, relation, constructor) of `prog`, by identity (from
   *  `stage` on), with which `--certify` builds object code (`hugin.runtime.Certify`). */
  var objectGlobals: java.util.IdentityHashMap[AnyRef, Integer] = java.util.IdentityHashMap()

  /** Signature requirements (reference: modules) recorded by staging, checked by `directives`. */
  var requirements: List[RequirementCheck] = Nil

  /** Relations that may be incomplete (Section 6.5), computed by `completeness`. */
  var incomplete: Set[RelSym] = Set.empty
  var core: hugin.ir.CoreProgram | Null = null
  var components: List[List[RelSym]] = Nil

  /** The dependency edges of each rule of `prog` (by identity) for the facts `edgeFacts`, shared by the
   *  phases that read the dependency graph (`hugin.obj.check.DepGraph.edgesOf`). */
  val edgeCache: java.util.IdentityHashMap[AnyRef, List[hugin.obj.check.DepEdge]] = java.util.IdentityHashMap()
  var edgeFacts: ProgramFacts | Null = null

  /** The split rules of Proposition 8.8 added by `stratify` (by identity; see `StratifyPhase.splitRules`). */
  val splitRules: java.util.Set[AnyRef] = java.util.Collections.newSetFromMap(java.util.IdentityHashMap())

  /** Positions → symbols and types, for tooling. */
  val index: SemanticIndex = SemanticIndex()

  /** Reports requested by settings (`--explain-termination`), printed with the compiler's output. */
  val explanations: mutable.ListBuffer[String] = mutable.ListBuffer.empty

  /** Rules named by `%derivations @r`. */
  val derivationRules: mutable.Set[String] = mutable.LinkedHashSet.empty

  /** With `--export-proofs` (from `derivations` on): the proof relation of every head of every rule in the
   *  exported fragment, and the rules outside it with the reason (`hugin.runtime.ProofExport`). */
  var proofRules: Vector[hugin.obj.transform.ProofRule] = Vector.empty
  var proofOmitted: Vector[(Rule, String)] = Vector.empty
