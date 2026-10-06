package hugin.compiler

import hugin.util.SourceFile
import hugin.syntax.Program
import hugin.meta.{MExpr, Scope}
import hugin.obj.*
import scala.collection.mutable

/** Everything the compiler knows about one source program; each phase fills in its part. */
final class CompilationUnit(val source: SourceFile):
  var untpd: Program | Null = null
  var rootScope: Scope | Null = null

  /** Scopes of module bodies (keyed by identity of the surface tree). */
  val scopes: java.util.IdentityHashMap[AnyRef, Scope] = java.util.IdentityHashMap()
  var elab: MExpr | Null = null

  /** Object program after meta evaluation (may still contain families). */
  var generic: ObjProgram | Null = null

  /** The object program, transformed in place by the object-level phases. */
  var prog: ObjProgram | Null = null

  /** Typing contexts computed by `objTyper`, keyed by rule/query identity. */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, OType]] = java.util.IdentityHashMap()

  /** Deferred checks of signature requirements (Section 4.4), run after evaluation. */
  val deferred: mutable.ListBuffer[() => Unit] = mutable.ListBuffer.empty
  var core: hugin.ir.CoreProgram | Null = null
  var components: List[List[RelSym]] = Nil

  /** Positions → symbols and types, for tooling. */
  val index: SemanticIndex = SemanticIndex()
  var incomplete: Set[RelSym] = Set.empty

  /** Reports requested by settings (`--explain-termination`), printed with the compiler's output. */
  val explanations: mutable.ListBuffer[String] = mutable.ListBuffer.empty

  /** Rules named by `%derivations @r`. */
  val derivationRules: mutable.Set[String] = mutable.LinkedHashSet.empty
