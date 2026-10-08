package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.Problem

/** Diagnostics of elaboration: unification failures as type, stage and universe errors; unsupported constructs. */
trait ElabErrors:
  self: Elaborator =>
  import core.*

  def fail(d: Diagnostic): Nothing = throw ElabError(d)

  def fail(p: Problem): Nothing = throw ElabError(p.toDiagnostic)

  /** Reports the error of an item (unless it follows from an error reported already). */
  def report(e: ElabError): Unit = if !e.silent then reporter.report(e.diag)

  /** Unifies an inferred type with an expected one, reporting a mismatch at `span`. */
  def unifyAt(c: Cxt, span: Span, expected: Val, found: Val): Unit =
    try unify(c.lvl, found, expected)
    catch case e: UnifyError => fail(mismatch(c, span, expected, Stage.S1, found, Stage.S1, e.failure))

  def mismatch(c: Cxt, span: Span, expected: Val, sExp: Stage, found: Val, sFound: Stage, f: UnifyFailure): Diagnostic =
    val e = show(c, expected)
    val fo = show(c, found)
    f match
      case UnifyFailure.MissingField(_) | UnifyFailure.Field(_, _, _) =>
        val note = f match
          case UnifyFailure.MissingField(l) => s"missing field `$l`"
          case UnifyFailure.Field(l, fo, ex) => s"field `$l`: expected `${show(c, ex)}`, found `${show(c, fo)}`"
          case _ => ""
        ElabProblem.SignatureMismatch(e, note, span).toDiagnostic
      case UnifyFailure.Universe => TypeProblem.UniverseInconsistency(e, fo, span).toDiagnostic
      case _ =>
        stageError(c, span, expected, sExp, found, sFound).getOrElse {
          val levels =
            if e == fo then List(s"the expected type is at the ${sExp.show} level, the found one at the ${sFound.show} level") else Nil
          val why = f match
            case UnifyFailure.Occurs(m) => List(s"the unknown `?$m` would have to contain itself (occurs check)")
            case UnifyFailure.Escape(x) =>
              val n = if x < c.lvl then c.binder(x).name else s"#$x"
              List(s"the solution of an unknown would mention `$n`, which is not in its scope")
            case UnifyFailure.NonPattern =>
              List(
                "an unknown is applied to arguments that are not distinct bound variables, so it cannot be solved by unification (outside the pattern fragment)"
              )
            case _ => Nil
          TypeProblem.Mismatch(e, fo, span, levels ++ why).toDiagnostic
        }

  private def isLiftOrFlex(v: Val): Boolean = force(v) match
    case Val.Lift(_) | Val.Flex(_, _) => true
    case _ => false

  /** Mismatches across stages get their own diagnostic (E0902). */
  private def stageError(c: Cxt, span: Span, expected: Val, sExp: Stage, found: Val, sFound: Stage): Option[Diagnostic] =
    val e = show(c, expected)
    val fo = show(c, found)
    (sFound, sExp) match
      case (Stage.S0, Stage.S1) if !isLiftOrFlex(expected) && !isUniverse(expected) =>
        Some(TypeProblem.ObjectForMeta(e, fo, span).toDiagnostic)
      case (Stage.S1, Stage.S0) if !isLiftOrFlex(found) && isMetaPrimOrData(found) =>
        Some(TypeProblem.MetaForObject(e, fo, span).toDiagnostic)
      case _ => None

  private def isMetaPrimOrData(v: Val): Boolean = force(v) match
    case Val.Base(_, Stage.S1) | Val.Pi(_, _, _, _) | Val.RecTy(_, _, _, _, _) | Val.U1(_) => true
    case Val.Rigid(Head.Glob(id), _) => globals(id).stage == Stage.S1
    case _ => false

  def unsupported(t: Tree): Nothing =
    val what = t match
      case _: ModuleBody => "module bodies"
      case _: Agg => "aggregates"
      case _: As => "`as` patterns"
      case _: With => "record updates"
      case _: Union => "union types"
      case _: Import => "imports"
      case _: RuleRef => "rule references"
      case RecordLit(_, true) => "`..` in records"
      case _ => "this construct"
    unsupportedAt(t.span, what)

  def unsupportedAt(span: Span, what: String): Nothing =
    fail(TypeProblem.Unsupported(what, span))
