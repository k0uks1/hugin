package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy, Problem}

/** Diagnostics of elaboration: unification failures as type, stage and universe errors; unsupported constructs. */
trait ElabErrors:
  self: Elaborator =>
  import core.*

  def error(code: DiagCode, msg: String, span: Span, label: String = ""): Nothing =
    throw ElabError(Legacy.error(code, msg, span, label))

  def fail(d: Diagnostic): Nothing = throw ElabError(d)

  def fail(p: Problem): Nothing = throw ElabError(p.toDiagnostic)

  /** Unifies an inferred type with an expected one, reporting a mismatch at `span`. */
  def unifyAt(c: Cxt, span: Span, expected: Val, found: Val): Unit =
    try unify(c.lvl, found, expected)
    catch case e: UnifyError => fail(mismatch(c, span, expected, Stage.S1, found, Stage.S1, e.failure))

  def mismatch(c: Cxt, span: Span, expected: Val, sExp: Stage, found: Val, sFound: Stage, f: UnifyFailure): Diagnostic =
    val e = show(c, expected)
    val fo = show(c, found)
    f match
      case UnifyFailure.Universe =>
        Legacy.error(DiagCode.E0904, "universe inconsistency", span, s"expected `$e`, found `$fo`")
          .withNote("universe levels are inferred: `Type₀ : Type₁ : …`, and a type in `Typeᵢ` is also in `Typeⱼ` for i ≤ j")
          .withNote("`Type : Type` is excluded: it would make the meta level inconsistent and non-terminating")
      case _ =>
        stageError(c, span, expected, sExp, found, sFound).getOrElse {
          var d = Legacy.error(DiagCode.E0901, "mismatched types", span, s"expected `$e`, found `$fo`")
          if e == fo then d = d.withNote(s"the expected type is at the ${sExp.show} level, the found one at the ${sFound.show} level")
          f match
            case UnifyFailure.Occurs(m) =>
              d = d.withNote(s"the unknown `?$m` would have to contain itself (occurs check)")
            case UnifyFailure.Escape(x) =>
              val n = if x < c.lvl then c.binder(x).name else s"#$x"
              d = d.withNote(s"the solution of an unknown would mention `$n`, which is not in its scope")
            case UnifyFailure.NonPattern =>
              d = d.withNote(
                "an unknown is applied to arguments that are not distinct bound variables, so it cannot be solved by unification (outside the pattern fragment)"
              )
            case _ =>
          d
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
        Some(
          Legacy.error(DiagCode.E0902, "object code used where a compile-time value is needed", span, s"object code of type `$fo`")
            .withNote(s"a meta value of type `$e` is expected here")
            .withNote(
              "object terms (rule variables, constructor terms, formulas) only exist at run time; the meta level computes at compile time"
            )
            .withHelp(s"to take object code as an argument, declare the parameter with an object type (`⇑$fo` at the meta level)")
        )
      case (Stage.S1, Stage.S0) if !isLiftOrFlex(found) && isMetaPrimOrData(found) =>
        Some(
          Legacy.error(DiagCode.E0902, "compile-time value used as object code", span, s"a meta value of type `$fo`")
            .withNote(s"object code of type `$e` is expected here")
            .withNote("only object code (of type `⇑A`) and primitive values (`int`, `float`, `string`) can be spliced into object code")
        )
      case _ => None

  private def isMetaPrimOrData(v: Val): Boolean = force(v) match
    case Val.Base(_, Stage.S1) | Val.Pi(_, _, _, _) | Val.RecTy(_, _, _) | Val.U1(_) => true
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
    fail(
      Legacy.error(DiagCode.E0907, s"$what are not supported by the new meta level yet", span, "not supported yet")
        .withNote("the new meta level (`--new-meta`) implements steps B1 and B2 of docs/REDESIGN.md §10; the rest is ported in B3")
    )
