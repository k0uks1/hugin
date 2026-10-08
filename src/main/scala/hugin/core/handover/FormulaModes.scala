package hugin.core
package handover

import hugin.core.elab.ObjectProblem
import hugin.obj.ProgramFacts
import hugin.obj.typing.Moding
import hugin.util.*

/** `%mode f m̄` on a formula function (Section 4.8): the body of `f`, applied to fresh variables `Arg1`,
 *  `Arg2`, …, must have a binding order from the input arguments that binds the outputs (E0501). It is
 *  checked once, on the staged body; the relations it calls are taken without modes (as the old meta
 *  evaluator checked it, before directives are attached). */
final class FormulaModes(core: Core, symbols: ObjectSymbols, reporter: Reporter):
  import core.*

  def check(f: Int, mode: List[Boolean], span: Span): Unit =
    val g = globals(f)
    val (applied, params) = applyToArguments(g.ty, globalValue(f))
    val modeText = mode.map(b => if b then "+" else "-").mkString
    if mode.length != params.length then
      reporter.report(ObjectProblem.FormulaModeArity(g.name, mode.length, params.length, span).toDiagnostic)
    else
      try
        val body = ObjectTerms(core, symbols, Nil, span).formulas(quote(0, applied))
        given ProgramFacts = ProgramFacts.empty
        val inputs = params.zip(mode).collect { case (p, true) => p }.toSet
        Moding.canonical(body, inputs) match
          case Left(stuck) =>
            reporter.report(
              Moding.describe(stuck)
                .withLabel(span, "mode declared here")
                .withNote(s"the body of formula function `${g.name}` is not well-moded for mode $modeText")
            )
          case Right((_, bound)) =>
            val outs = params.zip(mode).collect { case (p, false) => p }.filterNot(bound)
            if outs.nonEmpty then
              reporter.report(ObjectProblem.FormulaOutputsUnbound(g.name, modeText, outs.map(_.drop(3)), span).toDiagnostic)
      catch case e: NotObjectCode => reporter.report(e.diagnostic)

  /** The formula function applied to fresh variables for its explicit parameters (and placeholders for
   *  its implicit ones): the formula, and the variables' names. */
  private def applyToArguments(ty: Val, f: Val): (Val, List[String]) =
    var t = ty
    var v = f
    val params = scala.collection.mutable.ListBuffer.empty[String]
    var more = true
    while more do
      force(t) match
        case Val.Pi(_, i, _, cl) =>
          val arg =
            if i == Icit.Impl then Val.Quote(Val.Wild)
            else
              val n = s"Arg${params.length + 1}"
              params += n
              Val.Quote(Val.Obj(ObjForm.Named(n), Nil))
          v = app(v, arg, i)
          t = inst(cl, arg)
        case _ => more = false
    val formula = force(v) match
      case Val.Quote(b) => b
      case other => vSplice(other)
    (formula, params.toList)
