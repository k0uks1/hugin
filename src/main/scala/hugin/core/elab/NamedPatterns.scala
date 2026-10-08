package hugin.core
package elab

import hugin.syntax.{Printer, Tree}
import hugin.syntax.Trees.*
import hugin.util.*

/** Named patterns `r { l₁ = e₁, …, .. }` (Section 2.4): the arguments of a relation, constructor or struct
 *  given by column label, in any order; with `..`, the columns not mentioned are wildcards. They are
 *  elaborated to the positional application. */
trait NamedPatterns:
  self: Elaborator =>
  import core.*

  /** The labelled columns of an object relation or constructor type and its result; `None` if it is not
   *  one, or if it has a single unlabelled column (then a record is an ordinary argument). */
  def namedColumns(ty: Val): Option[List[(Name, Val)]] =
    def go(t: Val): List[(Name, Val)] = force(t) match
      case Val.Pi(x, Icit.Expl, d, cl) if stageOfType(d) == Stage.S0 => (x, d) :: go(inst(cl, Val.Wild))
      case _ => Nil
    val cols = go(ty)
    Option.when(cols.nonEmpty && !(cols.length == 1 && cols.head._1 == "_"))(cols)

  /** `f { fields }` where `f` (elaborated to `ft`, a relation, constructor or struct with the columns
   *  `cols`) is named by `head`. */
  def namedPattern(c: Cxt, head: Tree, ft: Tm, cols: List[(Name, Val)], rl: RecordLit): Tm =
    val rel = Printer.show(head)
    val declared = Tm.unloc(ft) match
      case Tm.Global(id) => globals(id).span
      case _ => Span.NoSpan
    checkFields(rel, declared, cols.map(_._1), rl)
    val byLabel = rl.fields.map(f => f.label.name -> f).toMap
    val args = cols.map { (l, ty) =>
      byLabel.get(l) match
        case Some(f) => check(c, f.value, ty, Stage.S0)
        case None => Tm.loc(rl.span, Tm.Wild)
    }
    Tm.apps(ft, args.map((_, Icit.Expl)))

  private def checkFields(rel: String, declared: Span, labels: List[Name], rl: RecordLit): Unit =
    if rl.rest && state.objectHead then fail(ObjectProblem.RestInHead(rl.span))
    dupLabels(rl.fields.map(_.label))
    for f <- rl.fields if !labels.contains(f.label.name) do
      fail(ObjectProblem.UnknownLabel(rel, f.label.name, labels.filter(_ != "_"), f.label.span, declared))
    val missing = labels.filter(l => l != "_" && !rl.fields.exists(_.label.name == l))
    if missing.nonEmpty && !rl.rest && !labels.contains("_") then
      fail(ObjectProblem.MissingLabels(rel, missing, state.objectHead, rl.span, rl.fields.lastOption.map(_.value.span.endPoint)))
    if labels.contains("_") then fail(ObjectProblem.UnlabelledColumns(rel, rl.span))
