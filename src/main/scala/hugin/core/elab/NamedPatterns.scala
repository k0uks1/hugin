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
    if rl.rest && state.objectHead then
      fail(
        Diagnostic.error("E0302", "`..` is not allowed in a rule head", rl.span, "rest pattern in head")
          .withNote("the omitted columns of a derived fact would be unknown")
      )
    dupLabels(rl.fields.map(_.label))
    for f <- rl.fields if !labels.contains(f.label.name) do
      var d = Diagnostic.error("E0306", s"`$rel` has no column labelled `${f.label.name}`", f.label.span, "unknown label")
      val named = labels.filter(_ != "_")
      d = if named.isEmpty then d.withNote(s"the columns of `$rel` are not labelled")
      else d.withNote(s"labels of `$rel`: ${named.mkString(", ")}")
      if declared.exists then d = d.withLabel(declared, "declared here")
      fail(d)
    val missing = labels.filter(l => l != "_" && !rl.fields.exists(_.label.name == l))
    if missing.nonEmpty && !rl.rest && !labels.contains("_") then fail(missingLabels(rel, rl, missing))
    if labels.contains("_") then
      error("E0306", s"`$rel` does not label all of its columns, so it cannot be used with a named pattern", rl.span)

  /** E0301, with fixes: add the missing labels after the last field (in a body as `_`, or ignore them with
   *  `..`; in a head as variables named after the labels). */
  private def missingLabels(rel: String, rl: RecordLit, missing: List[Name]): Diagnostic =
    val head = state.objectHead
    val d = Diagnostic.error(
      "E0301",
      s"missing label${if missing.length > 1 then "s" else ""} in named pattern for `$rel`",
      rl.span,
      s"missing ${missing.map(l => s"`$l`").mkString(", ")}"
    ).withHelp(if head then s"add ${missing.map(l => s"`$l = ...`").mkString(", ")}"
    else "add the missing labels, or end the pattern with `..` to ignore them")
    rl.fields.lastOption.fold(d) { last =>
      val at = last.value.span.endPoint
      val add = d.withSuggestion("add the missing labels", at, missing.map(l => s", $l = ${if head then l.capitalize else "_"}").mkString)
      if head then add else add.withSuggestion("ignore the missing labels with `..`", at, ", ..")
    }
