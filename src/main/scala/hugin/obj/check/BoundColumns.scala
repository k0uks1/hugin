package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*

/** Phase: bound columns (docs/REDESIGN.md §5.2). Checks the declarations of bound columns (E0605) and that
 *  every rule reading a bound relation of its own component is type-consistent (E0606,
 *  [[TypeConsistency]]), so that evaluation with best values per key computes the limit semantics. */
final class BoundColumnsPhase extends Phase:
  def phaseName = "bound-columns"
  def description = "bound columns are last integer columns of relations; recursive rules over them are type-consistent (Section 5.2)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    p.rels.foreach(checkDeclaration)
    val compOf = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    for r <- p.rules; h <- Termination.headRel(r) do
      val inC: RelSym => Boolean = x => compOf.get(x).exists(compOf.get(h).contains)
      TypeConsistency.check(r, inC).foreach(d => ctx.report(Diag.rule(r)(d)))

  /** E0605: a bound column must be the last column of a plain relation, of an integer type, and the
   *  relation must not be moded (the demand transformation would drop the column from the inputs). */
  private def checkDeclaration(r: RelSym)(using Context): Unit =
    val bounds = r.cols.zipWithIndex.collect { case (c, i) if c.bound.isDefined => (c, i) }
    def report(msg: String, label: String, help: String) =
      ctx.report(Diagnostic.error("E0605", msg, r.span, label).withHelp(help))
    for (c, i) <- bounds do
      val k = c.bound.get.show
      if r.kind != RelKind.Plain then
        report(
          s"`$k` column in the constructor `${r.name}`",
          "constructors have no bound columns",
          "declare a relation with a bound last column instead, e.g. `best : key -> (v : min int) -> rel.`"
        )
      else if i != r.arity - 1 then
        report(
          s"`$k` column of `${r.name}` is not the last column",
          s"column ${i + 1} of ${r.arity} is a `$k` column",
          "move the bound column to the end"
        )
      else if !Termination.isInt(c.tpe) then
        report(s"`$k` column of `${r.name}` is not an integer column", s"has type `${c.tpe.show}`", s"use `$k int`")
      else if ctx.unit.facts.hasModes(r) then
        report(s"`${r.name}` has a bound column and a `%mode`", "moded relation with a bound column", "remove the `%mode` directive")
