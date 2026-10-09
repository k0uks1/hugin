package hugin.core
package elab

import hugin.compiler.MetaIndex
import hugin.syntax.Trees.Hole

/** Typed holes (reference: meta/functions): `?` or `?name` stands for an expression still to be written.
 *  It is checked against the expected type like any expression, as an unknown that may stay unsolved,
 *  so the item around it elaborates and its other holes are found as well. Each hole is an error
 *  (E0924, unsolved goal) that reports its type, the *goal*, and the variables in scope, once the item's
 *  other unknowns are solved; the goal is also recorded for language servers (hover, completion, code
 *  actions). The error stops the compilation before staging, so no hole reaches object code. A hole in
 *  an item that fails for another reason is recorded but not reported (the item's error is). */
trait Holes:
  self: Elaborator =>

  /** A hole checked against `a` at stage `st`. */
  def checkHole(c: Cxt, h: Hole, a: Val, st: Stage): Tm =
    recordGoal(c, h, a, st)
    freshMeta(c, a, st, h.span, Holes.What, allowUnsolved = true)

  /** A hole whose type is not known: its type is an unknown as well. */
  def inferHole(c: Cxt, h: Hole): (Tm, Val, Stage) =
    val st = state.stage
    val a = ev(c, freshType(c, st, h.span, "the type of the hole", allowUnsolved = true))
    (checkHole(c, h, a, st), a, st)

  private def recordGoal(c: Cxt, h: Hole, a: Val, st: Stage): Unit =
    later { ok =>
      val goal = show(c, a)
      val context = c.binders.reverse.zipWithIndex.collect {
        case (b, l) if c.scope.get(b.name).contains(l) && visible(b.name) => (b.name, show(c, b.ty))
      }
      index.meta.goal(MetaIndex.Goal(h.span, h.name, goal, st.show, context))
      if ok then
        reporter.report(TypeProblem.UnsolvedGoal(h.name, goal, st.show, context.map((x, t) => s"$x : $t"), h.span).toDiagnostic)
    }

  /** Names a program can write (not the compiler's own: `f#1`, `$sel`). */
  private def visible(n: Name): Boolean = n != "_" && !n.exists(ch => ch == '#' || ch == '$')

object Holes:
  /** What the unknown of a hole is (its [[MetaEntry.what]]). */
  val What: String = "the hole"
