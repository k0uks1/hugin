package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.Tree
import scala.collection.mutable

/** Integer literals checked against a type that is still unknown (reference: meta/functions,
 *  literals): the literal is an unknown of that type until the end of its item, when it is checked
 *  against the type as solved by then, and against `int` at the stage of its position if the type is
 *  still unknown. A literal never takes a nat-like type by default. */
trait Literals:
  self: Elaborator =>
  import core.*

  /** A postponed literal: its unknown `meta` (with its description and position, to recognise it after
   *  backtracking removed it), the context, the literal and the unknown type. */
  private final case class Postponed(meta: Int, what: String, c: Cxt, lit: Tree, ty: Val, term: Tm)

  private val postponed = mutable.LinkedHashMap.empty[Int, Postponed]

  /** The literal `t`, checked against the unknown meta type `a`: an unknown, resolved by [[resolveLiterals]]. */
  def postponeLiteral(c: Cxt, t: Tree, a: Val): Tm =
    val what = s"the literal `${t.span.text}`"
    val term = freshMeta(c, a, Stage.S1, t.span, what)
    val m = metas.length - 1
    postponed.filterInPlace((k, _) => k < m)
    postponed(m) = Postponed(m, what, c, t, a, term)
    term

  /** Resolves the literals postponed since meta `start`, in their order (at the end of an item, and before
   *  a definition is stored): each is checked against its type,
   *  `int` (at stage 1) if that is still unknown, and its unknown is unified with the result. */
  def resolveLiterals(start: Int): Unit =
    val due = postponed.values.filter(p => p.meta >= start).toList
    postponed.filterInPlace((k, _) => k < start)
    due.foreach { p =>
      if p.meta < metas.length && metas(p.meta).what == p.what && metas(p.meta).span == p.lit.span then
        force(p.ty) match
          case Val.Flex(_, _) => unifyAt(p.c, p.lit.span, Val.Base(BaseType.IntT, Stage.S1), p.ty)
          case _ =>
        val tm = check(p.c, p.lit, p.ty, Stage.S1)
        unifyAt(p.c, p.lit.span, ev(p.c, tm), ev(p.c, p.term))
    }
