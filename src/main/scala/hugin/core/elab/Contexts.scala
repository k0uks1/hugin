package hugin.core
package elab

import hugin.util.*

/** Elaboration contexts: binding variables, fresh metavariables, evaluation in a context. */
trait Contexts:
  self: Elaborator =>
  import core.*

  def show(c: Cxt, v: Val): String = showVal(c.names, v)

  def bind(c: Cxt, x: Name, a: Val, st: Stage): Cxt =
    Cxt(
      Val.local(c.lvl) :: c.env,
      c.lvl + 1,
      Binder(x, a, quote(c.lvl, a), st) :: c.binders,
      if x == "_" then c.scope else c.scope + (x -> c.lvl),
      Some(Icit.Expl) :: c.pruning
    )

  /** A binder that source names cannot refer to (an inserted implicit lambda). */
  def newBinder(c: Cxt, x: Name, a: Val, st: Stage): Cxt = bind(c, x, a, st).copy(scope = c.scope)

  /** A fresh meta of type `a` in context `c`, applied to the context's variables. */
  def freshMeta(c: Cxt, a: Val, st: Stage, span: Span, what: String, allowUnsolved: Boolean = false): Tm =
    val closed = c.binders.foldLeft(quote(c.lvl, a))((acc, b) => Tm.Pi(b.name, Icit.Expl, b.tyTm, acc))
    val m = newMeta(eval(Nil, closed), st, span, what, allowUnsolved)
    Tm.AppPruning(Tm.Meta(m), c.pruning)

  def freshType(c: Cxt, st: Stage, span: Span, what: String, allowUnsolved: Boolean = false): Tm =
    st match
      case Stage.S0 => freshMeta(c, Val.U0, Stage.S0, span, what, allowUnsolved)
      case Stage.S1 => freshMeta(c, Val.U1(levels.fresh()), Stage.S1, span, what, allowUnsolved)

  def ev(c: Cxt, t: Tm): Val = eval(c.env, t)
