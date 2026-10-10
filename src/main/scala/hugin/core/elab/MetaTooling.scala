package hugin.core
package elab

import hugin.compiler.MetaIndex
import hugin.compiler.MetaIndex.{HintKind, Typed}
import hugin.util.*
import scala.util.control.NonFatal

/** What the elaborator records about the meta level for language servers (issue #54), in the
 *  [[hugin.compiler.MetaIndex]] of the semantic index: the elaborated type and stage of every expression
 *  that is checked or inferred at a stage, the quotes, splices, lifts and implicit arguments stage
 *  inference and implicit insertion add (inlay hints), and the levels of universes.
 *
 *  Records are made where the elaborator decides, but shown only once the item's unknowns are solved:
 *  they go to the core's tooling log ([[Core.toolingLog]], rolled back with the metas) and are flushed
 *  at the end of an item ([[flushTooling]]). An item that elaborated keeps its core unchanged afterwards,
 *  so its records are shown when a language server asks (lazily: the compiler pays only for the
 *  closures); a failed item's are shown at once, before its metas are undone. */
trait MetaTooling:
  self: Elaborator =>
  import core.*

  /** Records `f` for the end of the item: called with whether the item succeeded. */
  def later(f: Boolean => Unit): Unit = if recording then toolingLog += f

  /** Whether records are kept ([[later]] drops them otherwise): a record that is costly to compute checks
   *  it first. */
  def recording: Boolean = !index.muted && !toolingOff

  private var toolingOff = false

  /** Runs `f` without records (generated code). */
  def withoutTooling[A](f: => A): A =
    val saved = toolingOff
    toolingOff = true
    try f
    finally toolingOff = saved

  /** A record shown when asked (lazily) if the item succeeded, and now otherwise. */
  private def shown[A](success: Boolean)(f: => A): () => Option[A] =
    def attempt: Option[A] =
      try Some(f)
      catch case NonFatal(_) | _: StackOverflowError => None
    if success then
      lazy val v = attempt
      () => v
    else
      val v = attempt
      () => v

  /** Runs the records of the item that ends (`success` if it elaborated). */
  def flushTooling(success: Boolean): Unit =
    val pending = toolingLog.toList
    toolingLog.clear()
    pending.foreach(f =>
      try f(success)
      catch case NonFatal(_) => ()
    )

  /** The position in the tooling log: the records made after it are those of a part of the item. */
  def toolingMark: Int = toolingLog.length

  /** Runs the records made since `mark` for a part of the item that failed (a clause group of a module
   *  body, [[ModuleBodies]]): they are shown at once, before its metas are undone. */
  def flushFailedSince(mark: Int): Unit =
    val pending = toolingLog.drop(mark).toList
    toolingLog.dropRightInPlace(toolingLog.length - mark)
    pending.foreach(f =>
      try f(false)
      catch case NonFatal(_) => ()
    )

  /** The expression at `span` elaborated to `tm : ty` at stage `st` (`checked` against `ty`). */
  def recordTyped(c: Cxt, span: Span, tm: Tm, ty: Val, st: Stage, checked: Boolean): Unit =
    if span.exists then
      later { ok =>
        index.meta.typedLazy(
          span,
          shown(ok) {
            val code = force(ty).isInstanceOf[Val.Lift]
            Typed(span, show(c, ty), st.show, code, elaborated(c, tm, span), checked, headKey(ty))
          }
        )
      }

  /** The expression at `span`, whose elaboration against `a` failed (a name being typed): what was
   *  expected there, with the variables in scope (for completion). */
  def recordExpected(c: Cxt, span: Span, a: Val, st: Stage): Unit =
    if span.exists then
      later { _ =>
        val context = c.binders.reverse.zipWithIndex.collect {
          case (b, l) if c.scope.get(b.name).contains(l) && b.name != "_" && !b.name.exists(ch => ch == '#' || ch == '$') =>
            (b.name, show(c, b.ty))
        }
        index.meta.typed(Typed(span, show(c, a), st.show, force(a).isInstanceOf[Val.Lift], None, checked = true, headKey(a), context))
      }

  /** The elaborated term, if it shows what is not written (implicit arguments, quotes, splices). */
  private def elaborated(c: Cxt, tm: Tm, span: Span): Option[String] =
    val text = showTm(c.names, zonk(c.env, c.lvl, tm))
    def norm(s: String) = s.filterNot(_.isWhitespace)
    Option.when(text.length <= MaxShown && norm(text) != norm(span.text) && text.exists(c => c == '{' || c == '⟨' || c == '$'))(text)

  private val MaxShown = 200

  /** What results of type `ty` are, for type-directed completion: the head of the type. A lifted type is
   *  its object type's (object code of type `A` is what an `A` is in object code). */
  def headKey(ty: Val): String = forceData(ty) match
    case Val.Rigid(Head.Glob(id), _) => s"g:${globals(id).name}"
    case Val.Base(b, _) => s"b:${b.show}"
    case Val.Lift(x) => headKey(x)
    case Val.U0 | Val.U1(_) => "type"
    case Val.PropT => "prop"
    case Val.RelT => "rel"
    case Val.FactTy(r) => headKey(r)
    case _: Val.Pi => "function"
    case _: Val.RecTy => "record"
    case _ => ""

  /** The head of the result of a global's type (after all its arguments). */
  def resultHeadKey(ty: Val): String = headKey(telescope(ty)._2)

  /** A hint at `at` (an empty span) shown as `label`. */
  def recordHint(at: Span, label: String, kind: HintKind, tooltip: String): Unit =
    if at.exists then later(_ => index.meta.hint(MetaIndex.Hint(at, label, kind, tooltip)))

  /** The source position the coercion being inserted is for ([[Coercions.coe]]). */
  var coercionAt: Span = Span.NoSpan

  /** Runs `f` with `span` as the position of the coercions it inserts. */
  def coercing[A](span: Span)(f: => A): A =
    val saved = coercionAt
    coercionAt = span
    try f
    finally coercionAt = saved

  /** Stage inference inserted a quote around the code at the current position. */
  def insertedQuote(): Unit =
    recordHint(coercionAt.startPoint, "⟨", HintKind.Staging, "quote (inferred): object code used as a meta value of type ⇑A")
    recordHint(coercionAt.endPoint, "⟩", HintKind.Staging, "end of the inferred quote")

  /** Stage inference inserted a splice, a persisted literal or a lifting (`how`) at the current position. */
  def insertedSplice(how: String): Unit = recordHint(coercionAt.startPoint, "$", HintKind.Staging, how)

  /** Stage inference inserted `⇑` (an object type used as a meta type). */
  def insertedLift(): Unit = recordHint(coercionAt.startPoint, "⇑", HintKind.Staging, "lift (inferred): an object type used as a meta type")

  /** The rule Lift moved the meta code `t` to object code `moved`: a splice, a persisted literal, or a
   *  shared type's lifting. */
  def insertedLifting(moved: Tm): Unit = moved match
    case Tm.Persist(_) => insertedSplice("persisted (inferred): the compile-time value is embedded as a literal")
    case Tm.Splice(Tm.App(l, _, _)) => insertedSplice(s"lifted (inferred) by `${showPlain(Nil, explicitOnly(l))}`")
    case _ => insertedSplice("splice (inferred): meta code of type ⇑A inserted as object code")

  /** Implicit insertion applied the term at `span` to the unknown `m` for the implicit argument `x`. */
  def insertedImplicit(c: Cxt, span: Span, x: Name, m: Tm): Unit =
    if span.exists && span.text.nonEmpty then
      later { ok =>
        index.meta.hintLazy(
          shown(ok) {
            val v = showPlain(c.names, zonk(c.env, c.lvl, m))
            MetaIndex.Hint(span.endPoint, s"{$v}", HintKind.Implicit, s"implicit argument `$x` = `$v` (inferred)")
          }
        )
      }

  /** `Type` at `span` is the universe at level `l` (inferred). */
  def recordLevel(span: Span, l: Level): Unit =
    if span.exists then
      later { ok =>
        index.meta.hintLazy(
          shown(ok) {
            val v = showLevel(l).stripPrefix("Type")
            MetaIndex.Hint(span.endPoint, if v.isEmpty then "₀" else v, HintKind.Level, s"universe level (inferred): ${showLevel(l)}")
          }
        )
      }
