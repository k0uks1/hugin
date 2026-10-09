package hugin.compiler

import hugin.util.Span
import scala.collection.mutable

/** What the elaborator learned about the meta level, for tooling (issue #54): the elaborated types and
 *  stages of expressions, what stage inference inserted, typed holes and what the coverage checker knows
 *  for interactive development. Part of the [[SemanticIndex]] (its `meta`), filled through
 *  [[hugin.core.elab.MetaTooling]] once the unknowns of an item are solved, so types are shown with their
 *  solutions. Language servers read it ([[hugin.query.MetaIde]]); the compiler's own output never does. */
final class MetaIndex:
  import MetaIndex.*

  private val typedSet = mutable.LinkedHashMap.empty[Span, () => Option[Typed]]
  private val hintSet = mutable.LinkedHashSet.empty[Hint]
  private val lazyHints = mutable.ArrayBuffer.empty[() => Option[Hint]]
  private val goalSet = mutable.LinkedHashMap.empty[Span, Goal]
  private val splitSet = mutable.LinkedHashMap.empty[Span, Split]
  private val missingSet = mutable.LinkedHashMap.empty[Span, MissingClauses]
  private val skeletonSet = mutable.LinkedHashMap.empty[Span, Skeleton]
  private val applications = mutable.LinkedHashMap.empty[Span, DirectiveUse]
  private val heads = mutable.HashMap.empty[Sym, String]
  private val roles = mutable.HashMap.empty[Sym, Role]
  private val notesOf = mutable.HashMap.empty[Sym, () => List[String]]

  /** The expression at `span` (the last record wins: an item elaborated again records it again). */
  def typed(t: Typed): Unit = typedLazy(t.span, () => Some(t))

  /** A record computed when first asked for (see [[hugin.core.elab.MetaTooling]]); `None` if it cannot be
   *  shown. */
  def typedLazy(span: Span, t: () => Option[Typed]): Unit = if span.exists then typedSet(span) = t
  def hint(h: Hint): Unit = if h.at.exists then hintSet += h
  def hintLazy(h: () => Option[Hint]): Unit = lazyHints += h
  def goal(g: Goal): Unit = if g.span.exists then goalSet(g.span) = g
  def split(s: Split): Unit = if s.variable.exists then splitSet(s.variable) = s
  def missing(m: MissingClauses): Unit = if m.at.exists then missingSet(m.at) = m
  def skeleton(s: Skeleton): Unit = if s.name.exists then skeletonSet(s.name) = s
  def directive(d: DirectiveUse): Unit = if d.span.exists then applications(d.span) = d

  /** The head of the result type of a global (after all its arguments), as [[headKey]] gives it: the
   *  candidates of type-directed completion. */
  def resultHead(sym: Sym, head: String): Unit = heads(sym) = head
  def resultHeadOf(sym: Sym): Option[String] = heads.get(sym)

  /** What a meta-level global is (semantic tokens tell functions from constructors and families). */
  def role(sym: Sym, r: Role): Unit = roles(sym) = r
  def roleOf(sym: Sym): Option[Role] = roles.get(sym)

  /** Hover notes of a symbol that only language servers show (the stages of a shared type), computed
   *  when first asked for. */
  def note(sym: Sym, notes: () => List[String]): Unit =
    lazy val computed = scala.util.Try(notes()).getOrElse(Nil)
    notesOf(sym) = () => computed
  def notes(sym: Sym): List[String] = notesOf.get(sym).fold(Nil)(_())

  def types: Iterable[Typed] = typedSet.values.flatMap(_())

  /** The expressions whose spans satisfy `p` (only those are computed). */
  def typesWhere(p: Span => Boolean): List[Typed] = typedSet.iterator.filter((sp, _) => p(sp)).flatMap(_._2()).toList
  def hints: Iterable[Hint] = (hintSet ++ lazyHints.flatMap(_())).toList.distinct
  def goals: Iterable[Goal] = goalSet.values
  def splits: Iterable[Split] = splitSet.values
  def missingClauses: Iterable[MissingClauses] = missingSet.values
  def skeletons: Iterable[Skeleton] = skeletonSet.values
  def directives: Iterable[DirectiveUse] = applications.values

  /** Adds what `other` recorded (the index of a part elaborated apart). */
  def include(other: MetaIndex): Unit =
    typedSet ++= other.typedSet
    hintSet ++= other.hintSet
    lazyHints ++= other.lazyHints
    goalSet ++= other.goalSet
    splitSet ++= other.splitSet
    missingSet ++= other.missingSet
    skeletonSet ++= other.skeletonSet
    applications ++= other.applications
    heads ++= other.heads
    roles ++= other.roles
    notesOf ++= other.notesOf

object MetaIndex:
  /** What a meta-level global is. */
  enum Role:
    case Function, Family, Constructor, Module, Value

  /** The expression at `span`: its elaborated type (shown with the solutions of unknowns), its stage, the
   *  elaborated term if it shows something not written (implicit arguments, quotes, splices), whether it
   *  was checked against `tpe` (rather than inferred), and the head of `tpe` ([[headKey]]). */
  final case class Typed(
      span: Span,
      tpe: String,
      stage: String,
      code: Boolean,
      elaborated: Option[String],
      checked: Boolean,
      head: String,
      /** For an expression whose elaboration failed (a name being typed): the variables in scope. */
      context: List[(String, String)] = Nil
  )

  enum HintKind:
    /** A quote `⟨`/`⟩`, splice `$`, lift `⇑` or lifting inserted by stage inference. */
    case Staging

    /** An inferred implicit argument `{A = int}`. */
    case Implicit

    /** The inferred level of a universe `Type`. */
    case Level

  /** A hint at the (empty) span `at`: `label` before or after it, `tooltip` saying what it is. */
  final case class Hint(at: Span, label: String, kind: HintKind, tooltip: String)

  /** A typed hole `?` or `?name`: its goal type and stage, and the context (name, type), outermost first. */
  final case class Goal(span: Span, name: Option[String], tpe: String, stage: String, context: List[(String, String)])

  /** A pattern variable `variable` of the clause at `clause` that can be split: the patterns replacing it,
   *  one per constructor that can apply (a constructor applied to fresh variables). */
  final case class Split(variable: Span, name: String, clause: Span, patterns: List[String])

  /** The clauses missing from the function declared at `at` (the coverage checker's cases, written as
   *  clauses with a hole for the right-hand side), to be inserted after `after` (its last clause). */
  final case class MissingClauses(at: Span, fn: String, clauses: List[String], after: Span)

  /** A meta function declared at `decl` (its name at `name`) without clauses or definition: the clause
   *  `clause` (variables for its explicit arguments, a hole for the right-hand side) starts one. */
  final case class Skeleton(name: Span, decl: Span, fn: String, clause: String)

  /** A directive application `%d a₁ … aₙ` at `span`: the type of the application and its footprint. */
  final case class DirectiveUse(span: Span, shown: String, tpe: String, footprint: String)
