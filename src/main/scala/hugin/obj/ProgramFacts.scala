package hugin.obj

import hugin.util.Span

/** The directives attached to one relation (Figure 2, `dir`). */
final case class RelDirectives(
    open: Boolean = false,
    input: Boolean = false,
    output: Boolean = false,
    /** `%terminates`: the measured argument positions (lexicographic if several) and the directive. */
    terminates: Option[(List[Int], Span)] = None,
    derivations: Boolean = false
)

object RelDirectives:
  val none: RelDirectives = RelDirectives()

/** What the object-level phases know about the relations of a monomorphic program, keyed by symbol: the
 *  directives attached by `directives`, and those of the relations later phases introduce (`%output` of a
 *  derivation relation). The value is immutable; a phase that learns
 *  more replaces the compilation unit's value, so symbols are never changed after staging. */
final class ProgramFacts private (private val byRel: Map[RelSym, RelDirectives]):
  def apply(r: RelSym): RelDirectives = byRel.getOrElse(r, RelDirectives.none)
  def updated(r: RelSym)(f: RelDirectives => RelDirectives): ProgramFacts = ProgramFacts(byRel.updated(r, f(apply(r))))

object ProgramFacts:
  val empty: ProgramFacts = ProgramFacts(Map.empty)

  /** Inside a phase, the facts of the unit being compiled (read at each use, so a phase sees what it
   *  added itself). */
  given current(using c: hugin.compiler.Context): ProgramFacts = c.unit.facts
