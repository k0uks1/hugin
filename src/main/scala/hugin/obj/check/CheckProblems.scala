package hugin.obj
package check

import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Why a relation is incomplete: a chain of positive dependencies ending at a declaration. */
enum Incompleteness:
  case Open(rel: RelSym)
  case Partial(rel: RelSym)

  /** `rel` depends positively on `dep` (at `edge`), which is incomplete because of `next`. */
  case Via(rel: RelSym, dep: RelSym, edge: Span, next: Incompleteness)

  def explain: Msg = this match
    case Open(r) => msg"$r is declared %open"
    case Partial(r) => msg"$r is declared %partial"
    case Via(r, d, _, next) => msg"$r depends positively on $d; " ++ next.explain

/** Where an incomplete relation is negated or aggregated over. */
enum NegSite:
  case InRule, InQuery

/** One step of a dependency cycle: `from` depends on `to` at `at`. */
final case class Dependency(from: RelSym, to: RelSym, negative: Boolean, at: Span)

/** Problems of stratification and the completeness discipline (E0601, E0602). Termination (E0603,
 *  E0604) is reported by `Termination`. */
enum CheckError extends Problem:
  /** The negative edge `negated` lies on the cycle `negated :: path` of the dependency graph. */
  case NegativeCycle(negated: Dependency, path: List[Dependency], reasons: List[CycleReason])
  case NegatedIncomplete(rel: RelSym, use: Span, site: NegSite, why: Incompleteness)

  def code: Code = this match
    case _: NegativeCycle => Code.E0601
    case _: NegatedIncomplete => Code.E0602

  def primary: Span = this match
    case NegativeCycle(e, _, _) => e.at
    case NegatedIncomplete(_, s, _, _) => s

  def message: Msg = this match
    case _: NegativeCycle => msg"stratification cycle through negation"
    case NegatedIncomplete(r, _, NegSite.InRule, _) => msg"negation or aggregation over the incomplete relation $r"
    case NegatedIncomplete(r, _, NegSite.InQuery, _) => msg"query negates or aggregates over the incomplete relation $r"

  override def primaryLabel: Msg = this match
    case NegativeCycle(e, _, _) => msg"${e.from} depends negatively on ${e.to}"
    case NegatedIncomplete(_, _, NegSite.InRule, _) => msg"incomplete relation used negatively"
    case NegatedIncomplete(_, _, NegSite.InQuery, _) => msg"used negatively"

  /** The first steps of the way back from the negated relation (more would clutter the snippet). */
  override def labels: List[(Span, Msg)] = this match
    case NegativeCycle(_, path, _) => path.take(3).map(x => x.at -> msg"${x.from} depends on ${x.to}")
    case _ => Nil

  override def notes: List[Msg] = this match
    case NegativeCycle(e, path, reasons) =>
      val cycle = (e :: path).map(x => (if x.negative then "not " else "") + x.to.name)
      List(
        msg"cycle: ${Lit(e.from.name)} -> ${Lit(cycle.mkString(" -> "))}",
        msg"negation and aggregation must not occur in a recursive cycle"
      ) ++ reasons.map(_.note(e))
    case NegatedIncomplete(_, _, site, why) =>
      List(
        why.explain,
        site match
          case NegSite.InRule => msg"the absence of a fact of an incomplete relation means unknown, not false"
          case NegSite.InQuery => msg"queries may mention incomplete relations only positively"
      )

  override def helps: List[Msg] = this match
    case NegativeCycle(e, _, reasons) => reasons.flatMap(_.help(e))
    case _ => Nil

/** Why a negative cycle exists although the program does not show it directly. */
enum CycleReason:
  /** A rule of `head` asserts facts of the fact constructor `ctor` in its head (Proposition 8.8), so
   *  `ctor` depends on what the rule reads. `head` is `None` if the head is not an atom. */
  case HeadAssertion(head: Option[RelSym], ctor: RelSym)

  /** The demand of the disjunction `aux` inside an aggregate reads the caller. */
  case AggregateDisjunction(aux: RelSym)

  def note(e: Dependency): Msg = this match
    case HeadAssertion(h, c) =>
      val head = h.fold(msg"`?`")(r => msg"$r")
      msg"a rule of $head asserts facts of $c in its head, so $c depends on what the rule reads"
    case AggregateDisjunction(aux) =>
      msg"$aux stands for a disjunction inside an aggregate; its demand needs the disjunction's outer variables, which are bound only by relations that depend on ${e.from}"

  def help(e: Dependency): Option[Msg] = this match
    case _: HeadAssertion => None
    case _: AggregateDisjunction =>
      Some(
        msg"bind the disjunction's outer variables with relations evaluated before ${e.from}, or define the disjunction as a relation with one rule per alternative"
      )
