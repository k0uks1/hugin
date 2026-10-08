package hugin.core

import hugin.util.{Origin, Span}
import scala.collection.mutable

/** A requirement of a signature met by evaluation: the relation (or constructor) `rel` passed for the
 *  field at the functor application `use`, in the application chain `origin`. */
final case class RequirementUse(req: SigReq, rel: Int, use: Span, origin: Origin)

/** Requirements of signatures (`%complete l`, `%mode l m̄`, `%fact l : …`) on the relations passed to a
 *  functor are recorded when the application is evaluated ([[Tm.Require]]), since the relations are
 *  only known then; the object level checks them once the directives are attached (E0208), and the
 *  handover checks `%fact` fields. */
trait Requirements:
  self: Core =>

  val requirementUses: mutable.LinkedHashSet[RequirementUse] = mutable.LinkedHashSet.empty

  def required(reqs: List[SigReq], use: Span, v: Val): Val =
    for r <- reqs do
      Val.unloc(force(proj(v, r.label))) match
        case Val.Quote(q) =>
          Val.unloc(force(q)) match
            case Val.Rigid(Head.Glob(g), Nil) => requirementUses += RequirementUse(r, g, use, origin)
            case _ =>
        case _ =>
    v
