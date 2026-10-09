package hugin.core
package elab

/** One variable of an elaboration context. `tyTm` is its type quoted at its own level (used to close
 *  the types of fresh metas, as elaboration-zoo's `Path`); `defn` the definition of a let-bound one;
 *  `origin` what declared it, for diagnostics; `site` where a local variable (a pattern variable, a
 *  lambda's parameter, a `where` binding) is written and what it is, for tooling. */
final case class Binder(
    name: Name,
    ty: Val,
    tyTm: Tm,
    stage: Stage,
    defn: Option[Tm] = None,
    origin: BinderOrigin = BinderOrigin.Plain,
    site: Option[Site] = None
)

/** Where a local variable is declared (`span`, its name) and what it is (`what`: "pattern variable"). */
final case class Site(span: hugin.util.Span, what: String)

/** What declared a variable: a parameter (of a definition or functor, with the position of its name and
 *  its type as written), a member of a module body, or anything else. */
enum BinderOrigin:
  case Plain
  case Param(span: hugin.util.Span, tpe: hugin.syntax.Tree)
  case Member

/** An elaboration context: the environment for evaluation (innermost first), the bound variables with
 *  their types and stages, the source names in scope (name → level) and the pruning that applies fresh
 *  metas to the bound variables. */
final case class Cxt(
    env: List[Val],
    lvl: Int,
    binders: List[Binder],
    scope: Map[Name, Int],
    pruning: Pruning
):
  def names: List[Name] = binders.map(_.name)

  /** The binder with the given level. */
  def binder(level: Int): Binder = binders(lvl - level - 1)

object Cxt:
  val empty: Cxt = Cxt(Nil, 0, Nil, Map.empty, Nil)
