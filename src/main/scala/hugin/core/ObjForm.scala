package hugin.core

import hugin.obj.CmpOp
import hugin.syntax.{AggKind, Bound}
import hugin.util.Span

/** The forms of object syntax that only exist at stage 0. In the core they are one node,
 *  [[Tm.Obj]] / [[Val.Obj]] (a form and its subterms): object code is inert data for evaluation,
 *  unification and read-back, which treat every form alike, so a new object form needs no new case in
 *  the core's algorithms. Object typing proper (subtyping, unions, refinements, projections, updates) is
 *  not the core's business: it is done by `obj/typing/ObjTyper` on the staged program (REDESIGN §3.4).
 *
 *  The subterms of each form, in order:
 *
 *  - [[Loc]]: `[t]`, the source position of the object term or formula `t`. It is transparent: evaluation
 *    keeps it (so that the staged program has positions for its diagnostics), unification looks through
 *    it.
 *  - [[Compare]] `[a, b]`, [[And]] `[a, b]`, [[Or]] `[a, b]`, [[Not]] `[a]`: formulas.
 *  - [[Wild]] `[]`: `_` in object code (each occurrence is a fresh variable).
 *  - [[As]] `[t, x]`: `t as X` (in a body, an atom with its fact bound to `X`).
 *  - [[Ascribe]] `[t, A]`: `(t : A)`, an ascription to an object type.
 *  - [[Proj]] `[t]`: `t.l`, a projection of a fact by column label.
 *  - [[With]] `[t, e₁, …, eₙ]`: `t with { l₁ = e₁, … }`, a functional update.
 *  - [[Agg]] `[x, t, φ]`: `X = k { t | φ }`, an aggregate.
 *  - [[Union]] `[A₁, …, Aₙ]`: the object union type `A₁ | … | Aₙ`.
 *  - [[Named]] `[]`: an object variable by name (see [[Tm.Fresh]]).
 *  - [[And]] and [[Or]] take any number of subterms (`Or` of none is the empty disjunction, false).
 *  - [[BoundCol]] `[A]`: the column type `min A` / `max A` of a bound column (REDESIGN §5.2).
 */
enum ObjForm:
  case Loc(span: Span)
  case Compare(op: CmpOp)
  case And, Or, Not, Wild
  case As
  case Ascribe
  case Proj(label: Name)
  case With(labels: List[(Name, Span)])
  case Agg(kind: AggKind)
  case Union

  /** A named object variable: a variable of a formula function's clause after hygienic renaming. */
  case Named(name: Name)
  case BoundCol(kind: Bound)
