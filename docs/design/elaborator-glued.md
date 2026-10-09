# Glued evaluation, approximate conversion and frozen metas

Design note for [issue #66](https://github.com/k0uks1/hugin/issues/66): three elaborator techniques from
smalltt, ported to the meta level (`hugin.core`). Status: proposal, not implemented. It is written to
land after Batch A of the typed object code design (#56, `docs/design/typed-object-code.md` on branch
`feat/typed-object-56`); section 7 gives the order.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 design, 5 interactions, 6 effects,
7 sequencing with #56, 8 batches, 9 sources.

## 1. Recommendations

1. **Freeze metas per top-level block.** A block is one declaration item, one clause group or one object
   item. Metas created before the block are frozen: unification never solves or prunes them. This makes
   the implementation agree with the reference, which says a hole is an unknown "that the rest of the
   item may constrain" (reference: meta/functions). On all goldens and 448 further tests no frozen meta
   is ever solved today (spike in 2.3), so the only behavioural change is for holes.
2. **Glue definitions, not clause functions.** A reference to a definition (`GlobalKind.Definition`)
   evaluates to a new value `Val.Top(id, spine, unfolded)`: the folded application and its lazily
   unfolded value. Read-back keeps the folded form by default; staging, memo keys, family keys,
   size-change matrices and index unification read back the unfolded form, so their results do not
   change. Functions defined by clauses keep reducing eagerly.
3. **`force` keeps its meaning.** `force` unfolds `Top` heads as well as solved metas, so the 172 call
   sites that match on a forced value need no change. The folded view is asked for explicitly
   (`forceMetas`, `quote` in display mode, the meta-solution read-back `psubst`).
4. **Three conversion states as in smalltt.** `unify` takes a state `Rigid`, `Flex` or `Full`. Equal
   `Top` heads compare their spines in `Flex` (no meta solutions, no unfolding, no new level
   constraints) and unfold once on failure. Different heads unfold the later definition first.
5. **Smallest meta solutions.** A meta is solved with the folded right-hand side (`?m := vec2`, not
   `vec int (suc (suc zero))`), eta-short when the right-hand side is a `Top` (`?m := f`, not
   `[x] f x`). Validity is still checked up to unfolding.
6. **Messages print folded types.** If expected and found print alike when folded but differ, they are
   printed unfolded. Unknowns print with numbers relative to their block (`?3`, not `?167`), so
   diagnostics no longer depend on the number of metas in the prelude.
7. **Fix the size-change check first.** Calls through a definition are invisible to the meta
   termination check today, and a non-terminating function is accepted and overflows the stack
   (2.4). Glued meta solutions would hide more calls behind definitions, so this fix is Batch 0.

## 2. Hugin today

Measured on f05ee62 (`design/elab-66`), with scratch programs and a staged build; nothing of this is
committed.

### 2.1 Printed types unfold definitions

`Evaluation.globalValue` returns the value of a definition, so a definition never survives evaluation,
and `Readback.quote` prints normal forms. Types that come from syntax (`GlobalEntry.tyTm`, printed by
hover and `--print-after elaborate`) are folded; types and implicit arguments that come from values are
not.

| program | what is printed today |
|---|---|
| `vec2 : Type = vec int two.` with `two : nat = suc (suc zero)`, `w = ident v.` (`v : vec2`), `--print-after elaborate` | `w : vec int (suc (suc zero)) = ident {vec int (suc (suc zero))} v.` |
| the same, `l = len v.` | `l : nat = len {int} {suc (suc zero)} v.` |
| `graph : Type = { … }`, `g : graph = …`, `h = ident g.` | `h : { node : ⇑type, edge : ⇑($node -> $node -> rel) } = ident {{ node : ⇑type, … }} g.` |
| hover on `w` | `meta definition w : vec int (suc (suc zero))` |
| `vec3 : Type = vec int (plus one (suc one)).` and a wrong `v : vec3` | ``expected `vec int (plus (suc zero) (suc (suc zero)))` `` |
| golden `neg/meta_types` (`bad4 = tc 5.`, `tc (g : graph)`) | ``expected `{ node : type, edge : ⇑(node -> node -> rel) }`, found `int` `` |
| golden `neg/interfaces` (`b : more_sig = %import …`) | ``expected `{ shape : type, circle : ⇑shape }` `` |
| golden `neg/core_e0906_field` (`origin : point`) | ``note: `{ x : int, y : int }` has the fields `x`, `y` `` |
| golden `neg/core_e0901_occurs` | ``expected `?167`, found `(x' : ?167) -> ?168 x'` `` (numbers count the prelude's metas) |

The `vec3` row also shows an ordering limit that is not part of #66: definitions are elaborated before
the clauses of functions (`Items.elabDeclarations`), so `plus` has no case tree yet when `vec3` and `v`
are checked, and the correct `v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil))` is rejected. This needs its
own issue (clause groups in dependency order with definitions).

### 2.2 Conversion and meta solutions

`Unification.unify` forces both sides and compares. Definitions are already unfolded by evaluation, so
there is no choice to make. A neutral application of a clause function (`Rigid(Glob f)` stuck on a
neutral argument) is compared by its spine, which commits to an approximate solution: with `c` constant
(`c zero = zero. c (suc N) = zero.`) and `q : (x : nat) -> (y : nat) -> eqn (c x) (c y) -> nat`, the
clause `r Y = q _ Y refl` is accepted with `_ := Y`, a solution that nothing determines. Meta solutions
are read back by `Renaming.psubst` from forced values, so they contain unfolded definitions, and a meta
equated with a definition whose value is a lambda gets the eta-expanded body (the `(t1, Lam)` case of
`unify` comes before the `Flex` cases).

### 2.3 Metas leak across items

`Items.checkSolved` reports the metas of an item that are still unsolved at its end, except those with
`allowUnsolved` (holes, the types of object variables). Those stay solvable by every later item:

```text
t : Type = ?t.        (* E0924, goal `Type` *)
x : t = 5.            (* accepted: solves ?t := int *)
y : t = "s".          (* E0901: expected `int`, found `string` *)
```

`k : nat = ?k.` followed by `w : eqn k zero = refl.` is accepted the same way (`?k := zero`). The E0924
of the first item is still reported, but a later item changed what the hole means, and `y`'s message
names `int`, which the user never wrote.

Spike (uncommitted): `Core.solveMeta` logged every solution of a meta created before the current block
(`Items.attemptItem`, `elabItemReporting`, `elabClauseGroups`). `testOnly hugin.golden.GoldenTests`
(199 tests, the prelude included) and `testOnly hugin.core.* hugin.reference.* hugin.lsp.*
hugin.query.IncrementalSuite` (448 tests) logged nothing; the two programs above logged the hole. So no
accepted program depends on a cross-item solution.

Forks (`Core.fork`, #60) share metas copy-on-write so that an item's fork cannot change the declarations'
metas, and `ProgramElab.Moved` maps every meta below the base's count to itself. Both are correct only if
an item never solves a base meta; nothing enforces it.

### 2.4 Termination through definitions

`elab/SizeChange.recordCalls` collects calls from the syntax of a clause body: `Tm.Global(g)` with `g` a
function. A call through a definition is not seen:

```text
f : nat -> nat.
g : nat -> nat = [x] f x.
f zero = zero.
f (suc N) = g (suc N).        (* accepted, no E0912 *)
test : eqn (f (suc zero)) zero -> nat.
test refl = zero.             (* java.lang.StackOverflowError in Matching.reduceFunction *)
```

Written directly (`f (suc N) = f (suc N)`), the same function gets E0912. Today a meta solution is read
back unfolded, so a call reached through a solved implicit argument is visible; with glued solutions
(`?m := g`) it would not be.

## 3. Prior art

Read from source: AndrasKovacs/smalltt ea99b0f, AndrasKovacs/elaboration-zoo 9626d6c, lean4 0bb12a8
(clones, `--depth 1`). Idris 2: `src/Core/Normalise/Eval.idr`, `src/Core/Normalise.idr`,
`src/Core/Unify.idr` fetched from raw.githubusercontent.com (branch `main`, 2026-10-09), skimmed only.
Agda was not read and is not used as evidence.

### 3.1 smalltt

**Glued values.** `CoreTypes.hs`: `Val` has `VUnfold UnfoldHead Spine ~Val`; an `UnfoldHead` is a
top-level variable or a solved meta. `Evaluation.hs`, `eval'`: `TopVar x v` evaluates to
`VUnfold (UHTopVar x v) SId v`; `app` extends both branches, `VUnfold h (SApp sp u i) (app ms v u i)`,
the unfolded one lazily. A solved meta is `VUnfold (UHSolved x) …` as well (`meta`, `force'`). Three
forcing functions: `force` (solved metas at the head become `VUnfold`), `forceAll` (removes all
unfoldings), `forceMetas` (removes meta unfoldings only). `quote` takes a `QuoteOption`: `UnfoldAll`,
`UnfoldMetas`, `UnfoldNone`. `zonk` substitutes metas and keeps top-level names. The README, "Glued
evaluation", states the aim: quotation should produce terms "as small as possible" for meta solutions and
messages, with a single evaluator. "Paired values": `infer` and `check` pass `G {g1, g2}`, the least
reduced and the forced value of the same type; `check` forces `g2` to see a `VPi` and keeps `g1` for
printing and solutions (`Elaboration.hs`, `check`, `goInsert'`).

**Conversion states.** `Unification.hs`, `unify` (lines 321–382) with `ConvState` `Rigid`, `Flex`,
`Full` (`Common.hs`). `forceCS` uses `forceAll` in `Full` and `force` otherwise. Equal unfolding heads:
in `Rigid`, `unifySp … Flex` and on failure `unify … Full` on the unfolded values; in `Flex`, spines
only; different heads: `Rigid` unfolds, `Flex` fails. Every meta solution in `Flex` throws
`FlexSolution` (`guardCS`). The README ("Approximate conversion checking") says smalltt "does not allow
approximate meta solutions" and backtracks at most once per path. Eta-short solutions: `solve` is tried
first and `solveLong` (eta-expanding) only on failure (lines 363–371); `etaContract` trims common
trailing variables.

**Solution read-back.** `rigidQuote`, `flexQuote`, `fullCheckRhs` (lines 89–213): a solution never
unfolds a top-level name; an illegal variable inside the spine of an unfolding is checked again on the
unfolded value (`fullCheckRhs`), and if it disappears there the spine position becomes `Irrelevant`
(README, "Meta solution checking and quotation": `?0 = const {Bool}{Bool} true y` gives
`const … true Irrelevant`).

**Freezing.** `TopCxt.hs`, `define`: after each top-level definition, `frz` becomes the current number
of metas and is stored in `TopEntry`. `Unification.hs`, `solve`, line 283: `when (x < frz) $ throw $
UnifyEx $ FrozenSolution x`. `approxOccursInSolution` (line 52) treats every frozen meta as not
containing the occurring one, and caches per solved active meta. smalltt does not report unsolved metas
at the end of a definition; freezing only makes them unsolvable (README, "Meta freezing and approximate
occurs checking": blocks "where fresh metas are solvable", as in Agda).

### 3.2 elaboration-zoo

`GluedEval.hs` is the minimal form of 3.1: `VTop Name Spine ~Val`, `vapp` on both branches, `quote` with
a flag `UnfoldTop`. `05-pruning` (`Unification.hs`: `invert`, `pruneVFlex`, `intersect`, `flexFlex`) is
what `core/Renaming.scala` and `core/Unification.scala` port already; it has no glued values and no
freezing. `06-first-class-poly` postpones checking problems and retries them in `checkEverything`
(`Elaboration.hs`, line 67) after the whole term: postponement, which Hugin does not have and #66 does
not add.

### 3.3 Lean 4

- **Lazy delta reduction.** `Meta/ExprDefEq.lean`, `isDefEqDelta` (doc comment lists the rules 1–11):
  unfold the side that can be unfolded; with the same head, `unfoldBothDefEq` first tries
  `tryHeuristic` (arguments pairwise, under `checkpointDefEq`, which restores the meta context on
  failure, `Meta/Basic.lean`), then unfolds both; with different heads, `unfoldDefEq` compares
  definitional heights (`tInfo.hints.lt sInfo.hints`) and unfolds the higher one first. `tryHeuristic`
  assigns metas, so Lean admits approximate solutions (`S.proj ?x =?= S.proj t` in its comment).
- **Meta scoping.** `Meta/Basic.lean`, `withNewMCtxDepth`: metas of a lower depth are read-only
  (`MVarId.isReadOnly`), and the depth is restored afterwards; this nests (type class resolution, quoted
  pattern matching in Qq). Per declaration, `Elab/MutualDef.lean` runs
  `synthesizeSyntheticMVarsNoPostponing` after the bodies and reports what is still unassigned with
  `logUnassignedUsingErrorInfos`.
- **Printing.** The elaborator manipulates `Expr` terms and reduces only through explicit `whnf` calls,
  so `ppExpr` (`Meta/Basic.lean`, `ppExprWithInfos`) prints what elaboration built; there is no value
  domain to read back from, hence nothing to fold.

### 3.4 Idris 2

`Core/Normalise/Eval.idr`, `data Glued`: `MkGlue fromTerm (Core (Term vars)) (Ref Ctxt Defs -> Core (NF
vars))`, a term and its normal form, each computed on demand; `getTerm` for printing, `getNF` for
comparison; `gnf` builds one from a term. The elaborator passes expected types as `Glued`, the same role
as smalltt's `G`.

### 3.5 What the references agree on

1. The term shown to the user and used in meta solutions is the least unfolded one available; the
   unfolded form exists for comparison only (smalltt `G`, Idris 2 `Glued`, Lean by working on terms).
2. Same-head applications are compared by arguments before unfolding, with at most one fallback to
   unfolding (smalltt) or a height-guided order (Lean). smalltt forbids meta solutions in the speculative
   step; Lean allows them and restores the meta context on failure.
3. Metas are solvable only inside the unit that created them: smalltt's frozen blocks, Lean's depths and
   per-declaration reporting.

## 4. Design

### 4.1 Freezing (Batch 1)

- `Core.frozenBelow: Int`. `Items.attemptItem`, `Items.elabItemReporting` and `Items.elabClauseGroups`
  set it to `metas.length` at the start of the block and restore it after. Nested elaboration inside a
  block (module bodies, `where`-lifted functions, directives' items) belongs to the block and does not
  freeze.
- `solveMeta`, `pruneMeta` and `etaExpandMeta` assert `m >= frozenBelow`. `unify` treats a frozen
  unsolved meta as a rigid head: an active meta on the other side is solved with it, and a problem that
  needs a solution of the frozen one fails with `UnifyFailure.Frozen(m)`.
- A failure caused by a frozen *hole* is a cascade of the E0924 already reported: the item fails
  silently (`ElabError(silent = true)`, as for syntax errors). Any other frozen unsolved meta is an
  E0901 with the note "the unknown `?n` belongs to an earlier item". After #56 Batch A no such meta
  is left at a block end (its store solves the object types there); before it, the spike shows none.
- Order at a block end: the #56 constraint store of the block is solved, then `checkSolved(start)`, then
  the tooling flush, then freezing.
- **Forks.** A fork never writes a base meta, so the copy-on-write of `Core.fork` (`sharedBelow`,
  `owned`, `ownMeta`) becomes an assertion, and `ProgramElab.Moved.meta`'s identity mapping is justified
  by the invariant.
- **Meta numbers.** `Printing` prints `?k` with `k = m - blockStart` of the block in which the
  diagnostic is reported; metas of earlier blocks cannot appear unsolved in a later block's message
  except holes, which have names.

Assessments:

- *Block = top-level item and clause group.* Chosen: the reference already speaks of the item, and
  clause groups are elaborated as one unit with one undo (`elabClauseGroups`). Rejected: one block per
  file (smalltt README's suggested relaxation): it keeps today's leak and gains nothing measured.
  Rejected: nested depths as in Lean (`withNewMCtxDepth`): Hugin has no type classes or speculative
  sub-elaboration that needs read-only outer metas; the existing trail covers backtracking.
- *Frozen holes fail silently.* Chosen: the hole is already an error and compilation stops before
  staging. Rejected: smalltt's `FrozenSolution` error, which would report every use of the hole again.
- *Relative meta numbers.* Chosen: goldens no longer change when the prelude gains a meta. Rejected:
  global numbers (smalltt, Lean `?m.123`).

### 4.2 Glued values (Batch 2)

```scala
enum Val:
  …
  /** A definition applied to `sp` (applications and splices only), folded; `cell` holds the value
   *  with the definition unfolded, computed at most once. */
  case Top(id: Int, sp: Spine, cell: Unfold)

final class Unfold(thunk: () => Val):   // compared by identity
  lazy val value: Val = thunk()
```

- `eval(Tm.Global(id))` for a definition: `Top(id, Nil, Unfold(() => d))` with `d` the stored value (a
  strict cell; the definition's value is computed when it is defined, as now).
- `app(Top(id, sp, c), a, i) = Top(id, EApp(a, i) :: sp, Unfold(() => app(c.value, a, i)))`;
  `vSplice` and `vQuote` act on both branches the same way, so `⟨$t⟩ = t` holds on each.
  `proj(Top(…), l)` unfolds: projections out of module values show the member (`roads.node` is `city`,
  as hover shows module members today), and record definitions are module values in practice.
- `force` unfolds `Top` (and solved metas, and retries stuck functions, as now). `forceMetas` does the
  latter two and keeps `Top`.
- `quote(l, v, mode = Folded)`: `Folded` keeps `Top` as `Tm.Global(id)` applied to its spine;
  `Unfolded` is today's `quote`. `nf` keeps its meaning (unfolded): it is the staging function.
- **Unfolded read-back sites.** Staging and the handover (`Staging`, `handover/*`), `MemoKeys`
  (`closedKey`), `Families.familyInstance`, `SizeChange.matrix`, `SplitProblem.norm`,
  `telescopeOrder` and the deletion test of `IndexUnifier.unifyIndices`, reflection (`Reflection`,
  `Reflective`, `Primitives`: data values), the staging observer behind hover's "persisted: the
  compile-time value `42`" and expansion (`query/MetaIde`, `Expansion`). Everything else reads back
  folded: diagnostics, hover, inlay hints, goals, `--print-after elaborate`, meta solutions.
- **Clause functions stay eager.** `Evaluation.rigid` keeps reducing saturated applications through
  `reduceFunction` and its memo.

Assessments:

- *Glue definitions only.* Chosen. Clause functions are the meta level's computation and the staging
  engine; a thunk per call would cost on `meta_scaled` and `tc_chain` and bring back deep recursion when
  a chain of thunks is forced (the stack depth work of #88). A stuck clause-function application already
  prints folded (`plus N M`). Rejected for now: `Top` for clause functions (smalltt has only
  definitions, so it has no evidence either way); a follow-up if measurements show it pays.
- *`force` unfolds.* Chosen: every existing match after `force` sees what it sees today; folding is
  opt-in at the few sites that print or solve. Rejected: smalltt's naming (`force` keeps unfoldings),
  which would need every one of the 172 sites to be audited for the right forcing.
- *Projections unfold, applications and splices fold.* Chosen: object type aliases
  (`name : type = string`, used as `$name`) and type-level definitions print as written, while module
  paths keep today's display. Rejected: folding projections too (changes the hover of every module
  member).
- *No paired `G` values in the elaborator.* `Top` already carries both forms, and the elaborator keeps
  the unforced expected type for its messages; smalltt's `G` saves forcing the same value twice, and
  forcing a `Top` again here reads a computed cell. Rejected: threading `G` through `check` and `infer`
  (large change for the same output).

### 4.3 Conversion states (Batch 3)

`unify(l, t, u, cs = Rigid)`; `forceCS` is `force` in `Full` and `forceMetas` otherwise.

| case | `Rigid` | `Flex` | `Full` |
|---|---|---|---|
| `Top(f, sp)`, `Top(f, sp')` | spines in `Flex`; on failure both unfolded in `Full` | spines in `Flex` | unfolded by `forceCS` |
| `Top(f, …)`, `Top(g, …)`, `f ≠ g` | unfold the larger id, stay `Rigid` | fail | unfolded by `forceCS` |
| `Top`, other | unfold the `Top`, stay `Rigid` | fail | unfolded by `forceCS` |
| `Flex(m, sp)`, other | solve (folded right-hand side), on failure eta-expand and retry | fail (`FlexSolution`) | solve |
| `U1(a)`, `U1(b)` | `levels.eq` | `levels.entails(a = b)`, no new constraint | `levels.eq` |
| rest | as today | as today | as today |

- The `Flex`/other case is tried before the eta cases when the other side is a `Top`, so `?m =? f`
  solves `?m := f`.
- `psubst` (solution read-back) keeps `Top`s; an escape or occurs failure inside a `Top`'s spine is
  retried on the unfolded value, which then appears unfolded in the solution.
- The retry after a failed eta-short solution runs under `Core.undoOnFailure`, because pruning and
  eta-expansion in the first attempt may have solved metas. The `Flex` attempt itself changes nothing
  and needs no checkpoint.
- **Stuck clause functions.** A `Rigid(Glob f)` that does not reduce is compared by its spine in every
  state, as today (Lean's choice). The `c`-example of 2.2 stays accepted.
- **Messages.** `mismatch` prints expected and found folded. If both print the same folded text, it
  prints both unfolded (the rule that already adds the stage note when `e == fo`).

Assessments:

- *One-shot speculation (smalltt).* Chosen: the README reports no benefit from more shots, and the cost
  of a failed attempt is bounded by one spine comparison. Rejected: Lean's full heuristic list
  (projections, reducibility attributes, `match` auxiliaries), which have no counterpart in Hugin.
- *Larger id first.* A definition refers only to globals elaborated before it (E0105 and
  `elabInDependencyOrder`), so the global id bounds the definitional height; this is Lean's height rule
  without stored heights. With `alias2 = vec2`, the problem `alias2 =? vec2` unfolds `alias2` once and
  ends in an equal-head step. Rejected: unfolding both sides (smalltt), which compares `vec2` with
  `vec int two` and unfolds again down to the rigid head.
- *Keep approximate solutions for stuck clause functions.* Chosen: rejecting them needs postponement,
  which the elaborator does not have (3.2), and would reject programs that pass today. Rejected:
  smalltt's strict policy, for this reason. In `Flex` they cannot arise, since no meta is solved there.
- *`Irrelevant` placeholders in solutions (smalltt).* Rejected: a new term and value node and a
  unification rule for one rare case; the unfolded retry gives a correct, slightly larger solution.

## 5. Interactions

- **Stages, `⇑`, splices.** `Top` spines hold `EApp` and `ESplice`, so `$code` and `⟨$t⟩ = t` work
  on both branches; `Lift(Top …)` prints `⇑vec2`. `persist` and the Lift rule (`elab/Liftings`) force
  first, so persisted literals and lifted shared data are computed from the unfolded value. Staging is
  normalisation with `quote(Unfolded)`, so staged items are identical, and the staging observer reports
  unfolded values.
- **Reflection and quotes.** Quotes are reified from syntax (`QuoteTerms`), not from values, and
  reflected data is read with `forceData`, which unfolds. #56 Batch B reifies quote content from the
  elaborated core term; that reification must use the unfolded read-back. `quoted` (#56, 4.6) must be
  a postulated type former, not a definition `quoted A = term`: as a definition, unfolding would forget
  the index, and Batch 3 would accept `quoted τ =? quoted σ` after the `Flex` attempt fails.
- **Index unification (Cockx & Abel).** `unifyIndices` forces with unfolding and decides deletion on
  unfolded normal forms, so solutions, conflicts and E0915 are as today; the `Stuck` pair of E0915 is
  printed folded. `SplitProblem.norm` (eval of read-back) may use the folded read-back: re-evaluation
  recreates the `Top`s, and the split types in E0911 and goals print folded.
- **Size-change termination.** Batch 0 makes `recordCalls` see through definitions: a `Tm.Global(g)`
  with `g` a definition is visited as the body of `g` applied to the arguments (definitions are not
  recursive, E0105, so this terminates). Matrices compare unfolded normal forms, so the accepted set of
  functions changes only by the fix.
- **The undo log and trails (#60).** Freezing bounds the trail: every entry has `m >= frozenBelow`, and
  rolling back an item removes its metas as now. `Flex` writes nothing, so speculation needs no
  checkpoint; the level graph is protected by the check-only `entails`. The retry of 4.3 uses the
  existing trail.
- **Incrementality.** With freezing, the result of a block depends only on the blocks before it, which
  is what `ProgramElab` assumes when it elaborates object items in forks and moves them
  (docs/INCREMENTALITY.md); it is also a precondition for elaborating declarations one by one later.

## 6. Effects

### 6.1 Before and after

| where | today | after |
|---|---|---|
| `--print-after elaborate`, `w = ident v.` | `w : vec int (suc (suc zero)) = ident {vec int (suc (suc zero))} v.` | `w : vec2 = ident {vec2} v.` |
| the same, `l = len v.` | `len {int} {suc (suc zero)} v` | `len {int} {two} v` |
| `h = ident g.` | `h : { node : ⇑type, edge : … } = ident {{ … }} g.` | `h : graph = ident {graph} g.` |
| hover on `w` | `w : vec int (suc (suc zero))` | `w : vec2` |
| E0901, `v : vec3 = …` | ``expected `vec int (plus (suc zero) (suc (suc zero)))` `` | ``expected `vec3` `` |
| E0901, `bad4 = tc 5.` | ``expected `{ node : type, edge : ⇑(node -> node -> rel) }` `` | ``expected `graph` `` |
| E0204, `b : more_sig = …` | ``expected `{ shape : type, circle : ⇑shape }` `` | ``expected `more_sig` `` (the note names the missing field, as now) |
| E0906 note | `` `{ x : int, y : int }` has the fields `x`, `y` `` | `` `point` has the fields `x`, `y` `` |
| E0901 occurs check | `` `?167` ``, `` `(x' : ?167) -> ?168 x'` `` | `` `?3` ``, `` `(x' : ?3) -> ?4 x'` `` (the prelude leaves 164 metas) |
| `t : Type = ?t. x : t = 5. y : t = "s".` | E0924, then E0901 ``expected `int` `` at `y` | E0924 only |
| `f (suc N) = g (suc N)` with `g = [x] f x` | accepted, stack overflow at use | E0912 |

### 6.2 Goldens

- Batch 0: a new negative golden (E0912 through a definition).
- Batch 1: `neg/core_e0901_occurs` (meta numbers); a new negative golden for the hole leak.
- Batch 2: `neg/meta_types` (two diagnostics), `neg/interfaces` (three labels and the E0906 note),
  `neg/core_e0906_field`; `--print-after elaborate` goldens wherever an inferred type or implicit
  argument comes from a definition (`run/core_b1_readme`, `run/core_b2_*`: to be reviewed one by one);
  no LSP golden found with an unfolded definition (their inputs annotate types). Staged output,
  `hugin run` output and `--print-after stage` do not change.
- Batch 3: smaller implicit arguments in `--print-after elaborate` where a solution was eta-expanded or
  unfolded; no change in accepted programs is expected, and `IncrementalSuite` and the fuzz suites
  (short run) guard it.

### 6.3 Performance

Expected: no regression, small gains in elaboration. Sources of gain: equal definitions compare in one
spine step instead of after evaluation; meta solutions are smaller, so `zonk`, `MemoKeys` and printing
do less; freezing removes the copy-on-write bookkeeping of forks. Costs: one `Top` and one cell per
reference to a definition, one thunk per application of a definition, and an indirection when staging
forces them. Clause functions, the bulk of meta computation (`meta_scaled`, `tc_chain`), are untouched.
Acceptance: the bench harness of docs/PERFORMANCE.md ("Method"), warm, after each of Batches 2 and 3; no
program more than 5 % slower than before. If `gen_large` or the uncached prelude regress, the fallback
is a strict cell for nullary definitions (most of them) and thunks only for applied ones.

## 7. Sequencing with #56

| file or area | #56 Batch A | #66 |
|---|---|---|
| `elab/Items.scala`, block ends | solves the object-type store at clause, definition and item ends | freezing (B1) at the same points, after the store |
| `Val` (new case) | `core/objtype/ObjTypes` matches on values | `Val.Top` (B2) adds a case to every exhaustive match |
| `elab/Coercions.scala` | covariant `⇑` (subsumption in `coe`) | `unify` gains a state parameter with a default (B3); no call changes |
| `core/Unification.scala` | none planned | B3 |
| `QuoteTerms`, `quoted` (#56 Batch B) | reification from core terms | B2's unfolded read-back; `quoted` not a definition (5) |

Order:

1. Batch 0 (size-change through definitions): independent bugfix, any time.
2. #56 Batch A.
3. #66 Batch 1 (freezing): after A, so that freezing runs after A's store is solved and no object-type
   meta is frozen unsolved. The textual conflict in `Items.scala` is a few lines.
4. #66 Batch 2 (glued values): after A, so the new `Val` case is added once to A's `ObjTypes`; with
   `force` unfolding, A's code needs only the exhaustivity cases, not a semantic review.
5. #56 Batch B and #66 Batch 3 in either order; the conflict is limited to `Unification.scala`
   against `QuoteTerms.scala` and is not semantic.

## 8. Batches

| batch | content | files | size |
|---|---|---|---|
| 0 | calls through definitions in the meta size-change check; negative golden | `elab/SizeChange` | +40/−5 |
| 1 | `frozenBelow`, assertions, `UnifyFailure.Frozen`, silent cascade for frozen holes, relative meta numbers, fork copy-on-write replaced by an assertion; goldens; `BacktrackingSuite` fork test updated | `Core`, `Unification`, `Renaming`, `elab/Items`, `elab/ElabErrors`, `Printing` | +150/−70 |
| 2 | `Val.Top`, `Unfold`, `forceMetas`, read-back modes, unfolded read-back at the sites of 4.2, display fallback, folded `psubst` with unfolded retry; goldens; a suite that compares staged output and memo keys with and without gluing on all goldens | `Value`, `Evaluation`, `Readback`, `Renaming`, `Printing`, `MemoKeys`, `Families`, `Staging`, `handover/*`, `elab/{SizeChange,SplitProblem,Clauses,ElabErrors,Reflection}`, `query/MetaIde` | +450/−120 |
| 3 | `ConvState`, `forceCS`, `levels.entails`, height order, eta-short solutions, retry under `undoOnFailure`; benches; reference unchanged (no language change) | `Unification`, `Levels`, `Renaming` | +250/−60 |

No batch changes the language; the reference needs no change. docs/NOTES.md gets a section "Glued
evaluation and frozen metas (#66)", and docs/PERFORMANCE.md the numbers of Batches 2 and 3.

## 9. Sources

- smalltt ea99b0f: `README.md` (sections "Glued evaluation", "Approximate conversion checking", "Paired
  values", "Eta-short meta solutions", "Meta solution checking and quotation", "Meta freezing and
  approximate occurs checking"), `src/CoreTypes.hs`, `src/Evaluation.hs`, `src/Unification.hs`,
  `src/Elaboration.hs`, `src/TopCxt.hs`, `src/MetaCxt.hs`, `src/Common.hs`, `src/Exceptions.hs`.
- elaboration-zoo 9626d6c: `GluedEval.hs`, `05-pruning/{README.md,Unification.hs}`,
  `06-first-class-poly/{Elaboration.hs,Metacontext.hs}`.
- lean4 0bb12a8: `src/Lean/Meta/ExprDefEq.lean` (`isDefEqDelta`, `unfoldBothDefEq`, `tryHeuristic`,
  `unfoldDefEq`, `isDefEqDeltaStep`), `src/Lean/Meta/Basic.lean` (`withNewMCtxDepth`,
  `MVarId.isReadOnly`, `checkpointDefEq`, `ppExpr`), `src/Lean/Elab/MutualDef.lean`.
- Idris 2 `main` (raw files, 2026-10-09): `src/Core/Normalise/Eval.idr` (`Glued`, `gnf`),
  `src/Core/Normalise.idr`, `src/Core/Unify.idr`.
- Hugin f05ee62: `core/{Value,Evaluation,Readback,Unification,Renaming,Core,Matching}.scala`,
  `core/{Printing,ProgramElab}.scala`,
  `core/elab/{Items,ElabErrors,SizeChange,SplitProblem,Clauses}.scala`; docs/PERFORMANCE.md ("Prior art",
  "Other opportunities found" 3–5); `docs/design/typed-object-code.md` at 1ed48bb on
  `feat/typed-object-56`.
