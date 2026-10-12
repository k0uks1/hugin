# Level 3.5: relations as propositions (P9)

Design note for batch P9 of [issue #186](https://github.com/k0uks1/hugin/issues/186), the follow-up that
decision D14 of the [proofs note](proofs.md) left "design first": a relation of a program used directly
as a meta-level proposition, by derived abbreviations, with no change to the core. Status: **proposal,
awaiting the designer's approval**; nothing here is implemented. Written against `ccr-48027e29-daam41` at
1db9441, after P1–P7b and P6 merged.

The note is a file of its own, linked from the proofs note's chapter 10, for three reasons. It is a
separate design round with its own approval, as chapter 10 recorded. The proofs note has about 2300 lines, and its
chapters 1–9 describe a plan that is now implemented, so a new end state belongs in a new chapter 1. And
§15 of the proofs note keeps recording implementation decisions, which this note does not touch until it
is approved.

**What was compiled.** The "today" programs in §1 and the probes in §2.2 were checked with today's
compiler (`hugin check`/`run` at 1db9441); the level 3.5 programs were not, because level 3.5 does not
exist yet. Probes with surprising results are listed in §2.2 and quoted in full in §6.2 and §6.3.

**Keywords.** Level 3.5 adds **no keyword, no token and no directive**. The words that matter in the
examples are: the token `⊢` (ASCII `|-`, P7b); the contextual names `given` and `programOf` (P7a, P7b),
which are names, not keywords, unless the program declares them; the keywords `match`, `rewrite` and
`with` (P3); the directives `%use`, `%opaque` and `%input`. Everything else in the examples is an ordinary
name: `path`, `tc`, `derives`, `decide`, `iff`.

Contents: 1 the end state, 2 what level 3.5 is, 3 prior art, 4 alternatives, 5 costs, 6 the open flags
(`decide`, multi-head rules, negation), 7 batches, 8 decisions for the designer, 9 sources.

## 1. The end state

**The rule in one sentence.** *An atom whose relation belongs to a program, written where a meta type is
expected, is that program's judgment at the database `d`.* For example, `fast.path x y` is `fast ⊢ path x
y`, `(tc2 g).path x y` is `tc2 g ⊢ path x y`, and `tc2.path x y` is `tc2 ⊢ path x y`, with `g` and `d`
generalised as P7b generalises them. The rule is a coercion that elaboration inserts by the expected type,
as stage inference inserts `⇑`, quotes and splices today. It generates no declaration, no family and no
lemma.

So `path x y` alone does **not** mean `tc ⊢ path x y`: `tc` and `tc2` both have a relation `path`, and the
name alone does not say which program is meant. A bare name is a proposition only if it names a relation
of one module instance, for example after `%use trip (path).` (§2.3).

### 1.1 Proof A: the doubling closure derives the same paths

Today (P7b, `tests/run/p7b_proof_a.hgn`, which compiles and runs):

```hugin
edgeIn : {x y : g.node} -> tc ⊢ g.edge x y -> tc2 ⊢ g.edge x y.
edgeIn (given I) = given I.
edgeOut : {x y : g.node} -> tc2 ⊢ g.edge x y -> tc ⊢ g.edge x y.
edgeOut (given I) = given I.

tcTrans : {x y z : g.node} -> tc ⊢ path x y -> tc ⊢ path y z -> tc ⊢ path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

toTc2 : {x y : g.node} -> tc ⊢ path x y -> tc2 ⊢ path x y.
toTc2 (path.1 E) = path.1 (edgeIn E).
toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).

toTc : {x y : g.node} -> tc2 ⊢ path x y -> tc ⊢ path x y.
toTc (path.1 E) = path.1 (edgeOut E).
toTc (path.2 P Q) = tcTrans (toTc P) (toTc Q).

sameFacts : {x y : g.node} -> iff (tc ⊢ path x y) (tc2 ⊢ path x y) = { to = toTc2, from = toTc }.
forFast : {x y : city} -> iff (tc { node = city, edge = road } ⊢ path x y) (fast ⊢ path x y) = sameFacts.
%opaque sameFacts forFast.
```

With level 3.5 (proposal):

```hugin
edgeIn : {x y : g.node} -> tc ⊢ g.edge x y -> tc2 ⊢ g.edge x y.      (* unchanged: g.edge is a parameter *)
edgeIn (given I) = given I.
edgeOut : {x y : g.node} -> tc2 ⊢ g.edge x y -> tc ⊢ g.edge x y.
edgeOut (given I) = given I.

tcTrans : {x y z : g.node} -> tc.path x y -> tc.path y z -> tc.path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

toTc2 : {x y : g.node} -> tc.path x y -> tc2.path x y.
toTc2 (path.1 E) = path.1 (edgeIn E).
toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).

toTc : {x y : g.node} -> tc2.path x y -> tc.path x y.
toTc (path.1 E) = path.1 (edgeOut E).
toTc (path.2 P Q) = tcTrans (toTc P) (toTc Q).

sameFacts : {x y : g.node} -> iff (tc.path x y) (tc2.path x y) = { to = toTc2, from = toTc }.
forFast : {x y : city} -> iff ((tc { node = city, edge = road }).path x y) (fast.path x y) = sameFacts.
%opaque sameFacts forFast.
```

What changed: the statements about the programs' own relations drop the turnstile; `tc.path x y` reads
"the relation `path` of `tc` holds of `x` and `y`". What did not change: every clause, every rule name,
the generalised binders (`{d : db} -> {g : graph}`, from `tc` and `tc2` written alone), and the elaborated
types, which are the same `derives (programOf (tc g)) d (atom (own 0) [v x, v y])` as today. `edgeIn` and
`edgeOut` keep the turnstile, because `g.edge` is the parameter's relation and belongs to no program
(§2.3). `forFast` shows the two other forms: a functor application, `(tc { … }).path`, and an instance,
`fast.path`.

### 1.2 Proof B: the analysis over-approximates

Today (P7b, `tests/run/p7b_proof_b.hgn`, which compiles):

```hugin
placed (d : db) (a : abstraction) : Type =
  (x : a.node) -> coarse a ⊢[d] reached x -> { b : a.anode, ok : coarse a ⊢[d] a.alpha x b }.

sound : placed d a -> {x : a.node} -> {b : a.anode} ->
        coarse ⊢ reached x -> coarse ⊢ a.alpha x b -> coarse ⊢ areached b.
sound T (reached.1 S) H = areached.1 S H.
sound T (reached.2 {X := W} R E) H = areached.2 (sound T R (T W R).ok) (aedge.1 E (T W R).ok H).

safe : placed d a -> {x : a.node} -> {b : a.anode} ->
       (coarse ⊢ areached b -> empty) -> coarse ⊢ a.alpha x b -> coarse ⊢ reached x -> empty.
safe T N H R = N (sound T R H).
%opaque sound safe.
```

With level 3.5 (proposal):

```hugin
placed (d : db) (a : abstraction) : Type =
  (x : a.node) -> (coarse a).reached x -> { b : a.anode, ok : coarse a ⊢ a.alpha x b }.

sound : placed d a -> {x : a.node} -> {b : a.anode} ->
        coarse.reached x -> coarse ⊢ a.alpha x b -> coarse.areached b.
sound T (reached.1 S) H = areached.1 S H.
sound T (reached.2 {X := W} R E) H = areached.2 (sound T R (T W R).ok) (aedge.1 E (T W R).ok H).

safe : placed d a -> {x : a.node} -> {b : a.anode} ->
       (coarse.areached b -> empty) -> coarse ⊢ a.alpha x b -> coarse.reached x -> empty.
safe T N H R = N (sound T R H).
%opaque sound safe.
```

In `placed`, `(coarse a).reached x` uses the parameter `d` of `placed`, because a coerced atom, like a
judgment without `[e]`, uses the `d` in scope (§2.4); `[d]` was never needed there. The input relation
`a.alpha` keeps the turnstile. In `sound` and `safe`, `coarse.reached` generalises `a` and `d` as `coarse ⊢`
does, so `placed d a` refers to the same binders.

### 1.3 A relation passed to a generic combinator: an undirected graph is symmetric

The two proofs above only shorten statements. This example shows what the abbreviation adds: a relation
can be passed, unapplied, where a meta relation `A -> A -> Type` is expected, as stage inference already
passes an object relation where a formula function is expected (reference `meta/staging.md`, "Stage
inference": "Functions are converted by eta-expansion").

Today (checked: compiles and runs at 1db9441):

```hugin
%use "std/graph" (graph).
%use "std/semantics".

symmetric : {A : Type} -> (A -> A -> Type) -> Type.
symmetric {A := T} R = (x : T) -> (y : T) -> R x y -> R y x.

undirected (g : graph) = {
  link : g.node -> g.node -> rel.
  link X Y :- g.edge X Y.
  link Y X :- g.edge X Y.
  reach : g.node -> g.node -> rel.
  reach X Y :- link X Y.
  reach X Z :- link X Y, reach Y Z.
}.

linkSym : {x y : g.node} -> undirected ⊢ link x y -> undirected ⊢ link y x.
linkSym (link.1 E) = link.2 E.
linkSym (link.2 E) = link.1 E.

reachTrans : {x y z : g.node} -> undirected ⊢ reach x y -> undirected ⊢ reach y z -> undirected ⊢ reach x z.
reachTrans (reach.1 L) Q = reach.2 L Q.
reachTrans (reach.2 L P) Q = reach.2 L (reachTrans P Q).

reachSym : symmetric ([x] [y] undirected ⊢ reach x y).
reachSym X Y (reach.1 L) = reach.1 (linkSym L).
reachSym X Y (reach.2 {Y := W} L R) = reachTrans (reachSym W Y R) (reach.1 (linkSym L)).
%opaque linkSym reachTrans reachSym.
```

With level 3.5 (proposal), only the statements change:

```hugin
linkSym : symmetric undirected.link.
linkSym X Y (link.1 E) = link.2 E.
linkSym X Y (link.2 E) = link.1 E.

reachTrans : {x y z : g.node} -> undirected.reach x y -> undirected.reach y z -> undirected.reach x z.
reachTrans (reach.1 L) Q = reach.2 L Q.
reachTrans (reach.2 L P) Q = reach.2 L (reachTrans P Q).

reachSym : symmetric undirected.reach.
reachSym X Y (reach.1 L) = reach.1 (linkSym _ _ L).
reachSym X Y (reach.2 {Y := W} L R) = reachTrans (reachSym W Y R) (reach.1 (linkSym _ _ L)).
%opaque linkSym reachTrans reachSym.
```

`symmetric undirected.reach` elaborates to `{d : db} -> {g : graph} -> symmetric {⇑g.node} ([x] [y]
undirected g ⊢ reach x y)`, the type that today's version has (its `--print-after elaborate` output is
`symmetric {⇑$(g.node)} ([x] [y] derives (([x0] programOf undirected x0) g) d (atom (own 1) …))`). The
combinator is an ordinary meta function: a library of relation properties (`symmetric`, `transitive`,
`included`, `sameRel`) applies to object relations without a lambda per use. `linkSym` now takes the two
nodes explicitly, because `symmetric` quantifies them explicitly.

### 1.4 An instance opened by `%use`, proved by evaluation

Today (P7b, `tests/run/p7b_rules.hgn`): `viaParis : trip ⊢ path berlin rome = decide 3 tt.` With level 3.5,
both of the following are the same declaration (proposal):

```hugin
viaParis : trip.path berlin rome = decide 3 tt.

%use trip (path).
viaParis : path berlin rome = decide 3 tt.
```

After `%use trip (path).`, the name `path` denotes the relation constant of the instance `trip`, and the
coercion finds its program from the instance the constant belongs to. Today the second form is E0905
("`path` cannot be applied: its type `⇑(city -> city -> rel)` is not a function type", checked).

### 1.5 What the editor shows

Hovers and goals print the elaborated judgment, as today: the hole in

```hugin
toTc : {x y : g.node} -> tc2.path x y -> tc.path x y.
toTc (path.2 P Q) = ?.
```

shows `goal: tc g ⊢ path x y` and `P : tc2 g ⊢ path x Y`, exactly the output that P7b gives for the
turnstile form (checked for `tc ⊢ path x y -> tc ⊢ path y x`: `goal: tc g ⊢ path y x`). Case splits offer
`path.1 E` and `path.2 P Q` as today. A relation that belongs to no program is an error with a help that
names the fix (proposal: code and text):

```text
error[E0960]: `g.edge x y` is not a type: no program declares the relation `g.edge`
 --> closure.hgn:3:28
  |
3 | edgeIn : {x y : g.node} -> g.edge x y -> tc2 ⊢ g.edge x y.
  |                            ^^^^^^^^^^ a relation of the parameter `g`
  |
  = note: an applied relation is a proposition of the program that declares it
  = help: name the program: `tc ⊢ g.edge x y`
```

## 2. What level 3.5 is

### 2.1 The rule

Level 3.5 is one elaboration rule, the **judgment coercion**, plus its eta form. Written as rules of the
bidirectional elaborator (`⇐` checks against a type, `⇝` is the elaborated term):

```text
  r is a relation, struct or constructor owned by the program P   (§2.3)
  r has the columns τ₁ … τₙ, n ≥ 1        Γ ⊢ tᵢ ⇐ ⇑τᵢ  ⇝  uᵢ        d : db in Γ
  ------------------------------------------------------------------------------------- (coerce)
  Γ ⊢ r t₁ … tₙ ⇐ Type ℓ   ⇝   derives (programOf P) d (atom ρ [v u₁, …, v uₙ])

  the same premises, with the arguments missing
  ------------------------------------------------------------------------------------- (coerce-η)
  Γ ⊢ r ⇐ (x₁ : ⇑τ₁) -> … -> (xₙ : ⇑τₙ) -> Type ℓ   ⇝   [x₁] … [xₙ] P ⊢ r x₁ … xₙ
```

`ρ` is the reference that P7b's atom resolution gives `r` in `P` (`own i` for the program's own
relations). The right-hand sides are exactly the terms that `P ⊢ r t̄` elaborates to: the implementation
builds the `Judgment` tree and calls P7b's `inferJudgment`, so column typing, `⇑` covariance, arity
errors, and generalisation behave as for the turnstile. "Where a meta type is expected" means both
checking against a universe (`check` with `isUniverse(a)`, which sets `state.typePosition`) and inferring a
type (`inferU`, used for arrow domains and codomains, binder types and declared types), the two places
where `⇑` is inserted for object types today.

**No core change.** The core sees `derives`, the family of `std/semantics`; the coercion is a rewrite of
the surface syntax before checking, as P7b's notation is. Consistency, coverage, termination and conversion
are untouched.

### 2.2 Today these programs are accepted, with a meaningless type

The slot that the coercion takes is not free today. An applied relation in a meta type position elaborates
to `⇑(r t̄)`, the lift of an *applied fact type*, which is not an object type (reference
`object/types.md`, "Fact types": the fact type of `r` is the constant `r` alone). The object level rejects
the same text (E0909: "`road berlin paris` is not an object type"), but the meta level accepts it silently,
because a type under `⇑` is not checked until it is staged, and a meta type never is. Checked at 1db9441:

| written in a meta type | elaborated today | inhabitants |
|---|---|---|
| `fast.path x y` (instance) | `⇑($(fast.path) $x $y)` | none in closed code: an object term of a relation has the fact type `fast.path`, which never unifies with an application |
| `(tc g).path x y` (functor application) | `⇑($((tc g).path) $x $y)` | none |
| `g.edge x y` (parameter relation) | `⇑($(g.edge) $x $y)` | none |
| `fast.path` at `⇑city -> ⇑city -> Type` | `[_] [_] ⇑($(fast.path) $_ $_)` | none |
| `path x y` after `%use trip (path).` | E0905, "not a function type" | |
| `tc.path x y` (functor alone, `g` bound) | E0107, "`tc` is not a module" | |

A declaration such as `t : {x y : city} -> fast.path x y -> fast.path x y. t P = P.` is accepted today and
proves nothing. Level 3.5 therefore changes the meaning of accepted programs, but only of programs whose
types have no closed inhabitants. The batch plan makes this a step of its own (P9a, §7): first the applied
fact type under `⇑` becomes an error, then the coercion gives the slot its meaning. The unapplied fact type
keeps its meaning: `w : fast.path = <fast.path berlin paris>.` is a fact identity, as today (checked:
elaborated as `w : ⇑$(fast.path) = ⟨$(fast.path) berlin paris⟩`).

### 2.3 Which program

The program is the one that *declares* the relation, found from the head of the atom without evaluating
anything (so no functor application creates an instance; D10, P7b's "program kind from the head's declared
type"):

| written | the relation belongs to | elaborates to | generalised |
|---|---|---|---|
| `fast.path x y`, `fast` an instance (`fast = tc2 { … }`) | the instance `fast` | `fast ⊢ path x y` | `d` |
| `trip.path berlin rome`, `trip` a module value (`trip = { … }`) | the module `trip` | `trip ⊢ path berlin rome` | `d` |
| `weak.v.vertex x`, a member instance (reference `modules.md`, "Instances") | the instance `weak.v` | `weak.v ⊢ vertex x` | `d` |
| `path x y` after `%use fast.` or `%use trip (path).` | the instance whose constant `path` denotes | `fast ⊢ path x y` | `d` |
| `(tc2 g).path x y`, any functor application | the application | `tc2 g ⊢ path x y` | `d` |
| `tc2.path x y`, a functor written alone | the functor at its parameters | `tc2 ⊢ path x y`, that is `tc2 g ⊢ path x y` | `d`, `g` |
| `fast.path` where `⇑city -> ⇑city -> Type` is expected | the instance `fast` | `[x] [y] fast ⊢ path x y` | `d` |

The following are **not** coerced; they are E0960 with a help that names the turnstile form:

- *A parameter's relation*, `g.edge x y` or `a.alpha x b`. Its reference `arg l` is relative to the program
  (P7a: `arg "edge"`, or `arg "g.edge"` when the body has several environment variables), every program
  over `g` reads it, and the same text would denote a different judgment in `tc` and in `tc2`. Write `tc ⊢
  g.edge x y`.
- *A relation of the file*, `road x y`. Its program is the file's, `programOf here`, which P7a deferred.
  When `here` lands, the coercion covers it with no new rule: `road x y` is `here ⊢ road x y`.
- *A relation of the body a proof is written in.* A member function of `tc2`'s body that states `path x
  y` would mean `tc2 g ⊢ path x y` with the functor's own parameter, as a lemma inside an Isabelle
  `context tc begin … end` block sees the locale's predicates unqualified. Reading the enclosing body's
  rules from inside it needs the same elaboration phase as `programOf here` (the body's object items are
  elaborated after its meta members), so it is deferred with `here`.
- *A relation computed by a meta function* (a family of object constants, `len[int]`): no program declares
  it syntactically.
- *A nullary relation*, `fast.flag`: as a type it is the fact type `⇑fast.flag`, whose single value is the
  fact's identity, as today. The proposition is `fast ⊢ flag`.

### 2.4 Which database

Always the variable `d`: in a declaration's type the generalised `{d : db}`, elsewhere the `d` in scope (a
parameter named `d`, as in `placed`, or a generalised binder in a clause). No `d` is E0947, as for the
turnstile. A judgment at another database is written `P ⊢[e] r t̄`; level 3.5 has no form for it, by design:
the abbreviation exists for the common case, and `[e]` keeps the explicit database visible, as Beluga's
contextual types `[Ψ ⊢ M]` keep their context visible.

### 2.5 Generalisation

P7b collects the `Judgment` nodes of a declaration's type and parameter types before elaborating them
(`Judgments.generalisedBinders`). P9b extends the collection with the coercion's candidates, also
syntactically, so that no type is elaborated twice:

- `f.r`, applied or not, with `f` a functor, is always a candidate, since it has no other meaning: it
  generalises `f`'s parameters by name, merged with other functors' parameters of the same name and type,
  exactly as `f ⊢` does (E0946 on a type clash).
- Any candidate (`f.r`, `m.r`, `(f ā).r`, an opened instance relation) applied to at least one argument and
  standing in a *syntactic type position* asks for `{d : db}`. The syntactic type positions are: the
  declared type itself, an arrow's domain and codomain, a binder's type, and an argument of a global
  constant whose parameter type is a universe or a Π type ending in one (`iff`, `symmetric`), read from the
  constant's declared type.

A coercion that happens elsewhere (an argument of a local function variable `F (fast.path x y)`) needs a
`d` in scope, and is E0947 otherwise, with the help to write `⊢[e]` or to bind `{d : db}`. Lean 4 solves
the same problem differently: an auto-bound implicit is found by an "unknown identifier" during elaboration,
and the header is elaborated again with the binder added (`Lean.Elab.Term.withAutoBoundImplicit`). The
syntactic rule is chosen because it keeps P7b's single pass and gives a predictable error.

### 2.6 Rule names, `given`, `match`, `rewrite`, `decide`

All unchanged, because the elaborated types are identical to the turnstile's:

- *Rule names* `r.k`, labels and `given` are resolved against the expected derivation type (P7b), so they
  work below coerced types without qualification. The per-relation pattern synonyms that chapter 10.1 of
  the proofs note sketched, `pattern (tc2 g).path.base E = path.1 E`, are not needed: a label `@base` on
  the rule already names it (P7b, `tests/run/p7b_rules.hgn`).
- *`match` and `rewrite`* abstract over normal forms (P3), which are `derives …`; a variable `x` of the goal
  is found inside `v {g.node} ⟨$x⟩` as today.
- *`decide n tt`* proves `trip.path berlin rome` as it proves `trip ⊢ path berlin rome`: its type is
  `so (holds n p a) -> derives p d a`, unified with the coerced goal.
- *Coverage and case splits* see `derives` and split into the program's rules (P7b's Π extension).
- *Termination*: premises are below `fire`, as before.

### 2.7 Hovers and printing

The printer is independent of the scope of a file (P2b's decision for operators), so it cannot know
whether a judgment was written with a turnstile or as an atom. It keeps printing the canonical form `tc g ⊢
path x y`. This also shows the program and, when it is not `d`, the database, which the atom form cannot
show. Hover on the relation name of a coerced atom shows the relation (go to definition goes to its
declaration), and hover on the atom shows the judgment, as Lean shows an inserted coercion (`↥s`) instead
of hiding it.

### 2.8 Negation and aggregates

A coerced atom elaborates to whatever `P ⊢ r t̄` elaborates to. Today that is `derives`, the positive
fragment, also for programs with negations; §6.3 shows that this is wrong, and proposes a stop-gap error
(P9a) and the stratified reading (P9c). Both apply to the coercion unchanged.

### 2.9 Name resolution and ambiguity

The coercion introduces **no name**. The head of an atom is resolved exactly as today (shadowing by the
file, `%use` conflicts E0109, local variables first); only if it resolves to an object relation that a
program owns is the coercion inserted. So:

- A meta function named like an object relation keeps whatever meaning it has today: if the head
  resolves to the meta function, nothing is coerced.
- A local variable or a pattern variable named like a relation shadows it, as everywhere.
- A record of relations that is not a module, such as a functor parameter `g : graph`, owns nothing:
  `g.edge x y` is E0960, never a judgment of some guessed program.
- Object positions are not affected: in a rule, a query, a formula function or under an explicit quote
  `<…>`, an atom is object code as today. The coercion applies only where a *meta type* is expected.

### 2.10 What level 3.5 is not

It is not level 4. `tc2.path` is not a family: it has no constructors of its own, it is not injective for
unification (`?R x y =?= tc2 g ⊢ path x y` is a higher-order problem, solved only when `?R` is given), and
a derivation is a `derives` value. Meta functions that walk derivations (`route`, chapter 10.2 of the
proofs note) are written over `derives` as today. Per-relation adequacy does not arise: the coerced atom
is the judgment, and the one adequacy statement (reference `std/semantics.md`, "Adequacy") covers it.

## 3. Prior art, per mechanism

| mechanism of this design | prior art | what Hugin takes, what it does not |
|---|---|---|
| a coercion inserted where a *type* is expected | Lean 4's `CoeSort` (a term used as a type, `↥s` for `s : Set α`); Rocq's coercions to `Sortclass` | the trigger "expected a sort"; not a user-extensible class (Hugin has no type classes, P2b) |
| a coercion inserted by expected type at all | Hugin's stage inference (`⇑`, quote, splice, lifting; Kovács 2022) | the same elaborator position (`inferU`, checking against a universe) |
| eta form for unapplied relations | Hugin's stage inference eta-expands an object relation to a formula function | the same rule, with `Type` in place of `⇑prop` |
| the abbreviated judgment hides the program | Abella's `{A}` for `{nil ⊢ A}`, with the one specification fixed by `Specification "file".` | the program comes from the relation's owner instead of a file-wide setting |
| the relation *is* the proposition | Isabelle's `inductive` predicates, Lean 4's `inductive … : α → α → Prop`, Twelf's type families | the surface only: level 3.5 keeps one judgment, level 4 would make the relation a family |
| explicit context stays visible | Beluga's contextual types `[Ψ ⊢ M]` | `⊢[e]` stays the form for a database other than `d` |
| "which program" for a functor's relation | Isabelle locales (`locale … fixes`, `context … begin`, `interpretation fast: tc road`); Agda parameterised modules and `variable`; Lean `section`/`variable`; Rocq `Section`/`Context` | the functor parameter is the locale's `fixes`, generalisation its abstraction at the end of the block, `forFast` its `interpretation`; in-body proofs (the `context` block) are deferred with `here` |
| a user-level notation instead | Agda `syntax` declarations, Rocq `Notation`, Lean `notation`/`macro` | not usable: a user notation needs a fixed head symbol and cannot compute the owner of a relation |
| an implicit program found by search | Agda instance arguments `{{p : P}}`, Lean instance implicits `[…]`, Rocq `Hint`s and type classes | rejected (alternative C): several programs in one statement, no type classes in Hugin |

**Lean's `CoeSort`** is the closest mechanism. In Lean 4, `class CoeSort (α : Sort u) (β : outParam (Sort
v))` (`src/Init/Coe.lean`) is consulted when a term of a non-sort type is used as a type; Mathlib's `Set α`
coerces to the subtype `↥s` that way, while `s x` is a proposition. Hugin's fact types are the analogue of
`↥s`: `fast.path` used as a type is the type of the identities of its facts (unchanged, §2.2), and
`fast.path x y` is a proposition (new). The difference is that Hugin's coercion is built in, for one
judgment, so it needs no instance search and no class.

**Rocq's coercions to `Sortclass`** (`doc/sphinx/addendum/implicit-coercions.rst`, "Coercion classes") are
declared per source class with `Coercion f : C >-> Sortclass.`; the elaborator inserts `f` when a term of
class `C` stands where a sort is expected. The trigger is the same; Hugin's source "class" is "an applied
relation that a program owns", which is syntactic and needs no declaration.

**Abella** (`src/metaterm.ml`, `Obj`, abella/abella 957bb74) writes the specification judgment `{L |- A}`
and abbreviates it `{A}` when the context `L` is empty; the program is the specification loaded by
`Specification "add".` (`src/prover.ml`, `clauses`). There is one program per development, so the
abbreviation can drop it. Hugin has several programs per statement (`tc` and `tc2` in Proof A), so the
program must come from somewhere else: the relation's owner.

**Isabelle's locales** answer the "which program" question for parameterised specifications. A `locale tc
= fixes edge :: "'a ⇒ 'a ⇒ bool"` with an `inductive path` inside a `context tc begin … end` block states
lemmas about `path` unqualified, with `edge` fixed; after `end`, they are abstracted over `edge`, and
`interpretation fast: tc road` instantiates them as `fast.lemma`. Hugin's functor parameter plus
generalisation is the same abstraction, written per declaration instead of per block: `tc2.path x y` in a
declaration's type abstracts over `g`, and `forFast` is the interpretation. Isabelle's `inductive` package
also gives the relation's rules the names `path.intros(1)`, which P7b followed with `path.1`.

**Agda** offers two mechanisms that could implement parts of this by hand. A `syntax` declaration
(`doc/user-manual/language/syntax-declarations.lagda.rst`) gives a function a mixfix surface, `syntax
derives P d a = P ⊢[ d ] a`, but only for a fixed function symbol, and the atom `path x y` has no such
symbol: the program depends on where `path` is declared. Instance arguments
(`doc/user-manual/language/instance-arguments.lagda.rst`) could supply an implicit program `{{p :
Program}}`, which is alternative C below. Parameterised modules and `variable`
(`doc/user-manual/language/generalization-of-declared-variables.lagda.rst`) are the precedent for P7b's
generalisation, which level 3.5 reuses.

**Twelf and Beluga.** In Twelf a relation is an LF type family (`path : node -> node -> type.`), so
"relations as propositions" is the starting point, and meta-theorems are total relations over it (`%total`).
That is level 4, with the program as the signature. Beluga reasons about LF objects in explicit contexts,
`[Ψ ⊢ M]`, and does not abbreviate the context away; Hugin follows it in keeping `⊢[e]` for databases other
than `d`.

## 4. Alternatives

### 4.1 A: the judgment coercion (recommended)

As in §2: one elaboration rule at the place where stage inference inserts `⇑` today, triggered by an
applied relation that a program owns, where a meta type is expected.

### 4.2 B: derived meta members per relation

Chapter 10.1 of the proofs note sketched this: for each relation `r` of a body, the compiler derives a meta
member `(tc2 g).path : g.node -> g.node -> Type = [x] [y] tc2 g ⊢ path x y`, and rule pattern synonyms.

- The module field `path` is already the object relation (`fast : { path : ⇑(city -> city -> rel) }`, from
  `--print-after elaborate`). A second field of the same name needs names overloaded by stage, as shared
  data has them (reference `meta/families.md`, "Names and stages"), but for relations, which are not data:
  the "crack in 2LTT's separation" that chapter 10.2 of the proofs note lists as a cost of level 4.
- `(tc2 g).path` as a member of an application evaluates `tc2 g`, which creates an instance (generativity,
  D10). To avoid it, the member must be recognised syntactically, at which point it is alternative A with
  an extra generated declaration.
- A member per relation of every body costs compile time and incrementality (a rule edit changes a
  member's type), and the pattern synonyms duplicate P7b's rule names.
- Gain over A: none that A's eta form does not give (`symmetric undirected.reach`).

### 4.3 C: an ambient program

Abella's choice: one program per scope, so that bare atoms, including parameter relations, are its
judgments. In Hugin it could be a directive (`%program tc.` until the next one), a block (Isabelle's
`context`), or an instance argument (`{{p : program}}`).

- Proof A mentions two programs in one statement; every ambient design then needs the explicit form
  anyway, and the reader must know which directive is in effect to read `path x y`.
- It would cover `g.edge x y`, but with a meaning that depends on the ambient program's labels (`arg
  "edge"` or `arg "g.edge"`).
- It needs a new directive or block form, that is new syntax, against the designer's request for no hidden
  keywords; an instance argument needs type classes, which P2b decided against.
- Gain over A: parameter relations without the turnstile, and in-body proofs earlier (but those need the
  `here` phase in any design).

### 4.4 D: no change; abbreviations written by hand

Today a user can define an abbreviation and match on rule names through it (checked: compiles and runs):

```hugin
reach (g : graph) (d : db) (x : ⇑g.node) (y : ⇑g.node) : Type = tc g ⊢[d] path x y.
reachTrans : {g : graph} -> {d : db} -> {x y z : ⇑g.node} -> reach g d x y -> reach g d y z -> reach g d x z.
reachTrans (path.1 E) Q = path.2 E Q.
reachTrans (path.2 E P) Q = path.2 E (reachTrans P Q).
```

- `g` and `d` must be explicit at every use: as implicit arguments they are not determined by `x : ⇑g.node`
  (`g.node` is a projection, not injective), and generalisation does not apply to a definition's uses.
- One definition per relation and program, written and named by the user; hovers show the unfolded
  judgment anyway.
- Gain: nothing to implement. It stays available under A.

### 4.5 Comparison

| | A coercion | B derived members | C ambient program | D by hand |
|---|---|---|---|---|
| new syntax or keyword | none | none (generated names) | a directive or block | none |
| core change | none | none | none | none |
| new names in scope | none | one member per relation | none | user's |
| meaning of `path x y` | determined by the head's owner | determined by the head's owner | by the directive in effect | user-defined |
| parameter relations without `⊢` | no | no | yes | yes, by hand |
| functor applications | syntactic, no instance | needs A's syntactic rule | syntactic | explicit `g` |
| generalisation of `g`, `d` | as `⊢` | as `⊢` | as `⊢` | none |
| unapplied relation as a meta relation | yes (η) | yes (member) | yes | yes |
| compile-time cost | one lookup per candidate | a member per relation | one lookup | none |
| lines (§5) | 650–1050 with P9a | 1100–1600 | 900–1300 | 0 |

**Recommendation: A.** It adds no syntax and no names, it reuses the P7b elaboration path in full, it
takes a slot that today holds only meaningless types (§2.2), and it is honest about relations that belong to
no program. B is A plus generated declarations; C trades a small gain (parameter relations) for a scope
rule the reader must track; D remains possible but does not remove the indirection.

## 5. Costs

**Lines (estimate).** Scala, Hugin library, reference and tests together: P9a 150–250, P9b 500–800, so
level 3.5 itself is 650–1050 (the proofs note budgeted 500–900 for P9 in chapter 12). The open flags add
P9c 900–1400, P9d 150–300 and P9e 200–350 (§7). Most of P9b's Scala is the owner lookup and the
generalisation pre-pass; the judgment itself is P7b's `inferJudgment`.

**Risks.**

- *Name resolution.* The owner of an opened constant (after `%use fast.`) needs a map from object constants
  to the module instances that declared them; P7a records instances (`ModuleInstance`) for `programOf m`,
  so the map is that record inverted, built once per file. An anonymous instance (`%use (tc { … }).`) has
  an owner too, `_m1`, and prints as `programOf _m1 …` (P7b's printing of bodies reached through an
  instance).
- *Ambiguity between object relations and meta names.* None is introduced (§2.9). The one new reading is
  of the text `f.r` for a functor `f`, which is an error today in every position.
- *A meaning change for accepted programs* (§2.2), limited to types without closed inhabitants; P9a turns
  them into errors first, so a program that relied on them fails loudly before P9b gives them a meaning.
- *Performance.* The coercion is syntax-directed: one name lookup per applied path in a type position, and
  the elaboration of a judgment, which the turnstile form costs anyway. No evaluation, no new unification
  problem. The generalisation pre-pass walks a declaration's type trees once, as P7b's does.
- *Error messages.* A failing coercion must say that the atom was read as a proposition: arity and column
  errors reuse E0945's text with "the atom `fast.path x`, read as `fast ⊢ path x`". An applied relation
  that no program owns is E0960, naming the turnstile form (§1.5).

**What it makes confusing.**

1. `fast.path` (unapplied, at `Type`) is the fact type, while `fast.path x y` is a proposition: one name,
   two readings by application. Lean has the same split (`↥s` against `s x`); the hover shows which one.
2. `tc.path x y` looks like a member selection on `tc`, a function; it hides the generalisation of `g`, as
   `tc ⊢` does.
3. The program's own relations lose the turnstile while parameter and file relations keep it (Proof A's
   `edgeIn`). The rule is principled (only an owned relation has one program) but visible.
4. A nullary relation needs the turnstile (`fast ⊢ flag`), because `fast.flag` at `Type` is the fact type.
5. Printing shows `tc g ⊢ path x y` where the user wrote `tc.path x y`.

**What it makes impossible.** The type `⇑(fast.path x y)`, which has no closed inhabitants, can no longer
be written. Nothing else that compiles today changes meaning.

## 6. The open flags

### 6.1 The `decide` name clash (L22a)

`std/semantics` declares `decide : {d : db} -> {p : program} -> {a : gatom} -> (n : nat) -> so (holds n p a)
-> derives p d a`, and `std/decide` declares the generic `decide : {A : Type} -> {P : A -> Type} -> (d :
decider A P) -> (x : A) -> so (d.check x) -> P x`. A file that opens both gets E0109 at every use (checked:
"`decide` is ambiguous: two `%use` items open it for different declarations").

**Would P2b's type-directed overloading fix it.** Yes, without a new rule, if it is applied to names that two
`%use` items open. P2b chooses among candidates by the heads of their types only: the result after the
given explicit arguments against the expected type, then the first explicit domain against the first
argument's type; each argument is elaborated once, nothing is backtracked (proofs note §15, P2b). For the
two `decide`s:

- `decide 3 tt` against `trip.path berlin rome`: after two explicit arguments, the semantics' result is
  `derives p d a`, whose head `derives` matches; the generic one's result after two arguments is the Π type
  `so (d.check x) -> P x`, whose head does not. One candidate fits.
- `decide ltDec { fst = 3, snd = 100000 } tt` against `lt 3 100000`: the semantics' `decide` takes two
  explicit arguments and its result is not a function, so three do not fit; the generic one's result `P x`
  has an unknown head and fits.

**Recommendation (P9e).** Resolve E0109 conflicts by P2b's rule when every candidate is a meta constant;
declarations of the file still shadow opened names; no fitting candidate or several is E0932/E0933 (P2b's
codes, generalised to names). This is Lean 4's treatment of ambiguous identifiers after two `open`s (all
alternatives are elaborated, and those that fail are dropped; "ambiguous, possible interpretations"
otherwise; `src/Lean/Elab/App.lean`), restricted to P2b's head comparison, so that it stays linear.
Idris 2 overloads every name by type (`TTImp.Elab.Ambiguity`); Agda overloads only constructors,
projections and pattern synonyms. The alternative is a rename of the semantics' `decide` (for example to
`evaluate`), which changes chapter 1's `decide 3 tt` and fixes only this clash.

### 6.2 Multi-head rule names (L22b)

P7b names a rule by its first head only (`r.k` = `crule.head`/`crule.index`). A rule's other heads, its
written heads after the first and the constructor terms of its heads (P5a's "no `sub`"), have no name. The
gap is a coverage gap, not only a cosmetic one. Checked at 1db9441:

```hugin
both (g : graph) = {
  edge : g.node -> g.node -> rel.
  edge X Y, edge Y X :- g.edge X Y.
}.
flip : {x y : g.node} -> both ⊢ edge x y -> both ⊢ edge y x.
flip (edge.1 E) = ?.
```

```text
error[E0911]: the clauses of `flip` do not cover all cases
 --> n_multihead.hgn:7:1
  |
7 | flip : {x y : g.node} -> both ⊢ edge x y -> both ⊢ edge y x.
  | ^^^^ missing: `flip (fire _ _ (there _))`
```

The missing case, the second head, can only be written with raw `fire`, `econs` and `there`.

**Recommendation (P9d).** Number *(rule, head)* pairs: `q.k` is the `k`-th pair, in program order and head
order, whose head relation is `q`. As a pattern, its head proof is `there^j here` for the head's position
`j` (P7b always wrote `here`). For a rule whose only head is its first, nothing changes; `both` gets
`edge.1` (head `edge X Y`) and `edge.2` (head `edge Y X`), and a nested fact's constructor gets names for
the rules that build it. `crule.index` keeps P7a's meaning (the first-head numbering), since rule names are
computed by the elaborator and need not equal it; the reference states the naming rule separately. This is
proofs note §7.3's "a name for each" head, and the reading of the reference: "a rule with several heads is
the same as one rule per head" (`object/rules.md`). A label `@n` keeps naming the rule; against a goal
whose relation is a later head's, it names that head, and E0948 if two heads of the rule have the goal's
relation (then `q.k` must be used).

Isabelle's `inductive` numbers the introduction rules per predicate in a mutual definition
(`p.intros`, `q.intros`), which is the same choice for rules that define several predicates.

### 6.3 The notation and `nderives` for stratified programs (L20)

**Today's behaviour is unsound with respect to the run.** `P ⊢ r t̄` always elaborates to `derives`, the
positive fragment, in which a rule with a negation or an aggregate never fires (P6 kept `derives`
unchanged). For a program with negation, the notation therefore states facts about a different program.
Checked at 1db9441, the following file compiles and runs, although the run derives `m.ok berlin`:

```hugin
%use "std/semantics".
%use "std/eq" (tt, empty).
city : type. berlin, paris : city.
m = {
  node : city -> rel.
  bad : city -> rel.
  node berlin. node paris. bad paris.
  ok : city -> rel.
  ok X :- node X, not bad X.
}.
never : m ⊢ ok berlin -> empty.
never (fire {xs := econs X enil} (there (there (there here))) (ppos _ _ ()) here).
```

The meta logic stays consistent (`derives` is an honest family), but `never` contradicts the adequacy
statement's intent, which the reference restricts to the positive fragment in prose while the notation
accepts any program. Rule names on such a rule give confusing errors as well: `ok.1 node.1` is E0901 with
a full `premises … cnot …` type, and the pattern `ok.1 N` is E0915 "the case for `pcmp` is impossible",
because P7b treats every non-atom literal as a comparison.

**Recommendation, in two steps.**

1. *Stop-gap (P9a).* A judgment, written or coerced, whose program has a negation or an aggregate in a rule
   is E0961, "the judgment notation covers programs without negation and aggregates; use `nderives` of
   `std/strata`". No existing test uses the notation on such a program (checked by search).
2. *The stratified reading (P9c).* For a program with negations or aggregates, `P ⊢ r t̄` elaborates to
   the *stratum-local* judgment of `r`:

   ```text
   P ⊢ r t̄  ⇝  nderives (layer p sₖ) (upTo p k d) (atom ρ vs)
   where p = programOf P, k = the last stratum with a rule that has a head of r,
         upTo p k d = layers p (take k p.strata) (inputs p d)
   ```

   `std/strata` gains `upTo` and the adequacy lemma `perfect p d a ↔ judged p d a` for that `k` (the facts of
   `r` are added only by layers up to `k`, and kept afterwards; P6's `kept` is one direction). Positive
   programs keep `derives`, so P7b's proofs and P9b's coercion do not change.

   Rule names over `nderives`: the pattern of `r.j` is `nfire` with the member proof in `filter (headIn sₖ)
   p.rules` (closed data, it evaluates), `npos refl P` for an atom of the same stratum, `ncmp _` for a
   comparison, and for an atom of a lower stratum the chain `ngiven _ (… (ngiven _ P))` down to that
   relation's own stratum, so that `P` again has the stratum-local type `P ⊢ q t̄`. A negated atom and an
   aggregate are written premises (a negation carries information, unlike a comparison): the pattern
   variable of `not q t̄` has the type `absent …`, and a library lemma converts it to `P ⊢ q t̄ -> empty`.
   `given` is `ngiven`. `decide` stays unavailable for these programs until P8b's certified completeness
   (`closed`) extends `holds` to strata (P6's decision).

   This is the iterated fixpoint of Apt, Blair and Walker, read stratum by stratum, as DatalogCert
   (Benzaken, Contejean and Dumbrava, ITP 2017) evaluates a stratum with negations read in the strata
   below, and as Schlichtkrull, Hansen and Nielson's *Stratified Datalog* (AFP 2025) indexes the semantics
   by strata. How a negated premise is best presented in patterns is the one sub-question that P9c settles
   in a short addendum before it is implemented.

### 6.4 Other flags that level 3.5 touches

- *L17, `programOf f : graph -> program`* for a bare functor. Level 3.5 never uses the bare form: `tc.path`
  generalises to `programOf (tc g)`, as `tc ⊢` does. Recommendation: accept L17 as implemented. P7a's D12
  realisation (the converse round trip proved on the image of `quote` instead of trusted) is not touched.
- *L22c, `{X := W}`.* Pattern variables are uppercase, so chapter 1 of the proofs note should write
  `{X := W}`, as the test does. Recommendation: correct chapter 1 (text only) with P9a's documentation.

## 7. Batches

Each batch is one PR, after approval; each needs only the batches before it in its column. Error codes:
E0960–E0961, provisional (the block after P8b's E0955+).

| batch | content | lines | tests | enables |
|---|---|---|---|---|
| **P9a** honest types | an applied relation under `⇑` in a meta type is E0960 (also written `⇑(r t̄)`); a judgment over a program with negation or aggregates is E0961; reference: `meta/staging.md` (stage inference), `std/semantics.md` (scope of the notation); E0960, E0961 explanations; chapter 1's `{X := W}` | 150–250 | neg: `e0960_applied_relation` (instance, functor application, parameter relation, explicit `⇑`, η), `e0961_judgment_negation` (`not`, `count`); the corpus run shows that no test relied on `⇑(r t̄)` | correctness on its own; the slot for P9b |
| **P9b** the judgment coercion | the coercion and its η form (§2.1), the owner lookup (§2.3), the generalisation pre-pass (§2.5), E0960 for unowned relations, E0945 texts for coerced atoms; reference: `std/semantics.md` "Relations as propositions", `meta/functions.md` (generalisation) | 500–800 | run: `p9b_proof_a`, `p9b_proof_b` (§1.1, §1.2 as written), `p9b_relations` (§1.3, §1.4, `weak.v.vertex`, `(f ā).r`); neg: parameter relation, file relation, nullary relation, `d` missing outside a type position; LSP: hover on `tc.path x y` shows `tc g ⊢ path x y`, a split below it | statements without the turnstile; relations passed to meta combinators |
| **P9c** stratified judgments | §6.3 step 2: the stratum-local reading, `upTo` and the adequacy lemma in `std/strata`, rule names over `nfire`/`npos`/`ncmp`/`nneg`/`nagg`, `ngiven` chains; E0961 lifted; the reference's adequacy statement extended to stratified programs | 900–1400 | run: `p9c_negation` (`ok.1` proves `m ⊢ ok berlin`; `never` no longer provable), `p9c_aggregate`; neg: rule name with a missing negated premise | proofs about programs with negation in the notation |
| **P9d** multi-head names | §6.2: names per (rule, head) pair, head proof `there^j here`, splits offer them, labels against later heads | 150–300 | run: `p9d_heads` (`flip` with `edge.1`, `edge.2`; a constructor term in a head); neg: label naming two heads of the goal's relation | coverage of multi-head rules with rule names |
| **P9e** overloaded opened names | §6.1: E0109 among meta constants resolved by P2b's head rule; hover and go to definition show the chosen constant; E0932/E0933 for names | 200–350 | run: `p9e_overload` (both `decide`s in one file); neg: no expected type (E0932) | chapter 1's `decide 3 tt` with `std/decide` open |

Order: P9a → P9b. P9d and P9e are independent of P9b and of each other. P9c needs P9a (it replaces E0961)
and is independent of P9b, since the coercion inherits whatever the turnstile elaborates to. Following the
house rule (L10), each batch's agent runs only the tests it adds or changes; CI runs the suite.

## 8. Decisions for the designer

1. **Where the design lives.** A separate note, `docs/design/proofs-level35.md`, linked from chapter 10 of
   the proofs note. *Recommended.*
2. **The mechanism.** Alternative A, the judgment coercion: an applied relation that a program owns,
   where a meta type is expected, is that program's judgment at `d`; no keyword, token, directive, core rule
   or generated declaration. Rejected: B (derived members), C (ambient program), D (by hand only).
   *Recommended: A.*
3. **The forms covered.** Instance paths `m.r t̄`, module values, member instances `m.v.r t̄`, names opened
   from an instance by `%use`, functor applications `(f ā).r t̄`, and functors written alone `f.r t̄`
   (generalised as `f ⊢`). *Recommended.*
4. **The η form.** An unapplied owned relation where `⇑τ₁ -> … -> ⇑τₙ -> Type` is expected is `[x̄] P ⊢ r
   x̄` (§1.3). *Recommended.*
5. **Not covered, kept in the turnstile form:** parameter relations, file relations (until `here`),
   relations of the enclosing body (until `here`), relations computed by meta functions, nullary relations,
   databases other than `d`. E0960 names the turnstile form. *Recommended.*
6. **Today's `⇑(r t̄)`** (an applied fact type under the lift, accepted with no closed inhabitants) becomes
   an error in P9a, before P9b gives the slot its meaning. *Recommended.*
7. **Generalisation** of coerced atoms is collected syntactically, in syntactic type positions (§2.5), not
   by re-elaborating the header as Lean does. *Recommended.*
8. **Printing.** Hovers and diagnostics keep the canonical `P ⊢ r t̄`, also for atoms written without the
   turnstile. *Recommended.*
9. **Rule names** are unchanged; the per-relation synonyms of chapter 10.1 (`(tc2 g).path.base`) are dropped,
   since labels already name rules. *Recommended.*
10. **When `programOf here` lands**, the coercion covers file relations (`here ⊢ r t̄`) and relations of the
    enclosing body (locale-style proofs inside a functor) with no new rule. *Recommended* (no batch now).
11. **Negation, stop-gap.** A judgment over a program with negations or aggregates is E0961 (P9a), since
    today it is read in `derives` and can contradict the run (§6.3). *Recommended.*
12. **Negation, the reading.** For such programs, `P ⊢ r t̄` is the stratum-local `nderives` judgment, with
    rule names over `nfire` and `ngiven` chains and written negated premises (P9c, after a short addendum
    on the presentation of negated premises). *Recommended.*
13. **Multi-head rules.** Rule names number (rule, head) pairs per head relation; head proofs `there^j
    here`; `crule.index` unchanged (P9d). *Recommended.*
14. **The `decide` clash.** Resolve E0109 among meta constants opened by two `%use` items with P2b's
    head rule (P9e). Alternative: rename the semantics' `decide`. *Recommended: P9e.*
15. **L17**, `programOf f : graph -> program`: accept as implemented; level 3.5 does not need a closed
    program of a bare functor. *Recommended.*
16. **L22c**: chapter 1 of the proofs note writes `{X := W}` (text correction in P9a). *Recommended.*
17. **Batches and order:** P9a → P9b; P9c after P9a; P9d, P9e independent; codes E0960–E0961.
    *Recommended.*

## 9. Sources

The sources of the proofs note (chapter 14) apply; in addition:

- leanprover/lean4 0bb12a8: `src/Init/Coe.lean` (`CoeSort`), `src/Lean/Elab/App.lean` (overloaded
  identifiers, "ambiguous, possible interpretations"), `src/Lean/Elab/Term.lean` (`withAutoBoundImplicit`).
  Mathlib's `Set` coercion to a type (`↥s`).
- rocq-prover/rocq 29f5238: `doc/sphinx/addendum/implicit-coercions.rst` (coercions to `Sortclass`),
  `doc/sphinx/user-extensions/syntax-extensions.rst` (`Notation`), the reference manual's `Hint` commands.
- agda/agda a3f41e8: `doc/user-manual/language/{syntax-declarations,instance-arguments,generalization-of-declared-variables,module-system,pattern-synonyms}.lagda.rst`.
- abella/abella 957bb74: `src/metaterm.ml` (`Obj`, the judgment `{L |- A}` and its abbreviation `{A}`),
  `src/prover.ml` (`clauses`, `Specification`).
- Isabelle: C. Ballarin, *Tutorial to Locales and Locale Interpretation* (Isabelle documentation
  `locales`); *The Isabelle/Isar Reference Manual*, sections on `inductive` and on locales (`locale`,
  `context`, `interpretation`).
- Idris 2: `src/TTImp/Elab/Ambiguity.idr` (idris-lang/Idris2 1c630e6).
- F. Pfenning, C. Schürmann: System description: Twelf, CADE 1999. B. Pientka, J. Dunfield: Beluga, IJCAR
  2010.
- K. R. Apt, H. A. Blair, A. Walker: Towards a theory of declarative knowledge, 1988. V. Benzaken,
  É. Contejean, S. Dumbrava: ITP 2017 (DatalogCert). A. Schlichtkrull, R. R. Hansen, F. Nielson: Stratified
  Datalog, Archive of Formal Proofs, 2025.
- Hugin 1db9441: `core/elab/{Judgments,Universes,Bidirectional,Declarations}.scala` (`inferJudgment`,
  `generalisedBinders`, `inferU`, `check`), `stdlib/std/{semantics,strata,decide}.hgn`,
  `tests/run/p7b_{proof_a,proof_b,rules}.hgn`, `reference/src/{modules,meta/staging,meta/families,object/types,object/rules,std/semantics}.md`.
  The paths of the Lean, Rocq, Agda and Isabelle documents are given from the projects' layout at the
  commits that chapter 14 of the proofs note cites; this note did not re-read them.
