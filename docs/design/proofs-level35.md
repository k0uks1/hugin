# Level 3.5: relations as propositions (P9)

Design note for batch P9 of [issue #186](https://github.com/k0uks1/hugin/issues/186), the follow-up that
decision D14 of the [proofs note](proofs.md) left "design first": a relation of a program used directly
as a meta-level proposition, by derived abbreviations, with no change to the core. Status: **approved by
the designer (revision 4)**; P9a is merged (05b8b45), the other batches follow §7. Written against
`ccr-48027e29-daam41` at 1db9441, after P1–P7b and P6 merged; revision 4 also reflects P9a, P8b, L27 and
L28.

Revision 2 (designer review of #207): the ambient-program alternative C was a sketch of ten lines. It is now
treated at the depth of A (§4.3): three variants with their end states, precise prior art, the elaboration
phase that blocks the locale-style variant C3, and what C3 gains and loses. The recommendation changed:
A and C3 are complementary, not alternatives (§4.3.5), and the plan is now A first, then the phase, then C3
(§4.6, §7, §8). The end state of the combination is §1.6.

Revision 3 (designer decision L27, approved: no blessed names in judgments; implemented by P7c before
P9b): a functor is no longer generalised by its parameters' names, so every example writes `tc G` with `G`
a free variable; an omitted database is P7c's anonymous binder in a declaration's type and a metavariable
elsewhere, and `d` means nothing special. A's form `f.r` for a functor written alone is dropped (§2.3), so
is the functor-parameter part of its generalisation (§2.5), and §2.4 is restated. With `tc.path` gone, A
no longer shortens Proofs A and B (§1.1); its gains are the η form and instance names, and C3 carries the
gain for proofs about one program. Costs, comparison, batches and decisions are recomputed.

Revision 4 (approval of #207): §8 is the approved list. C3's scope includes the file itself, so a relation
of the file is written unqualified at the top level (`trip x y`, not `here ⊢ trip x y`; §1.7). Parameter
relations in judgments are written through the user's argument (`tc G ⊢ G.edge x y`), as P7c resolves
them (L28). The batch plan follows the approved order.

The note is a file of its own, linked from the proofs note's chapter 10, for three reasons. It is a
separate design round with its own approval, as chapter 10 recorded. The proofs note has about 2300 lines, and its
chapters 1–9 describe a plan that is now implemented, so a new end state belongs in a new chapter 1. And
§15 of the proofs note records the implementation decisions of each batch as it lands.

**What was compiled.** The probes in §2.2, §4.3, §6.2 and §6.3 and the P7b versions of the "before"
programs in §1 were checked with the compiler at 1db9441 (`hugin check`/`run`). The "before" programs are
shown in P7c's notation, which is not merged yet, and the level 3.5 programs do not exist yet; neither was
compiled. Probes with surprising results are listed in §2.2 and quoted in full in §6.2 and §6.3.

**Keywords.** Level 3.5 adds **no keyword, no token and no directive**. The words that matter in the
examples are: the token `⊢` (ASCII `|-`, P7b); the contextual names `given` and `programOf` (P7a, P7b),
which are names, not keywords, unless the program declares them; the keywords `match`, `rewrite` and
`with` (P3); the directives `%use`, `%opaque` and `%input`. Everything else in the examples is an ordinary
name: `path`, `tc`, `derives`, `decide`, `iff`.

Contents: 1 the end state (1.1–1.5 the coercion A, 1.6 A with locale-style proofs C3), 2 what level 3.5
is, 3 prior art, 4 alternatives (4.3 the ambient program, in full), 5 costs, 6 the open flags (`decide`,
multi-head rules, negation), 7 batches, 8 decisions (approved), 9 sources.

## 1. The end state

**The rule in one sentence.** *An atom whose relation belongs to a program, written where a meta type is
expected, is that program's judgment, at the database that the turnstile would use if it were written
without `[…]`.* For example, `fast.path x y` is `fast ⊢ path x y` and `(tc2 G).path x y` is `tc2 G ⊢ path
x y`. `G` is an ordinary free uppercase variable, bound by the existing implicit-argument mechanism, and
the database is P7c's: in a declaration's type, the one anonymous binder that all judgments without `[…]`
share; elsewhere, a metavariable solved by unification (§2.4). The rule is a coercion that elaboration
inserts by the expected type, as stage inference inserts `⇑`, quotes and splices today. It generates no
declaration, no family and no lemma, and it gives no name a special meaning.

So `path x y` alone does **not** mean `tc G ⊢ path x y`: `tc` and `tc2` both have a relation `path`, and
the name alone does not say which program is meant. A bare name is a proposition only if it names a
relation of one module instance, for example after `%use trip (path).` (§2.3), or, with C3, a relation of
the body or the file that the statement is written in (§1.6, §1.7).

**The baseline is P7c.** After L27, the turnstile has no blessed names: `tc G ⊢ path x y` with `G` free,
`⊢[D]` to name a database. P7c implements that before P9b. The "before" programs below are written in
P7c's notation; their P7b versions (`tc ⊢ path x y`, with `g` and `d` generalised by name) compile at
1db9441 (`tests/run/p7b_*.hgn`), and the P7c versions follow by the rewriting L27 prescribes. A
parameter relation in an atom is written through the user's argument: `tc G ⊢ G.edge x y`, since P7c
resolves it there (L28); the body's own path `g.edge` is an unbound name outside the body.

### 1.1 Proof A: the doubling closure derives the same paths

Before (the turnstile, P7c):

```hugin
edgeIn : {x y : G.node} -> tc G ⊢ G.edge x y -> tc2 G ⊢ G.edge x y.
edgeIn (given I) = given I.
edgeOut : {x y : G.node} -> tc2 G ⊢ G.edge x y -> tc G ⊢ G.edge x y.
edgeOut (given I) = given I.

tcTrans : {x y z : G.node} -> tc G ⊢ path x y -> tc G ⊢ path y z -> tc G ⊢ path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

toTc2 : {x y : G.node} -> tc G ⊢ path x y -> tc2 G ⊢ path x y.
toTc2 (path.1 E) = path.1 (edgeIn E).
toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).

toTc : {x y : G.node} -> tc2 G ⊢ path x y -> tc G ⊢ path x y.
toTc (path.1 E) = path.1 (edgeOut E).
toTc (path.2 P Q) = tcTrans (toTc P) (toTc Q).

sameFacts : {x y : G.node} -> iff (tc G ⊢ path x y) (tc2 G ⊢ path x y) = { to = toTc2, from = toTc }.
forFast : {x y : city} -> iff (tc { node = city, edge = road } ⊢ path x y) (fast ⊢ path x y) = sameFacts.
%opaque sameFacts forFast.
```

With level 3.5, A alone (proposal):

```hugin
edgeIn : {x y : G.node} -> tc G ⊢ G.edge x y -> tc2 G ⊢ G.edge x y.   (* unchanged: G.edge is a parameter *)
edgeIn (given I) = given I.
edgeOut : {x y : G.node} -> tc2 G ⊢ G.edge x y -> tc G ⊢ G.edge x y.
edgeOut (given I) = given I.

tcTrans : {x y z : G.node} -> (tc G).path x y -> (tc G).path y z -> (tc G).path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

toTc2 : {x y : G.node} -> (tc G).path x y -> (tc2 G).path x y.
(* clauses unchanged *)
toTc : {x y : G.node} -> (tc2 G).path x y -> (tc G).path x y.
(* clauses unchanged *)

sameFacts : {x y : G.node} -> iff ((tc G).path x y) ((tc2 G).path x y) = { to = toTc2, from = toTc }.
forFast : {x y : city} -> iff ((tc { node = city, edge = road }).path x y) (fast.path x y) = sameFacts.
%opaque sameFacts forFast.
```

What changed: nothing of substance. `(tc G).path x y` reads "the relation `path` of `tc G`", but it is as
long as `tc G ⊢ path x y`; the clauses, the rule names, the binders (`{G : graph}`, the anonymous database)
and the elaborated types are the same. Before L27, A's proposed form `tc.path x y` was shorter than `tc ⊢
path x y` because both generalised `g` by name; L27 removes that generalisation, revision 3 drops the form
(§2.3), and with it A's gain on Proof A. The gains of
A that remain are in §1.3 (relations passed to meta combinators) and §1.4 (instances and opened names);
the gain on Proofs A and B comes from C3 (§1.6).

### 1.2 Proof B: the analysis over-approximates

Before (the turnstile, P7c). The hypothesis `placed` is a definition, so its databases are named; the
theorems must then name the same database, `⊢[D]` with `D` free, since the anonymous binder cannot be
referenced:

```hugin
placed (d : db) (a : abstraction) : Type =
  (x : a.node) -> coarse a ⊢[d] reached x -> { b : a.anode, ok : coarse a ⊢[d] a.alpha x b }.

sound : placed D A -> {x : A.node} -> {b : A.anode} ->
        coarse A ⊢[D] reached x -> coarse A ⊢[D] A.alpha x b -> coarse A ⊢[D] areached b.
sound T (reached.1 S) H = areached.1 S H.
sound T (reached.2 {X := W} R E) H = areached.2 (sound T R (T W R).ok) (aedge.1 E (T W R).ok H).

safe : placed D A -> {x : A.node} -> {b : A.anode} ->
       (coarse A ⊢[D] areached b -> empty) -> coarse A ⊢[D] A.alpha x b -> coarse A ⊢[D] reached x -> empty.
safe T N H R = N (sound T R H).
%opaque sound safe.
```

A coerced atom has no `[…]`, so with a named database it does not apply: this version stays as it is. With
level 3.5 the hypothesis can instead be stated over *relations*, passed by the η form, so that no database
is named and all of them are the declaration's anonymous binder (proposal):

```hugin
placed : (A : abstraction) -> (⇑A.node -> Type) -> (⇑A.node -> ⇑A.anode -> Type) -> Type.
placed A Reached Alpha = (x : ⇑A.node) -> Reached x -> { b : ⇑A.anode, ok : Alpha x b }.

sound : placed A (coarse A).reached ([x] [b] coarse A ⊢ A.alpha x b) -> {x : A.node} -> {b : A.anode} ->
        (coarse A).reached x -> coarse A ⊢ A.alpha x b -> (coarse A).areached b.
sound T (reached.1 S) H = areached.1 S H.
sound T (reached.2 {X := W} R E) H = areached.2 (sound T R (T W R).ok) (aedge.1 E (T W R).ok H).

safe : placed A (coarse A).reached ([x] [b] coarse A ⊢ A.alpha x b) -> {x : A.node} -> {b : A.anode} ->
       ((coarse A).areached b -> empty) -> coarse A ⊢ A.alpha x b -> (coarse A).reached x -> empty.
safe T N H R = N (sound T R H).
%opaque sound safe.
```

`placed` no longer mentions `derives` or a database: it is a property of two meta relations. In `sound`'s
type, the η-coerced `(coarse A).reached`, the judgment in the lambda and the three atoms have no `[…]`, so
they all use the one anonymous database binder of the declaration. The input relation `A.alpha` keeps the
turnstile (§2.3). This version is not shorter; its point is that the database disappears from the
statement. In C3 (§1.6) it becomes `placed reached a.alpha`.

### 1.3 A relation passed to a generic combinator: an undirected graph is symmetric

This is A's clearest gain: a relation can be passed, unapplied, where a meta relation `A -> A -> Type` is
expected, as stage inference already passes an object relation where a formula function is expected
(reference `meta/staging.md`, "Stage inference": "Functions are converted by eta-expansion").

Before (the turnstile, P7c; the P7b version compiles and runs at 1db9441):

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

linkSym : {x y : G.node} -> undirected G ⊢ link x y -> undirected G ⊢ link y x.
linkSym (link.1 E) = link.2 E.
linkSym (link.2 E) = link.1 E.

reachTrans : {x y z : G.node} -> undirected G ⊢ reach x y -> undirected G ⊢ reach y z ->
             undirected G ⊢ reach x z.
reachTrans (reach.1 L) Q = reach.2 L Q.
reachTrans (reach.2 L P) Q = reach.2 L (reachTrans P Q).

reachSym : symmetric ([x] [y] undirected G ⊢ reach x y).
reachSym X Y (reach.1 L) = reach.1 (linkSym L).
reachSym X Y (reach.2 {Y := W} L R) = reachTrans (reachSym W Y R) (reach.1 (linkSym L)).
%opaque linkSym reachTrans reachSym.
```

With level 3.5 (proposal), only the statements change:

```hugin
linkSym : symmetric (undirected G).link.
linkSym X Y (link.1 E) = link.2 E.
linkSym X Y (link.2 E) = link.1 E.

reachTrans : {x y z : G.node} -> (undirected G).reach x y -> (undirected G).reach y z ->
             (undirected G).reach x z.
reachTrans (reach.1 L) Q = reach.2 L Q.
reachTrans (reach.2 L P) Q = reach.2 L (reachTrans P Q).

reachSym : symmetric (undirected G).reach.
reachSym X Y (reach.1 L) = reach.1 (linkSym _ _ L).
reachSym X Y (reach.2 {Y := W} L R) = reachTrans (reachSym W Y R) (reach.1 (linkSym _ _ L)).
%opaque linkSym reachTrans reachSym.
```

`symmetric (undirected G).reach` elaborates to `symmetric {⇑G.node} ([x] [y] undirected G ⊢ reach x y)`
under the implicit binders `{G : graph}` (a free variable) and the anonymous database, the type of the
turnstile version. The combinator is an ordinary meta function: a library of relation properties
(`symmetric`, `transitive`, `included`, `sameRel`) applies to object relations without a lambda per use.
`linkSym` now takes the two nodes explicitly, because `symmetric` quantifies them explicitly.

### 1.4 An instance opened by `%use`, proved by evaluation

Before (P7b and P7c alike, `tests/run/p7b_rules.hgn`): `viaParis : trip ⊢ path berlin rome = decide 3 tt.`
With level 3.5, both of the following are the same declaration (proposal):

```hugin
viaParis : trip.path berlin rome = decide 3 tt.

%use trip (path).
viaParis : path berlin rome = decide 3 tt.
```

After `%use trip (path).`, the name `path` denotes the relation constant of the instance `trip`, and the
coercion finds its program from the instance the constant belongs to. Today the second form is E0905
("`path` cannot be applied: its type `⇑(city -> city -> rel)` is not a function type", checked).

### 1.5 What the editor shows

Hovers and goals print the elaborated judgment, as for the turnstile: the hole in

```hugin
toTc : {x y : G.node} -> (tc2 G).path x y -> (tc G).path x y.
toTc (path.2 P Q) = ?.
```

shows `goal: tc G ⊢ path x y` and `P : tc2 G ⊢ path x Y` (P7b prints `tc g ⊢ path y x` for the turnstile
form, checked; P7c prints the program with the user's variable). Case splits offer `path.1 E` and `path.2 P
Q` as for the turnstile. A relation that belongs to no program is an error with a help that names the fix
(proposal: code and text):

```text
error[E0960]: `G.edge x y` is not a type: no program declares the relation `G.edge`
 --> closure.hgn:3:28
  |
3 | edgeIn : {x y : G.node} -> G.edge x y -> tc2 G ⊢ G.edge x y.
  |                            ^^^^^^^^^^ a relation of the variable `G`
  |
  = note: an applied relation is a proposition of the program that declares it
  = help: name the program: `tc G ⊢ G.edge x y`
```

### 1.6 With locale-style proofs (C3, after the phase of §4.3.6)

The approved plan adds proofs written inside the program's own body (§4.3.4), and in the file itself (§1.7). There a relation of the
body *and a relation of its parameter* is a proposition of that body's program, unqualified, and every
instance inherits the lemmas, as Isabelle's `interpretation` instantiates a locale's theorems. The body's
parameter `g` is in scope by its own binder, `tc2 (g : graph)`: a declared name, not a blessed one, so C3
is consistent with L27. Proof A then reads (proposal):

```hugin
%use "std/graph".
%use "std/eq" (iff).
%use "std/semantics".

(* tc belongs to std/graph: its body cannot take lemmas, so its lemma is stated outside *)
tcTrans : {x y z : G.node} -> (tc G).path x y -> (tc G).path y z -> (tc G).path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

tc2 (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- path X Y, path Y Z.

  (* inside the body, `path` and `g.edge` are tc2's own propositions; tc's are qualified *)
  edgeIn : {x y : g.node} -> tc g ⊢ g.edge x y -> g.edge x y.
  edgeIn (given I) = given I.
  edgeOut : {x y : g.node} -> g.edge x y -> tc g ⊢ g.edge x y.
  edgeOut (given I) = given I.
  toTc2 : {x y : g.node} -> (tc g).path x y -> path x y.
  toTc2 (path.1 E) = path.1 (edgeIn E).
  toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).
  toTc : {x y : g.node} -> path x y -> (tc g).path x y.
  toTc (path.1 E) = path.1 (edgeOut E).
  toTc (path.2 P Q) = tcTrans (toTc P) (toTc Q).
  sameFacts : {x y : g.node} -> iff ((tc g).path x y) (path x y) = { to = toTc2, from = toTc }.
  %opaque sameFacts.
}.

city : type. berlin, paris, rome : city.
road : city -> city -> rel.
%input road.
fast = tc2 { node = city, edge = road }.
%output fast.path.
(* no forFast: fast.sameFacts : {x y : city} -> iff ((tc { node = city, edge = road }).path x y) (fast.path x y),
   under the anonymous database binder *)
```

Proof B moves into `coarse`'s body, since it is about one program. The parameter relation `a.alpha` is
coerced there too, also in the η form, so the hypothesis takes the two relations by name:

```hugin
coarse (a : abstraction) = {
  (* … the rules of reached, aedge and areached as in §1.2 … *)
  placed : (⇑a.node -> Type) -> (⇑a.node -> ⇑a.anode -> Type) -> Type.
  placed Reached Alpha = (x : ⇑a.node) -> Reached x -> { b : ⇑a.anode, ok : Alpha x b }.
  sound : placed reached a.alpha -> {x : a.node} -> {b : a.anode} -> reached x -> a.alpha x b -> areached b.
  sound T (reached.1 S) H = areached.1 S H.
  sound T (reached.2 {X := W} R E) H = areached.2 (sound T R (T W R).ok) (aedge.1 E (T W R).ok H).
  safe : placed reached a.alpha -> {x : a.node} -> {b : a.anode} ->
         (areached b -> empty) -> a.alpha x b -> reached x -> empty.
  safe T N H R = N (sound T R H).
  %opaque sound safe.
}.
eu = coarse { node = city, edge = road, seed = start, anode = country, alpha = located }.
(* eu.sound and eu.safe are the theorems for the run's instance *)
```

The variant that keeps P7c's named database inside the body writes C2's prefix turnstile (§4.3.3):
`placed (D : db) : Type = (x : a.node) -> ⊢[D] reached x -> { b : a.anode, ok : ⊢[D] a.alpha x b }` and
`⊢[D]` in `sound` and `safe`. Both read better than any top-level version: the statements about one program
lose the program, the parameter relation loses its turnstile, and `forFast` disappears. The statement that
compares `tc` with `tc2` still qualifies `tc`, with A's `(tc g).path` or the turnstile.

### 1.7 The file itself (C3 at the top level, after P9f)

The file is the outermost body, and C3 applies to it as to a module body: after P9f, a relation that the
file declares is a proposition of the file's program wherever a meta type is expected at the top level,
written **unqualified** (proposal):

```hugin
%use "std/semantics".
%use "std/eq" (tt).
city : type. berlin, paris, rome : city.
hop : city -> city -> rel.
hop berlin paris. hop paris rome.
trip : city -> city -> rel.
trip X Y :- hop X Y.
trip X Z :- hop X Y, trip Y Z.

viaParis : trip berlin rome = decide 3 tt.
tripTrans : {x y z : city} -> trip x y -> trip y z -> trip x z.
tripTrans (trip.1 H) Q = trip.2 H Q.
tripTrans (trip.2 H P) Q = trip.2 H (tripTrans P Q).
%opaque viaParis tripTrans.
```

The user writes `trip x y`, never `here ⊢ trip x y`. `here ⊢ trip x y` is only the elaborated meaning,
`derives (programOf here) δ (atom (own i) …)`, which hovers and goals print, as they print `tc G ⊢ path x
y` for `(tc G).path x y`; the turnstile form stays valid, as for any program. Today the same file needs a
module around the rules (`trip = { … }` and `trip ⊢ path berlin rome`, `tests/run/p7b_rules.hgn`), because
`programOf here` was deferred by P7a; P9f delivers it. The file's lemmas are members of the file's module,
so a file that imports it reaches them with its relations.

## 2. What level 3.5 is

### 2.1 The rule

Level 3.5 is one elaboration rule, the **judgment coercion**, plus its eta form. Written as rules of the
bidirectional elaborator (`⇐` checks against a type, `⇝` is the elaborated term):

```text
  r is a relation, struct or constructor owned by the program P   (§2.3)
  r has the columns τ₁ … τₙ, n ≥ 1        Γ ⊢ tᵢ ⇐ ⇑τᵢ  ⇝  uᵢ        δ the omitted database (§2.4)
  ------------------------------------------------------------------------------------- (coerce)
  Γ ⊢ r t₁ … tₙ ⇐ Type ℓ   ⇝   derives (programOf P) δ (atom ρ [v u₁, …, v uₙ])

  the same premises, with the arguments missing
  ------------------------------------------------------------------------------------- (coerce-η)
  Γ ⊢ r ⇐ (x₁ : ⇑τ₁) -> … -> (xₙ : ⇑τₙ) -> Type ℓ   ⇝   [x₁] … [xₙ] P ⊢ r x₁ … xₙ
```

`ρ` is the reference that P7b's atom resolution gives `r` in `P` (`own i` for the program's own
relations). The right-hand sides are exactly the terms that `P ⊢ r t̄` elaborates to: the implementation
builds the `Judgment` tree and calls P7b's `inferJudgment`, so column typing, `⇑` covariance, arity
errors and the omitted database behave as for the turnstile written without `[…]`. "Where a meta type is expected" means both
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

A declaration such as `t : {x y : city} -> fast.path x y -> fast.path x y. t P = P.` is accepted today and
proves nothing. Level 3.5 therefore changes the meaning of accepted programs, but only of programs whose
types have no closed inhabitants. This was made a step of its own: P9a (merged, 05b8b45) turned the
applied fact type under `⇑` into E0960, and P9b gives the slot its meaning. The unapplied fact type
keeps its meaning: `w : fast.path = <fast.path berlin paris>.` is a fact identity, as today (checked:
elaborated as `w : ⇑$(fast.path) = ⟨$(fast.path) berlin paris⟩`).

### 2.3 Which program

The program is the one that *declares* the relation, found from the head of the atom without evaluating
anything (so no functor application creates an instance; D10, P7b's "program kind from the head's declared
type"):

| written | the relation belongs to | elaborates to |
|---|---|---|
| `fast.path x y`, `fast` an instance (`fast = tc2 { … }`) | the instance `fast` | `fast ⊢ path x y` |
| `trip.path berlin rome`, `trip` a module value (`trip = { … }`) | the module `trip` | `trip ⊢ path berlin rome` |
| `weak.v.vertex x`, a member instance (reference `modules.md`, "Instances") | the instance `weak.v` | `weak.v ⊢ vertex x` |
| `path x y` after `%use fast.` or `%use trip (path).` | the instance whose constant `path` denotes | `fast ⊢ path x y` |
| `(tc2 G).path x y`, any functor application (`G` a free variable, a parameter, or any argument) | the application | `tc2 G ⊢ path x y` |
| `fast.path` where `⇑city -> ⇑city -> Type` is expected | the instance `fast` | `[x] [y] fast ⊢ path x y` |
| with C3: `path x y` or `g.edge x y` inside the body of `tc2 (g : graph)` | the enclosing body at its parameter | `tc2 g ⊢ path x y` |
| with C3, after P9f: `trip x y` at the top level of the file that declares `trip` | the file | written `trip x y`; elaborated meaning `here ⊢ trip x y` |

Each row uses the omitted database of §2.4. A functor written alone, `tc2.path x y`, is **not** a form: it
would bind the functor's parameter under its declared name, which L27 rules out for the turnstile
(`tc2 ⊢ …` is no longer generalised), and it stays the error it is today (E0107, "`tc2` is not a module",
checked).

The following are **not** coerced; they are E0960 with a help that names the turnstile form:

- *A relation of a variable or of a functor's parameter*, `G.edge x y` or `A.alpha x b` at the top level.
  Its reference `arg l` is relative to the program (P7a: `arg "edge"`, or `arg "g.edge"` when the body has
  several environment variables), every program over `G` reads it, and the same text would denote a
  different judgment in `tc G` and in `tc2 G`. Write `tc G ⊢ G.edge x y`. Inside a body the program is
  known, and C3 covers the body's parameter relations (§4.3.4).
- *A relation of the file*, `road x y`, until P9f and P9g. Its program is the file's, `programOf here`,
  which P7a deferred and P9f delivers. Then C3 covers it: at the top level the user writes `road x y`
  unqualified (§1.7), and `here ⊢ road x y` is only what it elaborates to.
- *A relation of the body a proof is written in,* until C3. A member function of `tc2`'s body that states
  `path x y` would mean `tc2 g ⊢ path x y` with the functor's own parameter, as a lemma inside an Isabelle
  `context tc begin … end` block sees the locale's predicates unqualified. Reading the enclosing body's
  rules from inside it needs the same elaboration phase as `programOf here` (the body's object items are
  elaborated after its meta members). This is variant C3 of §4.3, planned after that phase (P9f, P9g).
  Until then such an atom is E0960; today it is accepted as the meaningless `⇑(path x y)` (checked).
- *A relation computed by a meta function* (a family of object constants, `len[int]`): no program declares
  it syntactically.
- *A nullary relation*, `fast.flag`: as a type it is the fact type `⇑fast.flag`, whose single value is the
  fact's identity, as today. The proposition is `fast ⊢ flag`.

### 2.4 Which database

The coercion uses exactly the database that P7c gives a turnstile written without `[…]` at the same
place:

- **In a declaration's type** (and its parameters' types): the one anonymous implicit binder that all such
  judgments of the declaration share, coerced atoms included. It has no name, so it cannot be referenced
  or matched. A statement that must relate it to another term, such as a hypothesis `placed D A` defined
  over a database, names the database with `⊢[D]` (`D` a free variable) and keeps the turnstile, or states
  the hypothesis over relations instead (§1.2).
- **Elsewhere** (a definition's value, a clause, a lambda outside a declaration's type): a metavariable
  solved by unification. If it stays unsolved, E0947 asks for `⊢[e]`. In `placed (d : db) (a :
  abstraction) : Type = (x : a.node) -> (coarse a).reached x -> …` nothing determines it, so that
  definition keeps `coarse a ⊢[d] reached x`.
- **A named database has no coerced form.** `P ⊢[D] r t̄` is written with the turnstile; inside a body,
  with C3, as the prefix `⊢[D] r t̄` (§4.3.3). This is by design: the abbreviation is for the common case,
  and `[…]` keeps an explicit database visible, as Beluga's contextual types `[Ψ ⊢ M]` keep their
  context visible.

The identifier `d` has no special meaning, in the coercion as anywhere (L27).

### 2.5 Binders

Nothing is bound by a declared name. Two things need care:

- *Free variables in a coerced atom.* `G` in `(tc2 G).path x y` is a free uppercase variable of the
  declaration's type like any other, bound by the existing implicit-argument mechanism (reference
  `meta/functions.md`, "Implicit arguments"); the atom is ordinary syntax, so the existing collection of
  free variables sees it. `(tc G).path` and `(tc2 G).path` share `G` because they are the same variable;
  no merging rule is involved.
- *The anonymous database binder.* P7c creates it when a declaration's type contains a judgment without
  `[…]`, which it finds syntactically (`Judgment` nodes, as P7b did). A coerced atom is not a `Judgment`
  node, so P9b's pre-pass adds the coercion's *candidates*: an owned relation path (`m.r`, `(f ā).r`, an
  opened instance relation), applied or not, in a *syntactic type position*: the declared type itself, an
  arrow's domain and codomain, a binder's type, and an argument of a global constant whose parameter type
  is a universe or a Π type ending in one (`iff`, `symmetric`), read from the constant's declared type.

A coercion in a type position that the pre-pass does not see (an argument of a local function variable,
`F (fast.path x y)`) gets a metavariable as "elsewhere" does, and E0947 if nothing solves it. Lean 4 avoids
the pre-pass: an unknown identifier in a header aborts elaboration, the binder is added and the header is
elaborated again (`Lean.Elab.Term.withAutoBoundImplicit`). The syntactic rule keeps P7c's single pass and
gives a predictable error.

### 2.6 Rule names, `given`, `match`, `rewrite`, `decide`

All unchanged, because the elaborated types are identical to the turnstile's:

- *Rule names* `r.k`, labels and `given` are resolved against the expected derivation type (P7b), so they
  work below coerced types without qualification. The per-relation pattern synonyms that chapter 10.1 of
  the proofs note sketched, `pattern (tc2 G).path.base E = path.1 E`, are not needed: a label `@base` on
  the rule already names it (P7b, `tests/run/p7b_rules.hgn`).
- *`match` and `rewrite`* abstract over normal forms (P3), which are `derives …`; a variable `x` of the goal
  is found inside `v {G.node} ⟨$x⟩` as for the turnstile.
- *`decide n tt`* proves `trip.path berlin rome` as it proves `trip ⊢ path berlin rome`: its type is
  `so (holds n p a) -> derives p d a`, unified with the coerced goal, whose database is the omitted one.
- *Coverage and case splits* see `derives` and split into the program's rules (P7b's Π extension).
- *Termination*: premises are below `fire`, as before.

### 2.7 Hovers and printing

The printer is independent of the scope of a file (P2b's decision for operators), so it cannot know
whether a judgment was written with a turnstile or as an atom. It keeps printing the canonical form `tc G ⊢
path x y`. This also shows the program and, when it is named, the database (`⊢[D]`), which the atom form
cannot show. Hover on the relation name of a coerced atom shows the relation (go to definition goes to its
declaration), and hover on the atom shows the judgment, as Lean shows an inserted coercion (`↥s`) instead
of hiding it.

### 2.8 Negation and aggregates

A coerced atom elaborates to whatever `P ⊢ r t̄` elaborates to. Today that is `derives`, the positive
fragment, also for programs with negations; §6.3 shows that this was wrong. The stop-gap E0961 is merged
(P9a), and the stratified reading (P9c) replaces it. Both apply to the coercion unchanged.

### 2.9 Name resolution and ambiguity

The coercion introduces **no name**. The head of an atom is resolved exactly as today (shadowing by the
file, `%use` conflicts E0109, local variables first); only if it resolves to an object relation that a
program owns is the coercion inserted. So:

- A meta function named like an object relation keeps whatever meaning it has today: if the head
  resolves to the meta function, nothing is coerced.
- A local variable or a pattern variable named like a relation shadows it, as everywhere.
- A record of relations that is not a module, such as a variable `G : graph` or a functor's parameter seen
  from outside its body, owns nothing: `G.edge x y` is E0960, never a judgment of some guessed program.
- Object positions are not affected: in a rule, a query, a formula function or under an explicit quote
  `<…>`, an atom is object code as today. The coercion applies only where a *meta type* is expected.

### 2.10 What level 3.5 is not

It is not level 4. `(tc2 G).path` is not a family: it has no constructors of its own, it is not injective
for unification (`?R x y =?= tc2 G ⊢ path x y` is a higher-order problem, solved only when `?R` is given), and
a derivation is a `derives` value. Meta functions that walk derivations (`route`, chapter 10.2 of the
proofs note) are written over `derives` as today. Per-relation adequacy does not arise: the coerced atom
is the judgment, and the one adequacy statement (reference `std/semantics.md`, "Adequacy") covers it.

## 3. Prior art, per mechanism

| mechanism of this design | prior art | what Hugin takes, what it does not |
|---|---|---|
| a coercion inserted where a *type* is expected | Lean 4's `CoeSort` (a term used as a type, `↥s` for `s : Set α`); Rocq's coercions to `Sortclass` | the trigger "expected a sort"; not a user-extensible class (Hugin has no type classes, P2b) |
| a coercion inserted by expected type at all | Hugin's stage inference (`⇑`, quote, splice, lifting; Kovács 2022) | the same elaborator position (`inferU`, checking against a universe) |
| eta form for unapplied relations | Hugin's stage inference eta-expands an object relation to a formula function | the same rule, with `Type` in place of `⇑prop` |
| the abbreviated judgment hides the program | Abella's `{A}` for `{nil \|- A}`, with the one specification fixed by `Specification "file".` | Abella hides the program but keeps the braces that mark an object judgment; A drops the marker and takes the program from the relation's owner |
| the relation *is* the proposition | Isabelle's `inductive` predicates, Lean 4's `inductive … : α → α → Prop`, Twelf's type families | the surface only: level 3.5 keeps one judgment, level 4 would make the relation a family |
| explicit context stays visible | Beluga's contextual types `[Ψ ⊢ M]` | `⊢[e]` stays the form for a named database |
| "which program" for a functor's relation | Isabelle locales (`locale … fixes`, `context … begin`, `interpretation fast: tc road`); Agda parameterised modules and `variable`; Lean `section`/`variable`; Rocq `Section`/`Context` | at the top level, the functor's argument is a variable the user writes (`tc G`), so the abstraction is the ordinary one over free variables; in C3 the body's own parameter is the locale's `fixes` and an instance's lemmas its `interpretation` |
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
`Specification "add".` (`src/prover.ml`, `clauses`), the first command of a `.thm` file. There is one
program per development, so the abbreviation can drop it. It does **not** drop the braces: a bare atom
`add N z N` in a theorem is a formula of the reasoning logic, an inductive definition introduced by
`Define`, never a specification judgment; `examples/first-order/add.thm` states `Theorem add_base :
forall N, {nat N} -> {add N z N}.`, with every object judgment in braces. So Abella is an *ambient program
with marked atoms*, variant C2 of §4.3. Hugin has several programs per statement (`tc` and `tc2` in Proof
A), so with A the program comes from the relation's owner, and the marker is dropped because the expected
type already says that a proposition is meant.

**Isabelle's locales** answer the "which program" question for parameterised specifications. A `locale tc
= fixes edge :: "'a ⇒ 'a ⇒ bool"` with an `inductive path` inside a `context tc begin … end` block states
lemmas about `path` unqualified, with `edge` fixed; after `end`, they are abstracted over `edge`, and
`interpretation fast: tc road` instantiates them as `fast.lemma`. At the top level Hugin makes the same
abstraction per declaration, with a variable the user writes: `(tc2 G).path x y` abstracts over `G`, and
`forFast` is the interpretation. Inside a body (C3) it is the locale's own: the parameter `g` of `tc2 (g :
graph)` is fixed, and the instance inherits the lemmas. Isabelle's `inductive` package
also gives the relation's rules the names `path.intros(1)`, which P7b followed with `path.1`.

**Agda** offers two mechanisms that could implement parts of this by hand. A `syntax` declaration
(`doc/user-manual/language/syntax-declarations.lagda.rst`) gives a function a mixfix surface, `syntax
derives P d a = P ⊢[ d ] a`, but only for a fixed function symbol, and the atom `path x y` has no such
symbol: the program depends on where `path` is declared. Instance arguments
(`doc/user-manual/language/instance-arguments.lagda.rst`) could supply an implicit program `{{p :
Program}}`, which is alternative C below. Parameterised modules are the precedent for C3.

**Generalisation binds only written names.** Agda's `variable` declarations
(`doc/user-manual/language/generalization-of-declared-variables.lagda.rst`) generalise a name only where
the user writes it in a signature, and Lean 4's auto-bound implicits bind only an unbound identifier that
occurs in the header (`Lean.Elab.Term.withAutoBoundImplicit`). Neither invents a binder from another
declaration's parameter names, which is what P7b's generalisation of `tc ⊢` did and L27 removed. Level 3.5
follows the same rule: `G` in `(tc G).path` is bound because it is written, and the anonymous database is
P7c's, which cannot be referenced by any name.

**Twelf and Beluga.** In Twelf a relation is an LF type family (`path : node -> node -> type.`), so
"relations as propositions" is the starting point, and meta-theorems are total relations over it (`%total`).
That is level 4, with the program as the signature. Beluga reasons about LF objects in explicit contexts,
`[Ψ ⊢ M]`, and does not abbreviate the context away; Hugin follows it in keeping `⊢[e]` for a named
database.

## 4. Alternatives

### 4.1 A: the judgment coercion (recommended, with C3)

As in §2: one elaboration rule at the place where stage inference inserts `⇑` today, triggered by an
applied relation that a program owns, where a meta type is expected.

### 4.2 B: derived meta members per relation

Chapter 10.1 of the proofs note sketched this: for each relation `r` of a body, the compiler derives a meta
member `(tc2 G).path : G.node -> G.node -> Type = [x] [y] tc2 G ⊢ path x y`, and rule pattern synonyms.

- The module field `path` is already the object relation (`fast : { path : ⇑(city -> city -> rel) }`, from
  `--print-after elaborate`). A second field of the same name needs names overloaded by stage, as shared
  data has them (reference `meta/families.md`, "Names and stages"), but for relations, which are not data:
  the "crack in 2LTT's separation" that chapter 10.2 of the proofs note lists as a cost of level 4.
- `(tc2 G).path` as a member of an application evaluates `tc2 G`, which creates an instance (generativity,
  D10). To avoid it, the member must be recognised syntactically, at which point it is alternative A with
  an extra generated declaration.
- A member per relation of every body costs compile time and incrementality (a rule edit changes a
  member's type), and the pattern synonyms duplicate P7b's rule names.
- Gain over A: none that A's eta form does not give (`symmetric (undirected G).reach`).

### 4.3 C: an ambient program

The idea: a *scope* fixes one program, and inside it atoms are judgments of that program without naming
it. Three variants differ in what the scope is and whether the atom is marked. They are kept separate
below, each with its end state, and §4.3.5 relates them to A.

#### 4.3.1 Prior art, precisely

- **Abella** fixes one specification per development with `Specification "add".`, the first command of a
  `.thm` file (`src/prover.ml`, `clauses`), and writes its judgments `{L |- A}`, `{A}` for an empty
  context (`src/metaterm.ml`, `Obj`, abella/abella 957bb74). The program is ambient, but **bare atoms are
  not propositions about it**: a bare `add N z N` is a formula of the reasoning logic G (an inductive
  definition from `Define`), and every specification judgment is in braces, as in
  `examples/first-order/add.thm`: `Theorem add_base : forall N, {nat N} -> {add N z N}.` Abella is
  variant C2.
- **Isabelle's locales** are variant C3's model. `locale tc = fixes edge :: "'a ⇒ 'a ⇒ bool"` fixes a
  parameter; an `inductive path` defined in `context tc begin … end` and the lemmas after it there use
  `path` and `edge` unqualified; after `end` they are known outside as `tc.path`, `tc.lemma` with `edge`
  as an argument; `interpretation fast: tc road` instantiates every lemma of the locale as `fast.lemma`
  (Ballarin, *Tutorial to Locales and Locale Interpretation*). A `context tc begin … end` block can be
  opened again in any later theory, so lemmas can be added to a locale that another theory defined.
- **Lean 4** has `section`/`namespace` with `variable`: inside `namespace Tc`, a `theorem trans` is
  `Tc.trans` outside, and `variable (g : Graph)` is added to every declaration that uses it. There is no
  instantiation of a whole namespace; each theorem is applied to its arguments.
- **Agda** has parameterised modules: `module Tc (g : Graph) where` with the inductive family and the
  lemmas inside; `open Tc g` (or `module Fast = Tc road`) instantiates all of them at once, which is
  Isabelle's interpretation without the reopening.
- **Rocq** has `Section` with `Context` (Lean's model) and functors over `Module Type`s (Agda's model).

All four elaborate in textual order: the relation or inductive family is defined before the lemmas about
it (§4.3.6).

#### 4.3.2 C1: a directive, `%program tc G.`

A directive sets the ambient program for the declarations after it, until the next `%program`. Bare atoms,
including parameter relations, are judgments of it; another program is qualified. After L27 the directive
must name the functor's argument too, and `G` is then a variable that every following declaration binds
for itself, as Agda's `variable G : graph` is generalised separately in each signature that uses it. End
state of Proof A (proposal):

```hugin
%program tc G.
tcTrans : {x y z : G.node} -> path x y -> path y z -> path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

%program tc2 G.
edgeIn : {x y : G.node} -> tc G ⊢ G.edge x y -> G.edge x y.
edgeIn (given I) = given I.
toTc2 : {x y : G.node} -> (tc G).path x y -> path x y.
toTc2 (path.1 E) = path.1 (edgeIn E).
toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).
(* edgeOut and toTc likewise *)
sameFacts : {x y : G.node} -> iff ((tc G).path x y) (path x y) = { to = toTc2, from = toTc }.
```

Proof B: `%program coarse A.` before `placed`, `sound`, `safe`, which then read as in §1.6 but at the top
level. §1.3: `%program undirected G.` and `reachSym : symmetric reach.`. §1.4: `%program trip.` and
`viaParis : path berlin rome = decide 3 tt.`. The cross-program statement `sameFacts` sits under one of the
two programs and qualifies the other, with A's form or the turnstile.

Assessment. Hugin's items are unordered: a name may be used before its declaration, the compiler orders
items by dependency (reference `meta/index.md`, "Order of elaboration"), and moving an item elaborates
nothing (`docs/INCREMENTALITY.md`, step 9). A region directive is the first construct whose meaning depends
on an item's position, and moving `toTc2` above `%program tc2 G.` silently changes the program it is about.
The `G` of the directive is a variable declared once and bound in each declaration, which is the kind of
name across declarations that L27 removed from the turnstile.
The bare name `path` would also resolve in `tc2`'s body scope instead of the file's, a second scope rule
that the reader must apply by position. A block instead of a region (`%program tc2 { … }`, Isabelle's
reopenable `context`) fixes the position problem, but it is new syntax that duplicates what a module body
already is; its one gain over C3 is lemmas for a functor whose body the user does not own (`tc` of
`std/graph`). **Rejected**; the block form is recorded as an option for library functors (§8, "Settled").

#### 4.3.3 C2: marked atoms with an ambient program

Abella's choice: the program is ambient (from C1's directive or C3's body), and a proposition is marked.
Abella's braces are not available: `{` opens implicit binders (`{x y : A}`), record types and values and
named arguments (`{X := e}`), and `{path x y}` is a syntax error today ("expected `.` after the fact",
checked), so telling them apart would need lookahead to the first `:`, `=` or `:=`. The free spelling is a
**prefix turnstile**, `⊢ path x y` (ASCII `|- path x y`), a syntax error today ("expected a type", checked),
read as `P ⊢ path x y` with `P` the ambient program. End state of Proof A inside `tc2`'s body (proposal):

```hugin
tc2 (g : graph) = {
  (* … the rules … *)
  edgeIn : {x y : g.node} -> tc g ⊢ g.edge x y -> ⊢ g.edge x y.
  toTc2 : {x y : g.node} -> tc g ⊢ path x y -> ⊢ path x y.
  toTc : {x y : g.node} -> ⊢ path x y -> tc g ⊢ path x y.
  sameFacts : {x y : g.node} -> iff (tc g ⊢ path x y) (⊢ path x y) = { to = toTc2, from = toTc }.
}.
```

Proof B: `reached x`, `areached b`, `a.alpha x b` become `⊢ reached x`, `⊢ areached b`, `⊢ a.alpha x b`.
§1.3: the η form has nothing to mark, so `symmetric reach` would need A's rule or a lambda `[x] [y] ⊢ reach x
y`. §1.4: `viaParis : ⊢ path berlin rome = decide 3 tt.` inside `trip`'s body.

Assessment. Marking removes A's one real confusion, `fast.path` as a fact type against `fast.path x y` as a
proposition (§5, item 1): with a marker, an atom never changes reading by application. It also covers the
cases A must refuse: a nullary relation (`⊢ flag`) and an explicit database (`⊢[e] path x y`). It costs one
token per atom, which is the turnstile minus the program. **Recommended as a complement**, not as the main
form: inside an ambient scope (C3's body, and the file once `here` exists), `⊢ r t̄` is the explicit form
for exactly those cases, while unmarked atoms follow A's rule (§8, item 5).

#### 4.3.4 C3: locale-style proofs inside the program's own body

Lemmas are members of the functor or module body they are about. Inside the body, an applied relation of
the body or of its parameter is a judgment of the body's program at the body's parameters, unqualified;
other programs are qualified as in A. The end state of Proofs A and B is §1.6. §1.3 and §1.4 (proposal):

```hugin
undirected (g : graph) = {
  (* … the rules of link and reach as in §1.3 … *)
  linkSym : symmetric link.
  linkSym X Y (link.1 E) = link.2 E.
  linkSym X Y (link.2 E) = link.1 E.
  reachTrans : {x y z : g.node} -> reach x y -> reach y z -> reach x z.
  reachTrans (reach.1 L) Q = reach.2 L Q.
  reachTrans (reach.2 L P) Q = reach.2 L (reachTrans P Q).
  reachSym : symmetric reach.
  reachSym X Y (reach.1 L) = reach.1 (linkSym _ _ L).
  reachSym X Y (reach.2 {Y := W} L R) = reachTrans (reachSym W Y R) (reach.1 (linkSym _ _ L)).
}.

trip = {
  (* … hop and path as in §1.4 … *)
  viaParis : path berlin rome = decide 3 tt.
}.
```

Every instance has the lemmas as fields: `fast.sameFacts`, `eu.sound`, `(undirected roads).reachSym`. This
already works mechanically today for lemmas about *another* program: a member function of a functor body
stating `tc g ⊢ path x y` compiles, and `fast.lem` is used at the instance's type `tc { node = city, edge =
road } ⊢ path x y` (checked at 1db9441, with P7b's database generalised inside the body). What does not work is a lemma about the
body's *own* program: naming the functor inside its body is E0105 ("`tc3` refers to itself", checked), and
there is no `programOf` of the enclosing body, because of the phase in §4.3.6.

**Where cross-program statements go.** A statement about two programs belongs in the body of one of them
when the other is a functor application it can name: `sameFacts` in `tc2`'s body, with `(tc g).path` for
the other side, and `fast.sameFacts` then replaces `forFast`. A statement about two programs that the user
does not own, or about two instances (`iff (fast.path x y) (slow.path x y)`), stays at the top level, with
A's qualified forms or the turnstile. A lemma about a library functor (`tcTrans` for `std/graph`'s `tc`)
also stays outside, since its body is closed; Isabelle reopens the locale for this, which is C1's block.

**Using a body's lemma from outside.** Through an instance, `fast.sameFacts`, as today. Through a functor,
the lemma must not create an instance: selecting a member of a functor application in meta code evaluates
the application, which is generative. Checked: `use : … = (tc3 { node = city, edge = road }).lem.` creates
an instance named `use` and the run prints `use.path berlin paris`. C3 therefore needs **member access
without an instance**: `(f ā).m`, for a meta member `m` that mentions no object constant of the body (a
lemma mentions the body's relations only through program references, `own i`), is the member function at
the arguments, read from the functor without evaluating its body (Isabelle's `tc.lemma` with the locale's
parameters as arguments). The arguments are written, `(tc2 G).sameFacts` with `G` free in a declaration's
type; a functor alone, `tc2.sameFacts`, is not a form, for the reason that `tc2.path` is not (§2.3). A member that
mentions an object constant still needs an instance (E0107 with a note, otherwise).

#### 4.3.5 The key observation: C3 is A's rule with one more owner

Inside a body, an unqualified own relation `path` is a relation whose owner is the enclosing body; a
parameter relation `g.edge` is one whose owner is ambiguous at the top level but not inside a body: it is
the body's program reading its parameter. So C3 needs no rule of its own: it is A's coercion (§2.1) with
the owner table of §2.3 extended by one row, "an own or parameter relation written inside a body: the
enclosing body, at its own parameters". This is the row that §2.3 deferred.

A and C3 are therefore **complementary, not alternatives**. A gives the qualified forms, which are needed
wherever no body encloses the statement: cross-program statements, statements about instances, lemmas about
library functors. C3 gives the unqualified forms where one body encloses the statement. Both elaborate to the
same `derives` term, print the same way, and share rule names, the omitted database, coverage and the
implementation of the coercion. C1 and C2 are different: C1 is an alternative source of the ambient
program (rejected, §4.3.2), C2 an orthogonal choice of marking (adopted as a complement, §4.3.3).

#### 4.3.6 The blocker: lemmas need the body's rules, which are elaborated last

**Today's order.** A file's declarations, definitions and clauses are elaborated in dependency order, then
its object items (reference `meta/index.md`, "Order of elaboration"). A module body does the same inside
its item: object constants first, then the meta members by their dependency cycles, then the body's rules
and queries (reference `modules.md`, "Module bodies"). Rules may use meta members (splices, formula
functions, meta functions in heads), so they come after them. A lemma about the body's rules needs the
program value of those rules, so it must come *after* them: the dependency is reversed for exactly the
members that state propositions about the body.

**How others order this.** Lean 4, Isabelle and Agda elaborate in textual order: an `inductive`
(Isabelle: `inductive`; Agda: `data` with its constructors) is complete before any later lemma, and a lemma
cannot be part of the mutual block that defines the family (Lean's `mutual` contains only inductives or only
definitions; Agda's interleaved `mutual` still checks a function's clauses after the constructors they
match). The order "definition before proof" is given by the text. Hugin's items are unordered, so the same
order has to follow from dependencies: a lemma depends on the rules it is about.

**The phase (P9f).** For a body, and the same for a file (which gives `programOf here`):

1. Classify the meta members. A member is *program-dependent* if, syntactically, it mentions the
   enclosing scope's program: an own or parameter relation applied in a type position (the candidates of
   §2.5), a prefix judgment `⊢ r t̄`, `programOf here`, or another program-dependent member. The test is
   the name-resolution pre-pass that P9b adds for the database binder (§2.5), so it costs no elaboration.
2. Elaborate the other members as today, then the object items (rules, queries).
3. Build the scope's program value from the elaborated rules, as `programOf` reads a body (P7a): for a
   functor body, P7b's folded program constant applied to the body's environment variables (`g`); for a
   module value, a closed program; for the file, `programOf here`.
4. Elaborate the program-dependent members by their dependency cycles, with the coercion's owner for
   unqualified atoms set to that program.
5. **Cycles.** A rule or query that mentions a program-dependent member, directly or through another
   member, depends on its own program: E0962, "the rule uses `m`, which states a property of this body's
   rules". Examples: a formula function whose type mentions `path x y` as a proposition and that a rule
   calls; a module-wide directive of the file that is program-dependent (its expansion changes the rules
   it is about). Nothing else changes: a program-independent member keeps today's position, so no existing
   program is reordered.

In bodies, one restriction of E0907 has to go for proofs to live there: `%opaque` (checked: "`%opaque` in
module bodies are not supported by the meta level"). Everything else that a proof needs (member functions
with clauses, typed definitions with parameters) is accepted in bodies today.

**Size.** The classification and the reordering in bodies: 400–700 lines; the same for files with
`programOf here` and E0962: 300–500 more (P7a deferred exactly this, "needs a new phase … and a rule that
splices such a value rejected as a cycle").

**Incrementality (#126).** A functor body is part of its declaration item, which the `Signatures` query
elaborates with all declarations of the file; an edit inside a body, a rule or a lemma, already elaborates
`Signatures` again and every object item after it (`docs/design/incrementality-2.md`, §2: `ElabItem`
depends on the whole `Signatures` value). C3 inside bodies therefore costs no new invalidation, only the
time of the body's own lemmas on every edit of the body, as member functions cost today. At the file level
the cost is new: today object items are elaborated after the declarations and nothing among the
declarations depends on them; `here`-dependent declarations add a query after the `ElabItem`s that depends
on all object items of the file. With early cut-off on the program value (salsa's backdating, §4.1 of the
incrementality note), an edit that leaves the program data unchanged (whitespace, a moved rule, a comment)
re-checks nothing, and an edit of a rule re-checks the `here`-dependent declarations and nothing else
(the cycle rule guarantees that no object item depends on them).

#### 4.3.7 What C3 gains, and what it loses

Gains:

- **Parameter relations without the turnstile.** Inside `tc2`'s body, `g.edge x y` has one program; outside,
  it has none (§2.3). Proof B's `a.alpha x b` and Proof A's `edgeIn` get shorter.
- **Lemmas inherited by every instance.** `fast.sameFacts` is the theorem for the run's instance, with no
  `forFast` written; Isabelle's `interpretation`, Agda's module application.
- **Proofs next to the program.** A rule edit and the lemma it breaks are in one body; the body's
  signature can export the lemmas with the relations.
- **No variable for the program's argument.** `g` is the body's own parameter, in scope by its binder `tc2
  (g : graph)`, so the lemmas need no free `G`; only the anonymous database is implicit.

Losses and confusions:

- **Closed bodies.** Lemmas can be added only to bodies the user writes; a library functor's lemmas stay
  outside (A), unlike Isabelle's reopenable contexts.
- **Module types grow.** Every lemma is a field: `%use fast.` opens `sameFacts` too, and `%use fast. %use
  slow.` makes the lemma names ambiguous (E0109, which P9e cannot resolve, since both have the same type
  shape). A signature ascription hides lemmas it does not list.
- **A second elaboration order in bodies.** Whether a member comes before or after the rules depends on
  whether it mentions the body's relations as propositions; a cycle through a rule is an error (E0962) that
  a user may not expect from a formula function.
- **Library load time.** Proofs inside library bodies are checked wherever the library is loaded (the
  load time of `std/semantics`, 2.2 s, was a concern in P6); library proofs are better kept in separate
  files, with A.
- **Member access without instance** is a new rule about generativity, with an error for members that
  mention object constants.

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

| | A coercion | B derived members | C1 directive | C2 marked atoms | C3 in-body proofs | A + C3 (recommended) | D by hand |
|---|---|---|---|---|---|---|---|
| new syntax | none | none (generated names) | `%program` | prefix `⊢ r t̄` | none | none (plus C2's prefix, optional) | none |
| core change | none | none | none | none | none | none | none |
| new names in scope | none | a member per relation | none | none | lemmas become fields | lemmas become fields | user's |
| what `path x y` means | the head's owner | the head's owner | the directive above it | (always marked) | the enclosing body | owner, or the enclosing body | user-defined |
| parameter relations without `⊢` | no | no | yes | marked | yes, inside the body | yes, inside the body | by hand |
| cross-program statements | qualified | qualified | one program qualified | one program qualified | one in a body, other qualified (needs A or `⊢`) | as C3 | explicit |
| lemmas inherited by instances | no | no | no | with C3 | yes | yes | no |
| lemmas for library functors | yes | yes | yes | with C1 | no (closed bodies) | yes, with A | yes |
| depends on item order | no | no | **yes** | no | no | no | no |
| elaboration phase needed | no | no | no (yes for in-body) | with C3 | **yes** (P9f) | yes, for the C3 part | no |
| unapplied relation (η) | yes | yes | yes | no | yes | yes | yes |
| shorter than `tc G ⊢ path x y` at the top level | no (`(tc G).path x y`); yes for instances, opened names, η | no | yes | slightly (`⊢ path x y`) | n/a | as A | no |
| lines (§5) | 550–900 with P9a | 1000–1500 | 800–1200 | +100–200 on C1 or C3 | 1150–2050 with the phase | 1700–2950 | 0 |

### 4.6 Recommendation (revised)

Revision 1 recommended A alone and dismissed C in ten lines; revision 2 found that dismissal wrong for
C3. L27 moves the balance further: with `tc.path` gone, A's forms at the top level are no shorter than the
turnstile (`(tc G).path x y` against `tc G ⊢ path x y`, §1.1). The honest comparison now:

- **C3 carries most of the value.** It gives what neither the turnstile nor A can: parameter relations
  without the turnstile, lemmas that every instance inherits (no `forFast`), proofs next to the rules, and
  no variable for the program's argument (the body's `g` is declared). It is the established design:
  Isabelle's locales with `interpretation`, Agda's parameterised modules with module application.
- **A's remaining gains are real but small:** the η form (§1.3: `symmetric (undirected G).reach`, and
  database-free hypotheses, §1.2), instance and opened names (§1.4), and E0960's help instead of today's
  meaningless `⇑(r t̄)`. Its implementation is also C3's: C3 is A's rule with the enclosing body as owner
  (§4.3.5).
- **C3 cannot replace A or the turnstile.** Statements about two programs, about instances, and about
  library functors have no enclosing body.
- **C3 is blocked by the phase of §4.3.6**, which is also `programOf here`'s blocker; it is the larger and
  riskier step, worth doing once for both.
- **C1 is rejected**: an order-dependent region in an unordered language, and after L27 a directive-wide
  variable `G`. Its block form, reopening a library functor, is recorded as an option.
- **C2 is adopted as a complement**: the prefix `⊢ r t̄` and `⊢[D] r t̄` inside an ambient scope, for
  nullary relations and named databases (§1.6's Proof B variant), where A must refuse.

**Recommendation, as approved: A and C3, with the phase P9f first in priority.** P9f starts at once and
also delivers `programOf here`; P9b (A) follows P7c and is kept because it is cheap (400–650 lines), gives
the η form and instance names, and is the mechanism that P9g extends; P9g (C3, with C2's prefix and member
access without instance) follows both. B and D are rejected (D stays possible). The batch order is §7.

## 5. Costs

**Lines (estimate).** Scala, Hugin library, reference and tests together: P9a 150–250, P9b 400–650, so A
is 550–900 (the proofs note budgeted 500–900 for P9 in chapter 12). P9b shrank with L27: no functor
written alone, no generalisation of its parameters, no merging; most of its Scala is the owner lookup and
the pre-pass that joins coerced atoms to P7c's anonymous database binder; the judgment itself is
`inferJudgment`. The open flags add P9c 900–1400, P9d 150–300 and P9e 200–350 (§7). The locale-style part
adds P9f, the phase, 700–1200 (it also delivers `programOf here`), and P9g, C3's surface, 450–850:
together 1150–2050, so A with C3 is 1700–2950 lines, about twice the level 3.5 budget of chapter 12,
because it includes the `here` phase that P7a deferred. P7c itself is not counted here.

**Risks.**

- *Name resolution.* The owner of an opened constant (after `%use fast.`) needs a map from object constants
  to the module instances that declared them; P7a records instances (`ModuleInstance`) for `programOf m`,
  so the map is that record inverted, built once per file. An anonymous instance (`%use (tc { … }).`) has
  an owner too, `_m1`, and prints as `programOf _m1 …` (P7b's printing of bodies reached through an
  instance).
- *Ambiguity between object relations and meta names.* None is introduced (§2.9), and no new reading of
  any text that is an error today other than the applied relation in a meta type (§2.2).
- *A meaning change for accepted programs* (§2.2), limited to types without closed inhabitants; P9a
  (merged) turned them into errors first, so a program that relied on them fails loudly before P9b gives
  them a meaning.
- *Performance.* The coercion is syntax-directed: one name lookup per applied path in a type position, and
  the elaboration of a judgment, which the turnstile form costs anyway. No evaluation, no new unification
  problem. The pre-pass for the database binder walks a declaration's type trees once, as P7c's does.
- *Error messages.* A failing coercion must say that the atom was read as a proposition: arity and column
  errors reuse E0945's text with "the atom `fast.path x`, read as `fast ⊢ path x`". An applied relation
  that no program owns is E0960, naming the turnstile form (§1.5).

- *C3's phase* (P9f) is the riskiest step: a second elaboration order inside bodies and files, a new
  cycle error (E0962), and at the file level a query that depends on all object items (§4.3.6). It changes
  the position of no existing item, since only program-dependent members move, and today there are none.
- *C3's member access without instance* (P9g) touches generativity: reading a member from a functor
  without evaluating its body is valid only for members that mention no object constant of the body,
  which the compiler must check; a mistake there would share relations between instances (D10).

**What it makes confusing.**

1. `fast.path` (unapplied, at `Type`) is the fact type, while `fast.path x y` is a proposition: one name,
   two readings by application. Lean has the same split (`↥s` against `s x`); the hover shows which one.
2. The program's own relations may drop the turnstile while parameter and file relations keep it (Proof
   A's `edgeIn`). The rule is principled (only an owned relation has one program) but visible.
3. A nullary relation needs the turnstile (`fast ⊢ flag`), because `fast.flag` at `Type` is the fact type.
4. Printing shows `tc G ⊢ path x y` where the user wrote `(tc G).path x y`.
5. A named database has no coerced form, so a declaration that names it (`⊢[D]`) mixes forms or keeps the
   turnstile throughout (§1.2).
6. With C3, the same text `path x y` means `tc2 g ⊢ path x y` inside `tc2`'s body and is an error (or
   another instance's relation, if opened) outside it; the losses of §4.3.7 apply.

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
gap is a coverage gap, not only a cosmetic one. Checked at 1db9441, in P7b's notation (with P7c: `{x y :
G.node} -> both G ⊢ edge x y -> both G ⊢ edge y x`):

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

1. *Stop-gap (P9a, merged as 05b8b45).* A judgment, written or coerced, whose program has a negation or an
   aggregate in a rule is E0961, "the judgment notation covers programs without negation and aggregates; use `nderives` of
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
   `given` is `ngiven`. Proof by evaluation exists since P8b (merged, 468f937): `std/certify`'s
   `perfectHolds n p ins` decides membership in `perfect p (memOf ins)`, both ways. P9c connects `decide`
   to it through the adequacy lemma `perfect p d a ↔ judged p d a`.

   This is the iterated fixpoint of Apt, Blair and Walker, read stratum by stratum, as DatalogCert
   (Benzaken, Contejean and Dumbrava, ITP 2017) evaluates a stratum with negations read in the strata
   below, and as Schlichtkrull, Hansen and Nielson's *Stratified Datalog* (AFP 2025) indexes the semantics
   by strata. How a negated premise is best presented in patterns is the one sub-question that P9c settles
   in a short addendum before it is implemented.

#### 6.3.1 Addendum (P9c): negated premises and aggregate witnesses in rule names

*Positions.* A stratum-local rule name `r.j p̄` has one written premise for each atom, negated atom and
aggregate of the rule's body, in body order; comparisons are not written (`ncmp _` in a pattern, proved
by evaluation in an expression), as in P7b. `ok X :- node X, not bad X.` is `ok.1 B N`. The positions
are those of `npos`, `nneg` and `nagg` in `npremises`, so the count is the body's, and a missing negated
premise is P7b's E0948 "has 2 premise(s), but 1 are given".

*Patterns: the premise as it is.* The pattern variable of `not q t̄` binds `nneg`'s argument, `absent (upTo p
j d) xs us b`, and that of an aggregate its witness `aggHolds …`, unchanged. A pattern cannot apply a
function: Hugin has no view patterns, and rule names are Agda's pattern synonyms, which expand to
constructor patterns only (Agda's `with` and Idris' views are separate mechanisms). For a negation
without local variables, `N enil : upTo p j d (atom q vs) -> empty` refutes the facts of `q` below the
rule's stratum, and `given F` lifts a judgment `F : P ⊢ q t̄` into them (below), so `okNotBad (ok.1 B N)
F = N enil (given F)` needs no stratum number. The library lemma `refuted k j tt N : notIn (judged p k d)
…`, the direction §6.3 names, is there for the general case; its strata are explicit (below, *Inference*).

*Expressions: a refutation.* In an expression, the argument for `not q t̄` without local variables is a
refutation `P ⊢ q t̄ -> empty` of `q`'s own stratum-local judgment, which the elaborator makes the premise
with `absentOf k j tt` (`k` the stratum of `q`, `j` the rule's); the premise `absent …` itself is accepted
as well (a pattern variable passed on). This is how a negative premise reads where negation is a
function into the empty type: Lean's and Rocq's inductive definitions accept a premise `¬ q x` exactly
when `q` is defined before (strict positivity), and the constructor then takes a refutation, as
DatalogCert reads a negated literal as absence from the model of the strata below. With local
variables (`not g.edge N _`), the argument is the premise `absent …`, which quantifies over them. An
aggregate's argument is its witness, a record (P6), in both positions.

*`given`.* At a stratum, `given I` is `ngiven` down to the program's input facts for an input relation
(an expression builds `{ fst = tt, snd = I }` there; a pattern binds the record, so `I.fst` refutes a
relation with rules), and for a relation with rules whose stratum `k` is at or below the expected one,
`given F` lifts its judgment `F` by `ngiven`. A derivation of a fact of a lower stratum inside a rule
name is lifted the same way, so that premises have their relation's stratum-local type.

*Inference.* Two applications of the same definition are compared by their arguments without solving
unknowns (smalltt's flex state), so the implicit arguments of a lemma over `judged p k d` or `upTo p k d`
are not inferred from them: the conversions take their strata explicitly, and the elaborator, which
knows them, inserts `absentOf` and the `ngiven` chains itself.

### 6.4 Other flags that level 3.5 touches

- *L17, `programOf f : graph -> program`* for a bare functor. Level 3.5 never uses the bare form: a coerced
  atom always has an application (`(tc G).path`) or an instance, and in C3 the body's program at its own
  parameter. L17 stands as implemented (§8, "Settled"). P7a's D12 realisation (the converse round trip
  proved on the image of `quote` instead of trusted) is not touched.
- *L22c, `{X := W}`.* Pattern variables are uppercase; chapter 1 of the proofs note now writes `{X := W}`,
  as the test does (corrected with this note).

## 7. Batches

Each batch is one PR. P9a is merged (05b8b45). P7c (L27 and L28: no blessed names in judgments, parameter
relations through the user's argument) is running on `fix/proofs-p7c-explicit-generalisation`. Error
codes: E0960 and E0961 are taken (P9a); P9f takes E0962, the next free code after P8b's E0955–E0957.

| batch | content | lines | tests | enables |
|---|---|---|---|---|
| **P9a** honest types (**merged**, 05b8b45) | an applied relation under `⇑` in a meta type is E0960; a judgment over a program with negation or aggregates is E0961; reference and error explanations | done | neg: `e0960_*`, `e0961_*` | correctness; the slot for P9b |
| **P9b** the judgment coercion | the coercion and its η form (§2.1), the owner lookup (§2.3), the pre-pass that joins coerced atoms to P7c's anonymous database binder (§2.5), E0960 for unowned relations, E0945 texts for coerced atoms; reference: `std/semantics.md` "Relations as propositions" | 400–650 | run: `p9b_proof_a`, `p9b_proof_b` (§1.1, §1.2 as written, including the relation-valued `placed`), `p9b_relations` (§1.3, §1.4, `weak.v.vertex`, `(f ā).r`); neg: a variable's relation `G.edge`, file relation, nullary relation, a functor written alone (`tc.path`, E0107), a coercion outside a type position with an unsolved database (E0947); LSP: hover on `(tc G).path x y` shows `tc G ⊢ path x y`, a split below it | relations passed to meta combinators; instance and opened names |
| **P9c** stratified judgments | §6.3 step 2: the stratum-local reading, `upTo` and the adequacy lemma in `std/strata`, rule names over `nfire`/`npos`/`ncmp`/`nneg`/`nagg`, `ngiven` chains; E0961 lifted; the reference's adequacy statement extended to stratified programs | 900–1400 | run: `p9c_negation` (`ok.1` proves `m ⊢ ok berlin`; `never` no longer provable), `p9c_aggregate`; neg: rule name with a missing negated premise | proofs about programs with negation in the notation |
| **P9d** multi-head names | §6.2: names per (rule, head) pair, head proof `there^j here`, splits offer them, labels against later heads | 150–300 | run: `p9d_heads` (`flip` with `edge.1`, `edge.2`; a constructor term in a head); neg: label naming two heads of the goal's relation | coverage of multi-head rules with rule names |
| **P9e** overloaded opened names | §6.1: E0109 among meta constants resolved by P2b's head rule; hover and go to definition show the chosen constant; E0932/E0933 for names | 200–350 | run: `p9e_overload` (both `decide`s in one file); neg: no expected type (E0932) | chapter 1's `decide 3 tt` with `std/decide` open |
| **P9f** the proof phase | §4.3.6: program-dependent members of a body or file classified by a name-resolution pre-pass (shared with P9b's) and elaborated after its object items; the scope's program value (P7b's folded constant for a functor body); `programOf here`; E0962 for a rule that uses a program-dependent member; the file-level query after `ElabItem` with early cut-off on the program value; reference `meta/index.md` ("Order of elaboration"), `modules.md` | 700–1200 | run: `p9f_here` (`programOf here`, a turnstile `here ⊢ road x y`); neg: `e0962_program_cycle` (a formula function about the body's rules used by a rule; a program-dependent module-wide directive); incremental: a rule edit re-checks only `here`-dependent declarations, a moved rule nothing | `programOf here`; the order C3 needs |
| **P9g** locale-style proofs (C3) | §4.3.4, §1.7: the enclosing body as owner of its own relations and of a functor body's parameter relations, and the file as owner of its relations at the top level (written unqualified); the prefix `⊢ r t̄` and `⊢[e] r t̄` with the ambient program (C2's complement); `%opaque` in bodies; member access without instance, `(f ā).m`, with the check that `m` mentions no object constant of the body | 450–850 | run: `p9g_proof_a`, `p9g_proof_b` (§1.6 as written, both variants of `placed`, `fast.sameFacts`, `eu.sound` used at the instance), `p9g_file` (§1.7: `trip x y` at the top level, `decide`, a lemma of the file), `p9g_relations` (§4.3.4's `undirected` and `trip`, `(tc2 G).sameFacts` from outside without an instance: the run prints no extra relation); neg: member access to a member that mentions an object constant; LSP: a hole inside a body shows `tc2 g ⊢ path x y` | proofs inside programs, inherited by instances |

Order, as approved:

- **P7c** runs first (L27, L28).
- **P9b, P9c, P9d** follow P7c, because all three change the notation's code (`core/elab/Judgments.scala`):
  the coercion, the stratified reading, the head numbering. They may run in sequence or with conflict
  control, as P7b and P6 did.
- **P9e and P9f** start now: P9e touches name resolution and P2b's overloading, P9f the order of
  elaboration; neither depends on the notation. P9f provides the name-resolution pre-pass if it lands before
  P9b, and P9b reuses it.
- **P9g** follows P9f and P9b.

Following the house rule (L10), each batch's agent runs only the tests it adds or changes; CI runs the
suite.

## 8. Decisions (approved)

1. **A + C3.** The judgment coercion A (an applied relation that a program owns, where a meta type is
   expected, is that program's judgment at P7c's omitted database; no keyword, token, directive, core rule,
   generated declaration or blessed name), together with C3, locale-style proofs, which is A's rule with the
   enclosing body or file as owner (§2, §4.3.5). **Approved.**
2. **The η form.** An unapplied owned relation where `⇑τ₁ -> … -> ⇑τₙ -> Type` is expected is `[x̄] P ⊢ r
   x̄`, so that `symmetric (undirected G).reach` works (§1.3). **Approved.**
3. **C3's scope: module bodies, functor bodies and the file itself.** Inside each, its own relations are
   propositions, written unqualified; inside a functor body, so are its parameter's relations (`g.edge x
   y` in `tc2 (g : graph) = { … }`). Lemmas are members, and instances inherit them (`fast.sameFacts`,
   `eu.sound`). At the top level of a file, the user writes `trip x y`, **not** `here ⊢ trip x y`:
   `here ⊢ trip x y` is only the elaborated meaning, which hovers print (§1.7). Other programs' relations
   are qualified with A's forms (`fast.path x y`, `(tc G).path x y`) or the turnstile. **Approved.**
4. **The phase P9f.** Program-dependent members of a body or file are elaborated after its object items; a
   rule that uses one is E0962; at the file level, a query after the object items with early cut-off on
   the program value. It delivers `programOf here`, and has priority over A (§4.3.6). **Approved.**
5. **The prefix turnstile.** `⊢ r t̄` and `⊢[e] r t̄` (ASCII `|-`), with no program, are the ambient
   program's judgment inside a body or the file: the form for nullary relations and named databases
   (§4.3.3). **Approved.**
6. **Negation and aggregates.** For a program with negations or aggregates, `P ⊢ r t̄` (and a coerced
   atom) is the stratum-local `nderives` judgment, with rule names over `nfire` and `ngiven` chains and
   written negated premises; it replaces E0961 (P9c, after a short addendum on negated premises in
   patterns, §6.3). **Approved.**
7. **Multi-head rule names.** Rule names number (rule, head) pairs per head relation; head proofs `there^j
   here`; `crule.index` unchanged (P9d, §6.2). **Approved.**
8. **The `decide` clash** is resolved by type: E0109 among meta constants opened by two `%use` items is
   decided by P2b's head rule (P9e, §6.1). **Approved.**
9. **Member access without instance, and `%opaque` in bodies.** `(f ā).m`, for a meta member that mentions
   no object constant of the body, reads the member without creating an instance; `%opaque` is allowed
   for members of a body (P9g, §4.3.4). **Approved.**

**Settled.**
- The note lives in `docs/design/proofs-level35.md`, linked from chapter 10 of the proofs note.
- The P9a stop-gap is merged: E0960 for an applied relation in a meta type, and E0961 for a judgment over
  a program with negation.
- Chapter 1 of the proofs note writes `{X := W}`.
- L17 (`programOf f : graph -> program`) stands as implemented.
- Diagnostics and hovers print the canonical `P ⊢ r t̄`.
- Rule names are unchanged; chapter 10.1's per-relation synonyms are dropped.
- The database of a coerced atom is P7c's omitted database (§2.4).
- Rejected: B (derived members) and C1 (a `%program` directive; its block form, for lemmas about library
  functors, is recorded as an option). D (abbreviations written by hand) stays possible.
- The batch order is §7.

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
- Abella: `examples/first-order/add.thm` (`Specification "add".`, `Theorem add_base : forall N, {nat N} ->
  {add N z N}.`), `src/prover.ml` (the specification as the first command), abella/abella 957bb74.
- Lean 4: `section`, `namespace` and `variable` (Lean 4 reference, "Sections and namespaces"); `mutual`
  blocks of inductives or of definitions.
- Agda: parameterised modules and module application (`doc/user-manual/language/module-system.lagda.rst`),
  interleaved `mutual` blocks (`mutual-recursion.lagda.rst`), agda/agda a3f41e8.
- Hugin incrementality: `docs/INCREMENTALITY.md`, `docs/design/incrementality-2.md` (§2, §4.1).
- Hugin decision L27 (no blessed names in judgments) and batch P7c, `fix/proofs-p7c-explicit-generalisation`.
- Hugin 1db9441: `core/elab/{Judgments,Universes,Bidirectional,Declarations}.scala` (`inferJudgment`,
  `generalisedBinders`, `inferU`, `check`), `stdlib/std/{semantics,strata,decide}.hgn`,
  `tests/run/p7b_{proof_a,proof_b,rules}.hgn`, `reference/src/{modules,meta/staging,meta/families,object/types,object/rules,std/semantics}.md`.
  The paths of the Lean, Rocq, Agda and Isabelle documents are given from the projects' layout at the
  commits that chapter 14 of the proofs note cites; this note did not re-read them.
