# Proving properties of Datalog programs in the meta language

Design note for [issue #186](https://github.com/k0uks1/hugin/issues/186): the meta level should state and
prove properties of object-level Datalog programs, such as "this derived relation is transitive" and
"this rewrite derives the same facts". Status: research, for the designer's approval; nothing is
implemented. Written against `ccr-48027e29-daam41` at 28dbcb1. No program in this note was compiled: the
task allowed no builds, and the only launcher on the machine predates the redesign. Statements about
today's behaviour are read from the reference, `docs/NOTES.md` and the sources, and are cited.

Revision history. The first review added chapter 1. The second review accepted these revisions: the
meta `int` becomes an inductive type, unbounded and native-accelerated (D8); `value` reuses the base
types (D4); `match` and `rewrite` move to right-hand sides (P3); and a comparison of with, match and
rewrite was added (4.2). The second review also asked whether a more principled design than a
per-relation `%semantics` directive exists. Chapter 8 surveys the alternatives. It recommends one
semantic judgment, `derives`, as an ordinary library family, with rule-name patterns as the only sugar.
Chapter 1, the plan and the decisions now follow that recommendation. The third review accepted it,
added the code bridge between `⇑A` and the reflective syntax (7.7, P7a), and asked whether a layered
modal foundation would fit better (chapter 9: not now, with the conditions under which it would).

Contents: 1 the end state (a tour and two complete proofs), 2 recommendations, 3 Hugin today, 4 gap
analysis, 5 logical consistency today, 6 prior art, 7 a meta-level semantics of Datalog programs
(with the code bridge, 7.7), 8 alternatives to `%semantics`, 9 is a (layered) modal foundation worth
it?, 10 worked examples against hand-written families, 11 batches, 12 decisions for the designer,
13 sources.

## 1. The end state: proving with Hugin

This chapter shows the language once batches P1–P8 (chapter 11) are in, and proves two properties end
to end, as a user would write them. Everything here is hypothetical syntax built on today's syntax from
`reference/src`: clauses, implicit binders `{x : A}`, records, `where` blocks, directives `%name …` and
reflection quotes `'( … )`. Places marked **(proposal)** are syntax the designer has not yet decided
(D11). Nothing in this chapter has been compiled; the programs were checked by hand against the rules
of chapters 3–9 and of the reference.

### 1.1 A tour of the additions

**Postulates, `--safe` and assumptions.** A constant without a value must say so. `--safe` rejects
it, and `%assumptions` lists what a definition rests on.

```hugin
plusComm : (m n : nat) -> eq (plus m n) (plus n m) = %postulate.   (* (proposal) marker *)
%assumptions sameFacts.
```

```text
$ hugin check --safe closure.hgn
error[E0925]: postulate `plusComm` is not allowed with --safe          (proposal: code and text)
$ hugin check closure.hgn
note: assumptions of `sameFacts`: none (no postulates)
```

A postulate is a marked axiom. A declaration without a marker that is not a family or a constructor
first draws a warning, then an error. → **P1**.

**`std/eq`.** The identity family and its library are written as ordinary clauses: J is dependent
matching on `refl`, with K (D9).

```hugin
%use "std/eq".
eq : {A : Type} -> A -> A -> Type.                 (* (proposal) an implicit binder in a family's type *)
refl : {A : Type} -> {x : A} -> eq x x.
sym : {A : Type} -> {x y : A} -> eq x y -> eq y x.
sym refl = refl.
trans : {A : Type} -> {x y z : A} -> eq x y -> eq y z -> eq x z.
trans refl Q = Q.
cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> eq x y -> eq (f x) (f y).
cong F refl = refl.
subst : {A : Type} -> {x y : A} -> (P : A -> Type) -> eq x y -> P x -> P y.
subst P refl H = H.
empty : Type.
unit : Type.  tt : unit.
either : Type -> Type -> Type.  left : A -> either A B.  right : B -> either A B.
iff : Type -> Type -> Type = [a] [b] { to : a -> b, from : b -> a }.
```

A user lemma about `std/nat`, whose `plus` recurses on its second argument:

```hugin
zeroPlus : (n : nat) -> eq (plus 0 n) n.
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
```

`plus 0 (N + 1)` evaluates to `suc (plus 0 N)` by the second clause of `plus`, so `cong suc (zeroPlus N)`
has the goal's type. The family is closed in `std/eq`, so no program can add a constructor. → **P2**.

**Explicit implicit arguments and implicit patterns.** An implicit argument can be given by name, and
a constructor's implicit argument can be bound in a pattern.

```hugin
three : eq (plus 0 3) 3 = zeroPlus 3.
viaTrans : eq (plus 0 (plus 0 3)) 3 = trans {y := plus 0 3} (zeroPlus (plus 0 3)) three.
vec : Type -> nat -> Type.
vnil : vec A 0.
vcons : A -> vec A N -> vec A (N + 1).
lengthOf : {A : Type} -> {n : nat} -> vec A n -> nat.
lengthOf {n := N} V = N.
tailLength : {A : Type} -> {n : nat} -> vec A n -> nat.
tailLength vnil = 0.
tailLength (vcons {N := K} X XS) = K.              (* binds the constructor's implicit N *)
```

The **(proposal)** spelling is `:=`: `{n = e}` would clash with a record value passed as an explicit
argument (reference `meta/records.md`, "Syntax"). → **P2**.

**Opaque theorems.** A theorem is checked once, never unfolded or evaluated afterwards, and not
reported as unused.

```hugin
%opaque sameFacts.      (* (proposal) a local directive, like %input *)
```

Opaque definitions keep compile time independent of proof size: NOTES "Glued evaluation" says a
definition's unfolded value is otherwise computed eagerly. They are also exempt from W0003. → **P2**.

**`match` and `rewrite` on the right-hand side.** `match` is a case expression. When the expected type
is known, it abstracts the scrutinee's occurrences in the goal, and it can name the equation.
`rewrite` changes the goal with an equation. Clause heads stay pure patterns.

```hugin
maxN : nat -> nat -> nat = [m] [n] if (less m n) n m.
maxIs : (m n : nat) -> either (eq (maxN m n) m) (eq (maxN m n) n).
maxIs M N = match less M N with                     (* (proposal) syntax *)
  | true => right refl
  | false => left refl.

below : (m n : nat) -> eq (less m n) true -> eq (maxN m n) n.
below M N H = match E : less M N with
  | true => refl
  | false => absurdBool (trans (sym E) H).         (* E : eq (less M N) false here *)

twice : (n : nat) -> eq (plus 0 (plus 0 n)) n.
twice N = rewrite zeroPlus N in zeroPlus N.          (* (proposal) syntax *)
```

Here `absurdBool : {A : Type} -> eq false true -> A` is the `std/eq` lemma with the single absurd
clause `absurdBool ().`. The goal of `maxIs M N` is normalised first, unfolding definitions such as
`maxN` but not functions by clauses: `either (eq (if (less M N) N M) M) (eq (if (less M N) N M) N)`.
Then `less M N` is abstracted. In the branch `true`, `if true N M` evaluates to `N`, so `right refl`
fits. `rewrite zeroPlus N in e` abstracts the occurrences of `plus 0 N` (the equation's left side) in
the goal, checks `e` against the goal with `N` in their place, and elaborates to
`subst ([y] eq (plus 0 y) N) (sym (zeroPlus N)) e`. Both desugar to a `where`-local function and
`subst` (4.2), add no core rule, and work in any meta code, not only in proofs. → **P3**.

**Integers.** The meta `int` becomes an inductive type, as Lean's `Int` is: unbounded, with native
arithmetic checked against its clauses, as #184 did for `nat`.

```hugin
int : Type.
ofNat : nat -> int.           (* 0, 1, 2, … *)
negSucc : nat -> int.         (* -1, -2, … *)
small : eq (2 + (-5)) (-3) = refl.           (* -3 is negSucc 2; native, one step *)
fits64 : int -> bool.                        (* within the object level's 64 bits *)
add64 : int -> int -> option int.            (* the object level's +: none if the sum does not fit *)
add64 A B = if (fits64 (A + B)) (some (A + B)) none.
```

The object level's 64-bit `int` stays. Persisting a meta `int` into object code checks the range;
whether that check is implicit (an error, as E0909 is for undefined arithmetic today) or an explicit
function is open sub-decision D8a. → **P4**.

**`decide`.** This is proof by evaluation. A boolean checker comes with a soundness lemma, and a closed
instance is proved by `tt`, because `so true` evaluates to `unit`.

```hugin
%use "std/decide".
so : bool -> Type.
so true = unit.
so false = empty.
lt : nat -> nat -> Type.
ltz : {n : nat} -> lt 0 (n + 1).
lts : {m n : nat} -> lt m n -> lt (m + 1) (n + 1).
lessSound : (m n : nat) -> so (less m n) -> lt m n.
lessSound M 0 ().
lessSound 0 (N + 1) T = ltz.
lessSound (M + 1) (N + 1) T = lts (lessSound M N T).
pair : Type = { fst : nat, snd : nat }.
decider : (A : Type) -> (A -> Type) -> Type = [a] [p] { check : a -> bool, sound : (x : a) -> so (check x) -> p x }.
decide : {A : Type} -> {P : A -> Type} -> (d : decider A P) -> (x : A) -> so (d.check x) -> P x =
  [d] [x] [t] d.sound x t.
ltDec : decider pair ([p] lt p.fst p.snd) = { check = [p] less p.fst p.snd, sound = [p] lessSound p.fst p.snd }.
big : lt 3 100000 = decide ltDec { fst = 3, snd = 100000 } tt.
```

`less 3 100000` takes one native step (reference `std/nat.md`), so `so (less 3 100000)` is `unit`.
`lessSound M 0 ()` is an absurd clause: `less M 0` evaluates to `false` by the first clause of `less`,
and `so false` is the empty type. → **P4**.

**The semantic judgment.** `std/semantics` defines one judgment for all programs: `derives p d a`, read
"program `p` derives the ground atom `a` from the input database `d`". It is an ordinary inductive
family over compiled programs (7.2); no per-relation declaration exists.

```hugin
%use "std/semantics".
value : Type.
vint : int -> value.  vfloat : float -> value.  vstr : string -> value.
vfact : sym -> list value -> value.          (* a fact's identity: its constant and its arguments *)
gatom : Type.
atom : sym -> list value -> gatom.
db : Type = gatom -> Type.
program : Type.                              (* compiled rules, input relations, strata *)
compile : module -> program.
derives : program -> db -> gatom -> Type.
monotone : {p : program} -> {d e : db} -> so (positive p) -> ((a : gatom) -> d a -> e a) ->
           {a : gatom} -> derives p d a -> derives p e a.
```

`value` reuses the base types and symbols (D4). `monotone` is proved in the library: a negation-free
program derives more facts from more input facts. → **P5** (positive Datalog∃!), **P6** (negation,
aggregates).

**Rule patterns.** For a *closed* program, a derivation is matched by the program's rule names. The
pattern `@step E P` stands for "rule `@step` fired, with premises `E` and `P`". The rule's variables
are bound by name with implicit patterns, and the same names build derivations.

```hugin
%use "std/semantics".
node : type.
edge : node -> node -> rel.
path : node -> node -> rel.
lin : module = '(
  @base path X Y :- edge X Y.
  @step path X Z :- edge X Y, path Y Z.
).
linP : program = compile lin.
pathAt : value -> value -> gatom = [x] [y] atom '(path) [x, y].
edgeAt : value -> value -> gatom = [x] [y] atom '(edge) [x, y].
firstHop : {d : db} -> {x z : value} -> derives linP d (pathAt x z) -> value.
firstHop (@base E) = z.
firstHop (@step {Y := W} E P) = W.
```

A rule pattern is resolved against the program in the scrutinee's type, which must evaluate to a
closed `program`. It elaborates to the general constructor `fire`, the rule's position in the program,
an instantiation vector of the rule's variables, the premises in body order and the head equation
(7.3). Branches whose head cannot unify with the goal atom are impossible: in `firstHop`, an `edge`
rule could not occur. `@input I` matches an input fact; it exists only for relations without rules in
the program (here `edge`), so `firstHop` needs no `@input` clause for `path`. The editor prints
`derives linP d (atom '(path) [x, z])` as `linP ⊢ path x z` **(proposal)**. → **P7b**.

**Programs of functors.** `body f` is the reified body of a functor, whose parameter relations are
input relations of the program.

```hugin
%use "std/graph".
tcP : program = compile (body tc).        (* (proposal) primitive; `g.edge` is an input relation *)
```

So a theorem about `tcP` holds for every graph a program passes to `tc`: the graph's edges are part of
the input database. → **P7a** (the code bridge, 7.7).

**One adequacy statement.** The link between the judgment and what a run prints is a single statement
about the compiler and the engine, the same for every program: for a program whose rules are the module
`m`, a run on the input facts `d` prints the fact `a` exactly when `derives (compile m) d a` holds. It
is trusted, written in the reference, and checked per run by `--certify`. → **P7b** (statement),
**P8b** (check).

**Derivations and certified runs.** `%derivations` exists today. P8 adds negative premises, an export
in a verified checker's format, and a run mode that checks the output against `derives`.

```hugin
%derivations areached.
```

```text
$ hugin run --export-proofs proofs.json europe.hgn        (proposal: flag; Tantow et al.'s JSON)
$ hugin run --certify --facts roads.facts europe.hgn       (proposal: flag and report)
areached de.
areached fr.
certified: 41 facts; 41 derivations checked by std/semantics.check (check.sound);
model check passed; 1 query, no answers
```

`--certify` replaces trust in the engine, for that run, by a check whose soundness is proven in
Hugin against `derives`. → **P8a** (export), **P8b** (`--certify`).

### 1.2 Proof A: an optimising rewrite derives exactly the same facts

**The program.** The linear closure is the specification. An optimiser replaces it by the non-linear
*doubling* rule, which needs logarithmically many rounds. The program runs the optimised rules, and the
specification is kept as data:

```hugin
%use "std/eq".
%use "std/semantics".

node : type.
edge : node -> node -> rel.
path : node -> node -> rel.
%input edge.

lin : module = '(                       (* the specification, not run *)
  @base path X Y :- edge X Y.
  @step path X Z :- edge X Y, path Y Z.
).
dbl : module = '(                       (* the optimised rules, run *)
  @base path X Y :- edge X Y.
  @join path X Z :- path X Y, path Y Z.
).
$dbl.
%output path.

linP : program = compile lin.
dblP : program = compile dbl.
pathAt : value -> value -> gatom = [x] [y] atom '(path) [x, y].
edgeAt : value -> value -> gatom = [x] [y] atom '(edge) [x, y].
```

Both quotes are typed where they are written (reference `reflection.md`, "Quotes"); only `dbl` is
reflected into the program.

**The statement.** For every input database, both programs derive the same `path` facts:

```hugin
sameFacts : {d : db} -> {x y : value} -> iff (derives linP d (pathAt x y)) (derives dblP d (pathAt x y)).
```

**The proof**, with every lemma:

```hugin
(* input edges are input edges in either program: `edge` has no rules in either *)
edgeIn : {d : db} -> {x y : value} -> derives linP d (edgeAt x y) -> derives dblP d (edgeAt x y).
edgeIn (@input I) = @input I.
edgeOut : {d : db} -> {x y : value} -> derives dblP d (edgeAt x y) -> derives linP d (edgeAt x y).
edgeOut (@input I) = @input I.

(* the linear closure is transitive *)
linTrans : {d : db} -> {x y z : value} ->
           derives linP d (pathAt x y) -> derives linP d (pathAt y z) -> derives linP d (pathAt x z).
linTrans (@base E) Q = @step E Q.
linTrans (@step E P) Q = @step E (linTrans P Q).

(* every linear derivation is a doubling one *)
toDbl : {d : db} -> {x y : value} -> derives linP d (pathAt x y) -> derives dblP d (pathAt x y).
toDbl (@base E) = @base (edgeIn E).
toDbl (@step E P) = @join (@base (edgeIn E)) (toDbl P).

(* every doubling derivation is a linear one *)
toLin : {d : db} -> {x y : value} -> derives dblP d (pathAt x y) -> derives linP d (pathAt x y).
toLin (@base E) = @base (edgeOut E).
toLin (@join P Q) = linTrans (toLin P) (toLin Q).

sameFacts : {d : db} -> {x y : value} -> iff (derives linP d (pathAt x y)) (derives dblP d (pathAt x y)) =
  { to = toDbl, from = toLin }.
%opaque sameFacts.
```

Each case, checked by hand:

- `edgeIn (@input I)`: `I : d (edgeAt x y)`. `edge` has no rule in `dblP`, so `@input I` builds the
  derivation; its hidden argument `so (edb dblP '(edge))` evaluates to `unit` and is filled by `tt`. No
  rule pattern applies to `edgeAt`, since every head of `linP` is `path`, whose symbol conflicts with
  `edge` in index unification (P2's symbol conflict rule).
- `linTrans (@base E) Q`: `@base` binds `X := x`, `Y := y`, and `E : derives linP d (edgeAt x y)`. Then
  `@step E Q` with `X := x`, `Y := y`, `Z := z` has type `derives linP d (pathAt x z)`.
- `linTrans (@step E P) Q`: `X := x`, `Z := y`, `E : … (edgeAt x Y)`, `P : … (pathAt Y y)`. The call
  `linTrans P Q : … (pathAt Y z)`, and `@step E (…) : … (pathAt x z)`.
- `toDbl (@step E P)`: `@base (edgeIn E) : derives dblP d (pathAt x Y)` and
  `toDbl P : derives dblP d (pathAt Y y)`, joined by `@join`.
- `toLin (@join P Q)`: `P : … (pathAt x Y)` and `Q : … (pathAt Y y)` in `dblP`, so `linTrans` joins
  their translations.
- No clause handles `@input` for `pathAt`: `path` has rules, so the hidden argument
  `so (edb linP '(path))` is `so false`, which is `empty`, and coverage refutes the case (reference
  `meta/coverage.md`, "Cases and probes").

**What the compiler checks.** Coverage over the cases that rule patterns produce: one per rule whose
head unifies with the goal atom, plus `@input` where the relation is an input. Termination: `P` and `Q`
are variables below the matched `fire` constructor (inside its premises), so they are subterms
(reference `meta/termination.md`). The types of every clause, which requires evaluating `compile lin`
to a closed program. And `--safe`: no postulates. A correct file prints nothing:

```text
$ hugin check --safe closure.hgn
$ hugin check closure.hgn --print-assumptions sameFacts
note: assumptions of `sameFacts`: none
```

**What the editor shows.** The user writes the statement and a hole, and asks the language server to
split `P`, as it does today for holes (reference `meta/functions.md`, "Typed holes"); for a derivation
over a closed program the split offers the rule patterns:

```hugin
toLin : {d : db} -> {x y : value} -> derives dblP d (pathAt x y) -> derives linP d (pathAt x y).
toLin P = ?.
```

The split produces `toLin (@base E) = ?.` and `toLin (@join P Q) = ?.`. Hovering over the second hole
shows the goal in E0924's format (`tests/neg/e0924_holes.check`), with the rule's unnamed variable `Y`
shown by its name in the rule:

```text
error[E0924]: unsolved goal `?`
  --> closure.hgn:46:20
   |
46 | toLin (@join P Q) = ?.
   |                     ^ goal: `linP ⊢ path x y`
   |
   = note: the hole stands for a meta value of type `linP ⊢ path x y`
   = note: in scope: `d : db`, `x : value`, `y : value`, `P : dblP ⊢ path x Y`, `Q : dblP ⊢ path Y y`
   = help: replace the hole with an expression of type `linP ⊢ path x y`
```

A mistake gives an ordinary type error. `toDbl (@step E P) = @join (toDbl P) (@base (edgeIn E)).` is
E0901: `@base (edgeIn E)` derives `path x Y` where `path y ?Z` is expected, and `x` is not `y`. A
recursive call that does not decrease, such as `toLin (@join P Q) = toLin (@join P Q)`, is E0912.

**The guarantee.** For every input of `edge`, the program prints exactly the `path` facts that the
linear specification derives.

| link | status |
|---|---|
| `sameFacts`: the two programs derive the same `path` facts from every input | checked by the meta level |
| `compile lin`, `compile dbl` are the rules of the quotes | checked: `compile` is meta code, evaluated |
| what the program runs is `dbl`, reflected by `$dbl.` | trusted: reflection and staging (compiler) |
| the run prints exactly what `derives dblP d` derives (one adequacy statement for all programs) | trusted, or checked for each run by `--certify` (P8b) |

**Bridges.** `iff`, `%opaque` and `--print-assumptions` → P1, P2. `derives`, `compile` → P5. Rule
patterns and `linP ⊢ …` display → P7b. `--certify` → P8b. The same proof against hand-written families
needs only today's language (chapter 10). Chapter 8 compares this formulation with `%semantics` and the
other alternatives.

### 1.3 Proof B: a program analysis over-approximates

**The program.** This is a classic of abstract interpretation: reachability on a *coarsened* graph.
Concrete nodes (cities) map to abstract nodes (countries) through the input relation `located`, and the
analysis computes the reachable countries. The property: every country of a reached city is reached
by the analysis. So a country the analysis reports as unreached contains no reached city, which is what
a user relies on when pruning by the analysis.

```hugin
%use "std/eq".
%use "std/semantics".

city : type. country : type.
berlin, paris, rome : city. de, fr, it : country.
road : city -> city -> rel.
start : city -> rel.
located : city -> country -> rel.
reached : city -> rel.
aedge : country -> country -> rel.
areached : country -> rel.
%input road. %input start. %input located.

coarse : module = '(
  @seed reached X :- start X.
  @step reached Y :- reached X, road X Y.
  @lift aedge A B :- road X Y, located X A, located Y B.
  @aseed areached A :- start X, located X A.
  @astep areached B :- areached A, aedge A B.
).
$coarse.
%output areached.
?- reached X, not located X _.         (* the hypothesis `placed` below: must have no answers *)

cP : program = compile coarse.
at1 : sym -> value -> gatom = [r] [x] atom r [x].
at2 : sym -> value -> value -> gatom = [r] [x] [y] atom r [x, y].
```

**The hypothesis.** Every reached city has a country. It is a property of the *input*, so it is a
hypothesis of the theorem:

```hugin
placed (d : db) : Type =
  (x : value) -> derives cP d (at1 '(reached) x) -> { a : value, ok : derives cP d (at2 '(located) x a) }.
```

**The statement and the proof**, complete:

```hugin
(* every country of a reached city is reached by the analysis *)
sound : {d : db} -> placed d -> {x a : value} ->
        derives cP d (at1 '(reached) x) -> derives cP d (at2 '(located) x a) -> derives cP d (at1 '(areached) a).
sound T (@seed S) H = @aseed S H.
sound T (@step {X := w} R E) H = @astep (sound T R (T w R).ok) (@lift E (T w R).ok H).

(* so a country reported unreached contains no reached city *)
safe : {d : db} -> placed d -> {x a : value} ->
       (derives cP d (at1 '(areached) a) -> empty) -> derives cP d (at2 '(located) x a) ->
       derives cP d (at1 '(reached) x) -> empty.
safe T N H R = N (sound T R H).
%opaque sound. %opaque safe.
```

Checked by hand, with the rule variables as the patterns bind them:

- `sound T (@seed S) H`: `@seed` binds `X := x`, so `S : cP ⊢ start x` and `H : cP ⊢ located x a`.
  `@aseed S H` with `A := a`, `X := x` derives `areached a`.
- `sound T (@step {X := w} R E) H`: `@step` binds `Y := x` and `X := w`, so `R : cP ⊢ reached w` and
  `E : cP ⊢ road w x`. `T w R : { a : value, ok : cP ⊢ located w a }`, so the recursive call
  `sound T R (T w R).ok : cP ⊢ areached (T w R).a`. Then `@lift E (T w R).ok H` (with `A := (T w R).a`,
  `B := a`, `X := w`, `Y := x`) derives `aedge (T w R).a a`, and `@astep` derives `areached a`.
- `safe T N H R`: `sound T R H : cP ⊢ areached a`, and `N` maps it to `empty`.

The implicit pattern `{X := w}` (P2) names the predecessor, which `T` needs. The converse of `sound`
is false (an abstract edge may combine two unrelated concrete edges), so the analysis is sound but not
complete, and no proof of the converse is attempted.

**What the compiler checks.** Coverage of `sound`: the rules with head `reached` (`@seed`, `@step`);
`reached` has rules, so there is no `@input` case. Termination: `R` is a premise below the matched rule.
The dependent record `{ a : value, ok : … }` (reference `meta/records.md`). `cP` evaluates to a closed
program.

**What the editor shows.** At `sound T (@step {X := w} R E) H = ?`, the goal is `cP ⊢ areached a`, with
`T : placed d`, `w : value`, `R : cP ⊢ reached w`, `E : cP ⊢ road w x` and `H : cP ⊢ located x a` in
scope. Writing `@astep ? ?` yields two goals, `cP ⊢ areached ?A` and `cP ⊢ aedge ?A a`; `?A` is solved
when the first is filled with `sound T R (T w R).ok`.

**The guarantee.** If the query has no answers in a run, every country of a reached city is printed
by `areached`, and a country that is not printed contains no reached city.

| link | status |
|---|---|
| `sound`, `safe` for every input database | checked by the meta level |
| `placed` holds for the run's input | the query has no answers; tied to `placed` by the adequacy statement (trusted) and the query semantics; `--certify` checks the empty answer with the certificate |
| `$coarse.` stages the rules of `coarse` | trusted (compiler) |
| the run prints exactly what `derives cP d` derives | trusted, or checked by `--certify` |

**Bridges.** `{X := w}`, `empty`, `%opaque` → P2. `derives` → P5. Rule patterns → P7b. `--certify`
and checked queries → P8b.

### 1.4 Where each piece comes from

| piece | batch | standalone |
|---|---|---|
| `= %postulate`, `--safe`, `%assumptions`, parameter promotion | P1 | yes |
| `std/eq`, `empty`/`unit`/`either`/`iff`, `{x := e}`, implicit patterns, `%opaque`, `decEq` | P2 | yes |
| `match … with`, `match H : … with`, `rewrite … in` | P3 | yes |
| inductive meta `int` with native arithmetic and comparisons; `std/decide` | P4 | yes |
| `std/semantics` (positive): `value`, `program`, `compile`, `derives`, `monotone` | P5 | partly |
| negation and aggregates in `derives` | P6 | no |
| `quote`/`unquote`, `quoteF`/`unquoteF`, `symOf`, `body f`, the missing syntax forms | P7a | yes |
| rule patterns `@r`, `@input`, `p ⊢ a` display, the adequacy statement in the reference | P7b | no |
| `--export-proofs` | P8a | yes |
| `--certify` | P8b | no |

## 2. Recommendations

1. **First make the logic honest (batch P1).** Today False takes three lines: any meta declaration that
   is not a family or a constructor is a *postulate* (reference `meta/index.md`, "Meta items"), and
   `boom : (A : Type) -> A.` is one. Postulates should need an explicit marker (`= %postulate`, by
   analogy with `= %builtin`), and a `--safe` mode should reject them. A command should list the
   assumptions a definition depends on (Lean's `#print axioms`, Rocq's `Print Assumptions`). Apart from
   postulates, this note found no way to derive False (chapter 5). One combination should still be
   closed before proofs matter: forced large indices together with recursion on forced arguments, which
   Agda forbids under `--safe` (Agda issue #6654).
2. **A small proof library and proof ergonomics (P2, P3).** This means a closed `std/eq` (`refl`, `sym`,
   `trans`, `cong`, `subst`, J by clauses, plus `empty`, `unit`, `either`, `iff`, `dec`). Also explicit
   implicit arguments `f {n := e}` and implicit patterns; *opaque theorems*, never unfolded or eagerly
   evaluated and exempt from W0003; and decidable equality of atoms with evidence. P3 adds the
   right-hand-side `match` (with an optional equation name) and `rewrite … in`. All of this is useful
   without the Datalog goal.
3. **An inductive meta `int` (P4).** It is defined the Lean way (`ofNat`, `negSucc`), unbounded, with
   native arithmetic checked against its clauses as #184 did for `nat`, plus comparison functions. The
   object level keeps 64 bits; the crossing checks the range (D8a). Object arithmetic in the semantics
   is `add64 : int -> int -> option int` and so on. P4 also adds `std/decide`.
4. **One semantic judgment (P5, P6).** `std/semantics` defines `derives : program -> db -> gatom ->
   Type` as an ordinary inductive family over compiled programs (rule variables as de Bruijn indices, an
   instantiation vector, head equations as arguments), closed under subfacts. Stratified negation and
   aggregates (P6) work stratum by stratum, as in Benzaken, Contejean and Dumbrava (ITP 2017). This is
   the specification, and generic theorems (monotonicity, correctness of module-wide directives) are
   stated over it.
5. **Rule patterns instead of `%semantics` (P7b), over a code bridge (P7a).** For a closed program, a derivation is matched and
   built by the program's rule names (`@step E P`), elaborated to the general constructor. This is
   Abella's `case` on a specification judgment (chapter 8), obtained with ordinary dependent matching.
   No per-relation families are generated, so there are no per-relation adequacy lemmas: one adequacy
   statement covers every program. P7a first makes `⇑A` and the reflective syntax interconvert
   (`quote`, `unquote`, with `unquote (quote c) ≡ c`; 7.7), and `body f` reifies a functor body. Chapter
   9 explains why this suffices, so that no modal foundation is needed. Example 1.2 proves an optimising
   rewrite correct, and 1.3 an analysis sound, in this style.
6. **The engine stays trusted, with a certificate mode (P8).** Verifying the Scala engine is out of
   reach. Hugin already emits derivation facts (`%derivations`). P8a exports them as Datalog proof
   trees in the JSON format of Tantow, Gerlach, Mennicke and Krötzsch (ITP 2025), whose Lean checker is
   verified. P8b adds `--certify`, which runs a meta-level checker, proven sound against `derives`, on
   the reified output: proof trees give soundness, and a one-round model check gives completeness.
7. **Not now:** a `Prop` universe or definitional proof irrelevance, tactics or meta-level elaborator
   reflection, a separate kernel, univalence, a layered modal foundation (chapter 9), and a core
   judgment former. Erasure comes for free: meta code never reaches the object program.

## 3. Hugin today

The meta level is "a total, dependently typed functional language: a two-level type theory" (reference
`meta/index.md`). As a proof language it has the following.

- **Universes.** There is a cumulative, predicative hierarchy `Type₀ : Type₁ : …`. Levels are inferred,
  are global to a program, and are not polymorphic. `Type : Type` is E0904 (reference
  `meta/universes.md`; `core/Levels.scala`). `type` is the universe of object types; it is first order,
  and `⇑type : Type₀` (NOTES "Decisions (B1)").
- **Π, implicit Π, records.** Records are dependent Σ types with eta, and functions have eta
  (`core/Unification.scala`, header comment). Lambdas are written `[x] e`. Implicit arguments are
  solved by pattern unification. They "cannot be written explicitly" and are not written in patterns;
  the names of a function's own implicit binders are in scope in its clauses (reference
  `meta/functions.md`, `meta/clauses.md`).
- **Inductive families.** Every argument is an index, and there are no parameters. Positivity is
  strict, including nesting through families that are positive in that argument. Implicit binders of
  a constructor that occur in its result type "do not count" for predicativity (reference
  `meta/families.md`; `core/elab/Inductives.scala`, `forcedBinders`). A family may have no
  constructors, which makes it an empty type. Its constructors are the declarations of the same file
  that return it, so a family is closed to other files.
- **Dependent pattern matching.** Clauses compile to case trees (Cockx and Abel 2018). Index
  unification is the full Cockx–Abel unifier *with* K: deletion, solution, injectivity, conflict and
  cycle, on constructors and literals only. Stuck equations are postponed, then reported as E0915.
  Absurd patterns `()` are allowed (`core/elab/SplitProblem.scala`, `IndexUnifier`; NOTES "Decisions
  (B2)").
- **Totality.** Coverage is checked over probes, with emptiness decided one level deep (reference
  `meta/coverage.md`). Termination uses the size-change principle over constructor subterms. Calls
  through definitions and record fields are followed; a function passed as a value is a call with
  unknown arguments (reference `meta/termination.md`; `core/elab/SizeChange.scala`). A cycle's bodies
  do not unfold until its termination check is done (reference `meta/index.md`, "Order of
  elaboration").
- **Equality.** There is no built-in identity type, but one can be declared as an ordinary family. The
  tests do so monomorphically (`eqn : nat -> nat -> Type. refl : eqn N N.`, for example in
  `tests/run/nat_offsets.hgn`), and coverage uses one to decide a split (reference `meta/coverage.md`,
  "Undecided splits"). The prelude's `same : A -> A -> bool` compares atoms (literals and symbols) and
  is stuck on everything else (`core/Primitives.scala`). It returns no evidence.
- **Numbers.** `nat` has numerals, offsets and native arithmetic that is checked against its clauses
  when `std/nat` is elaborated, as Agda does with its built-ins (reference `std/nat.md`, "Native
  arithmetic"). The meta `int` is 64-bit; its overflow is stuck, and the meta level has no comparison
  operators (reference `meta/functions.md`, "Literals and primitive operations").
- **Staging.** `⇑A` is opaque: it is spliced, never inspected (reference `meta/staging.md`). Module
  bodies are generative: there is one instance per evaluation site, and `Tm.Fresh` advances a hygiene
  counter. NOTES calls both "effects" of evaluation (NOTES "Glued evaluation").
- **Reflection.** Object syntax is available as data: `term`, `formula`, `rule`, `item` and `module`,
  with `'( … )` quotes, quoted patterns and `$m.` to reflect data back into the program (reference
  `reflection.md`). `quoted A` is a phantom-typed term whose constructor `qterm` is unchecked
  (NOTES "Typed object code (#56)"). A module-wide directive is a meta function `module -> module`
  over the file's rules (reference `directives.md`, "Module-wide directives"). There is no reflection
  of *meta* terms.
- **Holes.** `?` is an error (E0924), and the language server shows its goal and offers case splits
  (reference `meta/functions.md`, "Typed holes"). There are no unsolved-meta or incomplete-match escape
  hatches; `%partial` was removed in redesign A3 (NOTES "Termination").

So the meta level is intended to be MLTT with K, inductive families, cumulative predicative universes,
Σ and Π with eta, primitive base types and an opaque code type, plus postulates.

## 4. Gap analysis

### 4.1 Features

Sources: Agda a3f41e8 (manual `doc/user-manual/language/*.lagda.rst`, `src/full/Agda/...`), Lean 4
0bb12a8 (`src/...`) and Rocq 29f5238 (`doc/sphinx/...`, `theories/Corelib/...`).

| feature | Agda | Lean 4 | Rocq | Hugin today | needed for #186? |
|---|---|---|---|---|---|
| identity type and eliminator | `_≡_` in `src/data/lib/prim/Agda/Builtin/Equality.agda`; J by matching | `inductive Eq : α → α → Prop` (`src/Init/Prelude.lean`:73); `Eq.rec` | `Inductive eq` (`theories/Corelib/Init/Logic.v`:379); `eq_rect` | user-declared family; J by clauses | yes: P2 `std/eq` |
| K / UIP | on by default; `--without-K` (`without-k.lagda.rst`); unifier `TypeChecking/Rules/LHS/Unify.hs` | definitional proof irrelevance gives UIP | UIP not provable in general; an axiom (`Eqdep`) | K by the deletion rule (`SplitProblem.scala`) | keep K (D9) |
| Prop universe | `--prop` (`prop.lagda.rst`), matching only by `()` into `Set` | impredicative `Prop`; large elimination only for subsingletons (`src/kernel/inductive.cpp`, `elim_only_at_universe_zero`, :510) | `Prop`, `SProp` (`language/core/sorts.rst`; empty/singleton elimination, `language/core/inductive.rst`:1306) | none | no (D6) |
| proof irrelevance, erasure | `irrelevance.lagda.rst`; `@0` (`runtime-irrelevance.lagda.rst`) | `Prop` erased by the compiler; `lcProof` (`Prelude.lean`:242) | extraction erases `Prop` (`addendum/extraction.rst`) | the whole meta level is erased by staging | free; opaque theorems for compile time (P2) |
| induction principles | by matching; `TermCheck.hs` (`src/full/Agda/Termination/`) | generated recursors; structural or well-founded (`src/Lean/Elab/PreDefinition/{Structural,WF}`) | `Fixpoint`, generated `_rect`/`_ind` | by matching, size-change | enough; no infinitary (applied-subterm) recursion |
| inductive families as evidence | yes | yes | yes | yes (examples 1.2, 10.1) | already there |
| params vs indices | declared parameters; `--large-indices` off by default since 2.6.4 | declared, plus `inductive.autoPromoteIndices` (`src/Lean/Elab/MutualInductive.lean`:52, `fixedIndicesToParams`) | declared parameters | no parameters; forced implicit binders exempt from predicativity | P1 (D2) |
| `with` / `match` / rewrite | `with-abstraction.lagda.rst` (with, `with … in eq`, rewrite) | `match h : e with`, `rw`, `▸` | `destruct e eqn:H`, `rewrite` | `where`-local functions only; `subst` after P2 | P3 (4.2) |
| explicit implicits, implicit patterns | `{x = e}`, `{n}` | `(x := e)`, `@f` | `(x:=e)`, `@f` | no | P2 |
| tactics / elaborator reflection | `TC` monad, macros (`reflection.lagda.rst`) | tactic framework (`src/Lean/Elab/Tactic/*`: `simp`, `omega`, `grind`, `decide`) | Ltac, Ltac2 | reflection of object syntax only | no; proof by reflection (P4) |
| assumption tracking | `--safe` (`safe-agda.lagda.rst`) | `#print axioms` (`src/Lean/Elab/Print.lean`); `sorryAx` (`Prelude.lean`:794) | `Print Assumptions` | none: postulates are silent | P1 |
| partial definitions | `TERMINATING` pragma, not `--safe` | `partial def` is opaque, needs `Inhabited` (`src/Lean/Elab/PreDefinition/MkInhabitant.lean`) | none in the core | none (`%partial` removed) | already there |
| trusted arithmetic | built-in `Nat`, checked against its definition | kernel GMP acceleration (`src/kernel/type_checker.cpp`, `reduce_nat`, :668) | `Uint63`, `Float64` primitives | native `std/nat`, checked against its clauses | already there |
| integers | built-in `Int` (`pos`/`negsuc`) over built-in `Nat` | `inductive Int` (`ofNat`/`negSucc`) | binary `Z` | 64-bit base type; overflow stuck; no comparisons | P4 (4.3, D8) |
| small kernel | no (the type checker is the kernel) | yes | yes | no (the elaborator is the kernel) | no (D7) |
| two-level | `--two-level`, `SSet` (`two-level.lagda.rst`) | — | — | staging 2LTT, `⇑A` opaque | chapters 7, 8 |

What is missing for proofs, in order of need:

1. **Postulate hygiene** (P1). Agda's `--safe` refuses `postulate` ("can be used to assume any axiom",
   `safe-agda.lagda.rst`). In Hugin a typo can create a postulate: a declaration whose type does not end
   in a family of the same file is one.
2. **Equality and its library** (P2). The machinery for J is there; a closed library and a convention
   are not. Without universe polymorphism there is one `eq` per program, whose type argument lives at
   the maximal level used. Cumulativity and the forced-binder exemption keep `eq` itself in `Type₀`.
3. **Naming implicit arguments** (P2). Proofs often need an index (`{m}`, `{x}`), and today a clause can
   only use the names of its function's own implicit binders.
4. **Opaque theorems** (P2). NOTES "Glued evaluation" says the unfolded value of a definition is
   computed eagerly. A theorem should be checked and then never unfolded (Agda's `opaque`,
   `opaque-definitions.lagda.rst`; Lean's `theorem`). W0003 would also report every theorem that
   nothing refers to.
5. **Decidable equality with evidence** (P2). The semantics needs `(a b : sym) -> dec (eq a b)` and the
   same for literals. That requires a conflict rule for distinct symbols in index unification (literals
   have one already) and a primitive whose `no` branch is a checkable absurd function.
6. **A theory of integers** (P4). The meta `int` has no comparisons and a stuck overflow, so it cannot
   model the object level's 64-bit arithmetic in proofs. The accepted fix (D8) makes it an inductive
   type, as Lean's `Int` is, with native arithmetic checked against its clauses (4.3).
7. **`match`/rewrite** (P3) is convenience for proofs, and a missing case expression for all meta
   code. `subst` and a `where`-local helper (Agda's "inspect" idiom) express it today (4.2).
8. **Automation.** For closed, finite programs a checker `check : … -> bool` with a soundness lemma
   proves goals by `refl` (Rocq's ssreflect `reflect`, Lean's `decide`, `src/Lean/Elab/Tactic/Decide.lean`).
   This needs no tactic language (P4).

### 4.2 `with`, `match` and `rewrite`

| | Agda | Idris 2 | Lean 4 | Rocq | Hugin (P3, proposal) |
|---|---|---|---|---|---|
| abstract a term of the goal and split on it | `f x with e` and clauses `f x \| p = …` (clause heads) | `f x with (e)` and `\| p => …` | `match e with \| p => …` (right-hand side; generalises `e` in the goal) | `destruct e` (tactic) | `match e with \| p => …` (right-hand side) |
| keep the equation | `with e in eq` | `with (e) proof p` | `match h : e with` | `destruct e eqn:H` | `match H : e with` |
| rewrite the goal | `rewrite eq` (clause heads) | `rewrite eq in e` (right-hand side) | `rw [h]` (tactic), `h ▸ e` (term) | `rewrite H` (tactic) | `rewrite H in e` (right-hand side) |
| branch on a decidable proposition with its proof | `with` on `Dec` | `with` on `Dec` | `if h : c then … else …` (`dite`) | `destruct (dec c)` | `match H : c with` on a `bool` or `dec` |
| desugaring | an auxiliary with-function | an auxiliary function | a matcher with an inferred motive | an eliminator | a `where`-local function |

Sources: Agda `doc/user-manual/language/with-abstraction.lagda.rst` (`with … in eq`, :659–665);
Idris 2 1c630e6 `src/Idris/Doc/Keywords.idr` (`with` and `proof`, "withabstraction") and
`docs/source/tutorial/theorems.rst` (`rewrite … in`, :226); Lean 4 `src/Lean/Elab/Match.lean`
(`h :` discriminants, :62–69), `src/Lean/Elab/BuiltinNotation.lean` (`▸`, `elabSubst`, :457),
`src/Init/Prelude.lean` (`dite`, :1319), `src/Lean/Elab/Tactic/Rewrite.lean`; Rocq
`doc/sphinx/proofs/writing-proofs/reasoning-inductives.rst` (`destruct … eqn:`) and `equality.rst`.

Hugin follows Lean's right-hand-side `match` and Idris's right-hand-side `rewrite … in`, so clause
heads stay pure patterns and the clause checking of reference `meta/clauses.md` is unchanged. The
specification:

- **`match [H :] e with | p₁ => e₁ | … | pₙ => eₙ`** is an expression. If its expected type `G` is known,
  `G` and `e` are normalised, with definitions unfolded but functions by clauses applied only as far as
  evaluation takes them (the normal form that conversion uses, NOTES "Glued evaluation"). Every
  subterm of the normal form of `G` that is syntactically equal to the normal form of `e` (up to bound
  variable names) is abstracted to a fresh variable `y`, which gives the motive `[y] G'`. The types of
  the context's variables are not generalised; whether to offer `generalizing x` is part of D11. The
  match elaborates to a `where`-local function `m : (y : A) -> eq e y -> G'` with the clauses
  `m pᵢ H = eᵢ`, applied as `m e refl`. In branch `i`, `H : eq e pᵢ` when the equation is named. Coverage,
  unreachable branches and termination are those of the local function: calls through local functions
  are calls of those functions (reference `meta/termination.md`), and the enclosing clause's variables
  are passed with the relation "equal". Without an expected type, `match` is a plain case expression.
- **`rewrite H in e`**, with `H : eq a b` and expected type `G`, abstracts the occurrences of `a` in the
  normal form of `G` as above, giving `P = [y] G'`. It checks `e : P b` and elaborates to
  `subst P (sym H) e`. It is an error if `a` does not occur. `rewrite sym H in e` rewrites from right to
  left.

### 4.3 Integers

The accepted D8 replaces the 64-bit meta `int` with an inductive type. The other systems agree that
mathematical integers are inductive, with the bounded machine integers a separate type:

| | mathematical integers | acceleration | machine integers |
|---|---|---|---|
| Lean 4 | `inductive Int` with `ofNat : Nat → Int` and `negSucc : Nat → Int` (`src/Init/Data/Int/Basic.lean`:46–58) | compiled code calls GMP (`@[extern "lean_int_add"]`, :162). The kernel accelerates only `Nat` (`src/kernel/type_checker.cpp`, `g_nat_*`, `reduce_nat`), so `Int` reduces through the accelerated `Nat` operations | `Int64` and friends, separate structures (`src/Init/Data/SInt/Basic.lean`:65) |
| Agda | built-in `Int` with `pos`/`negsuc` (`src/data/lib/prim/Agda/Builtin/Int.agda`, `BUILTIN INTEGER`); stdlib notation `+_` and `-[1+_]` (`agda-stdlib/src/Data/Integer/Base.agda`) | arithmetic by clauses over the built-in, accelerated `ℕ` | `Word64` (`Agda/Builtin/Word.agda`, `Data/Word64`) |
| Rocq | binary `Z` over `positive` (`theories/Corelib/Numbers/BinNums.v`:68) | binary representation, no native step | primitive `Int63`/`Uint63` (`theories/Corelib/Numbers/Cyclic/Int63/PrimInt63.v`, `language/core/primitive.rst`) |

Correction to the brief: Lean's kernel acceleration covers `Nat`; its `Int` gains from it only through
`Nat`. Hugin can go further, as #184 did for `nat`: native operations on `int` numerals in one step,
checked against `int`'s clauses when the library is elaborated. The design for Hugin:

- `int : Type` with `ofNat : nat -> int` and `negSucc : nat -> int` in the prelude. A closed integer is
  represented as a number, which is not observable (as for numerals, reference `meta/families.md`).
  Integer literals, including negative ones, checked against `int` are these values.
- `+`, `-`, `*`, `/` on meta `int` are functions by clauses with native computation on numerals, checked
  against their equations. Comparison functions (`iless`, `ileq`, `iequal : int -> int -> bool`) give
  the meta level the comparisons it lacks today. `std/nat`'s `toInt` becomes total.
- The object level's `int` stays 64-bit. Persisting a meta `int` into object code checks the range.
  Whether that is implicit, with an error like today's E0909 for undefined arithmetic, or an explicit
  function is open sub-decision D8a. `fits64 : int -> bool` exists in either case.
- In the semantics, object arithmetic is `add64 : int -> int -> option int` and so on, `none` outside
  64 bits (7.2).

## 5. Logical consistency today

**Can False be proved now? Yes, by a postulate.** By reference `meta/index.md` ("Meta items") and
`meta/families.md` ("Syntax"), `boom` below is a postulate, since its type ends in a variable, not in a
family of the file. `empty` is a family without constructors, and `absurd : empty` type-checks. E0909
only fires if *object* code depends on a stuck value, and a proof never reaches object code.

```hugin
empty : Type.
boom : (A : Type) -> A.
absurd : empty = boom empty.
```

(`boom : empty.` would not do: it would declare a *constructor* of `empty`.) Lean has `sorryAx` and
Agda has `postulate`; the difference is that both mark and track them (`#print axioms`, `--safe`).

Apart from postulates, here is each hole the issue names.

| hole | today | verdict |
|---|---|---|
| type-in-type | E0904; universes checked as difference constraints (`core/Levels.scala`) | closed |
| `type : type` | the object universe classifies itself, but holds only first-order object types, with no Π and no meta types (NOTES "Decisions (B1)") | harmless: a set-theoretic model interprets `⇑A` as sets of object terms |
| `%partial`, `TERMINATING`, unsolved metas, incomplete matches | none: `%partial` removed, `?` is E0924, E0911 and E0912 are errors, and an item with an error fails the compilation | closed |
| unchecked escapes | `qterm` (unchecked phantom type of `quoted A`); `same`, `labels`, `derive`, `derived`, `qatom` reduce only on canonical arguments and are stuck otherwise (`core/Primitives.scala`) | not logical escapes, since they assert no equation. `quoted A` is not evidence that the term has type `A` |
| native arithmetic | `std/nat` is checked against its clauses when the library is elaborated; the meta `int` is Scala arithmetic | trusted code, as in Agda and Lean |
| coverage | probes; emptiness one level deep; an absurd pattern needs a conflict; undecided splits are errors | sound (it only rejects more) |
| index unification | constructors and literals only (`SplitProblem.scala`, lines 99–178). The rule that solves `c α = c Y` as `α := Y` for a stuck `c` belongs to elaboration's unifier (`meta/functions.md`), where it picks *a* solution; it does not belong to index unification | sound. K holds; UIP is consistent with MLTT |
| positivity | strict, nested through positive families (E0913) | closed |
| termination | size-change over constructor subterms; no applied-subterm rule; unknown calls through values | sound by Lee et al. 2001, modulo the next row |
| forced large indices and forced-argument recursion | forced implicit binders do not count for predicativity (`Inductives.scala`, `forcedBinders`). At a leaf, a variable that index unification solved inside a constructor term counts as a subterm (`SizeChange.scala`: "the clause's patterns, as terms of the leaf") | **to close (D2).** Agda calls this combination "known to be inconsistent" (`--large-indices`, `doc/user-manual/tools/command-line-options.rst`) |
| generativity | functor bodies create fresh constants per evaluation site; closed applications are memoised "since meta functions are total and have no effects" (`meta/clauses.md`) | not a source of False, but evaluation is not referentially transparent across items (D10) |
| 2LTT staging | `⇑A` has no eliminator into the meta level; quotes are syntax, not semantics | closed: the object level cannot feed facts into the meta logic |

**The forced-index row in detail.** Agda's counterexample (`test/Fail/Issue6654a.agda`) declares
`data Bad : ((P : Set) → P → P) → Set` with `b : (f : …) → Bad f`, and recurses with
`no-bad (b x) = no-bad (x _ bad)`. Two things make it go through. The forced argument `f` lives in
`Set₁` but is not counted, and Agda's termination checker counts `x _ bad`, an *applied* subterm, as
smaller than `b x`. In Hugin the exemption applies only to *implicit* forced binders:
`b : {f : (P : Type) -> P -> P} -> Bad f.` puts `Bad` in `Type₀`. The function `no-bad` can reach `f`
through its own implicit binder. But the size-change relation holds only for a *variable* below a
constructor (reference `meta/termination.md`), so `no-bad (F _ bad)` is an unknown call, E0912. The
note found no derivation of False. Still, Hugin has exactly the two features that Agda now refuses to
combine under `--safe`, and the argument for its safety rests on a missing termination rule (applied
subterms), which proofs over infinitely branching trees will one day want. D2 closes it as Lean does:
promote fixed indices to parameters and exempt only parameters.

**Trusted base.** Hugin has no kernel: the whole elaborator, the evaluator and native arithmetic are
trusted, as in Agda. That is acceptable while the goal is to catch mistakes rather than to certify for
third parties. A core re-checker is the long-term answer (D7).

## 6. Prior art

**Verified Datalog engines.**

- Benzaken, Contejean and Dumbrava, *Certifying Standard and Stratified Datalog Inference Engines in
  SSReflect*, ITP 2017 (LNCS 10499, 171–188), released as DatalogCert. The development formalises the
  model-theoretic and fixpoint semantics of Datalog and of its stratified extension, and implements
  them by bottom-up and stratified evaluation, with proofs of soundness, termination, completeness and
  model minimality. They chose bottom-up evaluation because loop-freedom of top-down or optimised
  strategies is harder to establish. The stratified engine reuses the standard one per stratum. This
  is the closest model for Hugin's semantics (7.2). Their engine *is* the proof object; Hugin's
  engine is not, so Hugin takes their semantics, not their architecture.
- Bonifati, Dumbrava and Gallego Arias, *Certified Graph View Maintenance with Regular Datalog*, TPLP
  18(3–4), 2018 (ICLP). Regular Datalog is a fragment with transitive closure as a primitive; an
  incremental engine is proven sound in Coq and extracted to OCaml.
- Bégay, Crégut and Monin, *Developing and Certifying Datalog Optimizations in Coq/MathComp*, CPP 2021.
  A static analysis and two program transformations are certified on top of the Coq/MathComp
  formalisation, with a new trace semantics. Their transformations are what Hugin's module-wide
  directives are; a "rewrite preserves the facts" theorem (1.2, 10.3) is the same kind of result.
- Schlichtkrull, Hansen and Nielson, AFP entry *Stratified Datalog* (2025; SAC 2024 paper
  *Isabelle-verified correctness of Datalog programs for program analysis*). It proves that every
  stratified program has a least solution, and proves five bit-vector analyses correct. These are
  proofs *about specific Datalog programs* against the least-solution semantics, which is exactly
  #186's goal, in Isabelle.
- Tantow, Gerlach, Mennicke and Krötzsch, *Verifying Datalog Reasoning with Lean*, ITP 2025 (LIPIcs
  352, 36). This is a Lean checker for Datalog proof trees and proof DAGs in a tool-independent JSON
  format. The model-theoretic and proof-theoretic semantics are proven equivalent
  (`modelAndProofTreeSemanticsEquivalent`), and a model checker (`checkPGR`) validates that a result is
  closed under the rules. Evaluated on traces of Nemo. This is the certificate route of 7.6.
- Shahin, *A Shallow Embedding of Datalog in Lean*, arXiv 2605.02113 (2026). Datalog relations map to
  native Lean inductive predicates, and backward-chaining queries become theorems proved by tactics.
  This is the inductive-predicate baseline of 8.2.

No Agda formalisation of Datalog semantics was found.

**Refinement-style verification.** Liquid Haskell's refinement reflection (Vazou et al., POPL 2018)
turns terminating functions into logic equations, with proofs as unit-returning functions and SMT
discharge. F* separates total, ghost and erased computation and has Meta-F* tactics. The lessons for
Hugin: proofs as ordinary total functions are enough for programs of this size; arithmetic wants a
decision procedure (here proof by reflection over `nat` and `int`, P4); and erasure must be guaranteed,
which staging already does.

**Two-level type theory.** Annenkov, Capriotti, Kraus and Sattler, *Two-level type theory and
applications* (MSCS 2023; arXiv 1705.03307): the outer level has a strict equality and reasons about
inner types through it. Agda implements this as `--two-level` with `SSet`, where UIP holds for the outer
equality even under `--without-K` (`two-level.lagda.rst`). Kovács, *Staged compilation with two-level
type theory* (ICFP 2022), on which Hugin's stage inference is built (NOTES "Architecture"), keeps
`⇑A` opaque so that staging is sound for every model of the object theory. Hence the meta level cannot
learn anything about object *semantics* from `⇑A`. Semantics has to enter as an explicit model inside the
meta level, as a judgment over reflected syntax connected to the object program by an adequacy
statement (chapter 8 surveys the alternatives, and Kovács's own §6 points the same way). This is
the main design consequence of the 2LTT literature for
#186. An outer equality on `⇑A` (Agda's `≡ˢ`) would give only *syntactic* equality of object code, which
is not the property users want.

**Provenance and monotonicity.** Soufflé's provenance evaluation (Zhao, Subotić and Scholz, TOPLAS 2020)
produces proof trees for derived facts; Hugin's `%derivations` does the same per rule (reference
`object/io.md`, "Derivation facts"). Datafun (Arntzenius and Krishnaswami, ICFP 2016) types
monotonicity; in Hugin, monotonicity of a negation-free program is a theorem of the deep semantics
(7.2), not a type discipline.

## 7. A meta-level semantics of Datalog programs

### 7.1 What has to be modelled

The object level is Datalog∃! with stratified negation, aggregates, 64-bit partial arithmetic,
floats, strings and bound columns (reference `object/index.md`). Its meaning is the iterated least
fixpoint, per component, of

```
IC_R(db) = db ∪ ⋃ { subfact(Head(R)[v/x]) | db ⊨ Body(R)[v/x] }
```

(REDESIGN §3.3). The identity of a fact is determined by its constant and its arguments (reference
`object/facts.md`), and bodies never create facts.

### 7.2 The judgment `derives` (`std/semantics`, P5–P6)

The semantics is a library over the reflective types, so that the reflected or reified program *is*
the object of proof.

```hugin
%use "std/reflect". %use "std/eq". %use "std/list".
value : Type.                          (* DL∃!'s values, over the existing base types (D4) *)
vint : int -> value.  vfloat : float -> value.  vstr : string -> value.
vfact : sym -> list value -> value.    (* the fact c v̄: identity = constant and arguments *)
gatom : Type.
atom : sym -> list value -> gatom.     (* an inductive, so index unification decomposes it *)
db : Type = gatom -> Type.             (* a set of facts, as a predicate *)

fin : nat -> Type.  fz : fin (N + 1).  fs : fin N -> fin (N + 1).
vec : Type -> nat -> Type.  vnil : vec A 0.  vcons : A -> vec A N -> vec A (N + 1).

cterm : nat -> Type.                   (* a term over n rule variables, de Bruijn *)
cvar : fin N -> cterm N.
cval : value -> cterm N.
capp : sym -> list (cterm N) -> cterm N.
carith : arith_op -> cterm N -> cterm N -> cterm N.
catom : nat -> Type.
cat : sym -> list (cterm N) -> catom N.
cbody : nat -> Type.
cpos : catom N -> cbody N.
cneg : catom N -> cbody N.             (* P6 *)
ccmp : cmp_op -> cterm N -> cterm N -> cbody N.
crule : Type = { name : string, arity : nat, head : catom arity, body : list (cbody arity) }.
program : Type = { rules : list crule, edb : sym -> bool, strata : list (list sym) }.
compile : module -> program.           (* names to indices; `edb r` iff no rule has head r *)
instAtom : {n : nat} -> vec value n -> catom n -> option gatom.   (* none: undefined arithmetic *)
```

The derivations of a positive program form two mutually inductive families:

```hugin
derives : program -> db -> gatom -> Type.
premises : program -> db -> {n : nat} -> vec value n -> list (cbody n) -> Type.
input : {p : program} -> {d : db} -> {r : sym} -> {vs : list value} ->
        so (p.edb r) -> d (atom r vs) -> derives p d (atom r vs).
fire  : {p : program} -> {d : db} -> {a : gatom} -> {c : crule} -> {xs : vec value c.arity} ->
        member c p.rules -> premises p d xs c.body -> eq (instAtom xs c.head) (some a) -> derives p d a.
sub   : {p : program} -> {d : db} -> {a : gatom} -> {s : sym} -> {vs : list value} ->
        derives p d a -> subfactOf (vfact s vs) a -> derives p d (atom s vs).
pnil  : {p : program} -> {d : db} -> {n : nat} -> {xs : vec value n} -> premises p d xs [].
ppos  : {p : program} -> {d : db} -> {n : nat} -> {xs : vec value n} -> {b : catom n} -> {g : gatom} ->
        {bs : list (cbody n)} -> eq (instAtom xs b) (some g) -> derives p d g -> premises p d xs bs ->
        premises p d xs (cpos b :: bs).
pcmp  : … -> holdsCmp o (inst xs t) (inst xs u) -> premises p d xs bs -> premises p d xs (ccmp o t u :: bs).
```

Three choices in this representation make rule patterns (7.3) work with ordinary dependent matching:

- **The goal atom is a variable index of `fire`, and the head is an equation argument.** An index
  `instAtom xs c.head` would be a stuck function application, which index unification postpones and
  then reports (reference `meta/coverage.md`, "Undecided splits"). This is the "green slime" problem.
  With the equation, matching `fire` always succeeds, and the head is unified only after `c` and `xs`
  are known.
- **Rule variables are de Bruijn indices into a vector `xs`.** Once `c` is a known rule, `c.arity` is a
  numeral, `xs` splits into named variables, and `instAtom xs c.head` evaluates to
  `some (atom '(path) [X, Z])`. Then `refl` unifies it with the goal atom.
- **`atom` is a constructor, and symbols get a conflict rule (P2).** A head with another relation is
  then refuted, not stuck.

`premises` with `derives` is a mutual pair of families; that Hugin's positivity check accepts mutual
families is a P5 prerequisite to confirm. The alternative, nesting through a list family, needs the
positivity check to accept a partially applied family as an argument. This is the proof-theoretic
least model (Tantow et al.'s proof trees). The model-theoretic one, "the least `db` closed under the
rules", follows as a theorem, as in their `modelAndProofTreeSemanticsEquivalent`.

- **Strata (P6).** For a stratified program, `derives p d` is defined by recursion over `p.strata`, a
  Type-valued recursion that Hugin allows (`sel : bool -> Type` in reference `meta/clauses.md`). Each
  stratum is a positive family as above, whose `cneg` premises read the model of the strata below. This
  is Benzaken et al.'s stratified engine. The stratification is the compiler's; the library states, but
  need not recompute, the side condition that `not` reads only lower strata.
- **Arithmetic.** It uses the inductive meta `int` (D8): `add64 : int -> int -> option int`, and `sub64`,
  `mul64`, `div64` likewise. `none` is the undefined case, matching "a formula that contains an
  undefined operation does not hold" (reference `object/arithmetic.md`). Floats stay uninterpreted:
  values compared for equality only.
- **Aggregates (P6).** `count`, `sum`, `min` and `max` need finite sets: the semantics takes a list of
  valuations, a proof that it has no duplicates, and a proof that it is complete for the body over the
  lower strata. That is heavy but standard. Bound columns (Limit Datalog with ±∞) come last and may
  stay out of scope.

Theorems this enables: monotonicity of negation-free programs in the input; correctness of
module-wide directives (`(m : module) -> iff (derives (compile m) d a) (derives (compile (dir m)) d a)`,
chapter 10.3); and "at most N facts" for programs with finite carriers, which needs a finite enumeration
of the model and is the most expensive.

### 7.3 Rule patterns (P7b)

For a closed program, the rule pattern `@r p₁ … pₖ` against `derives p d a` stands for

```
fire {c := cᵢ} {xs := [X₁, …, Xₙ]} (there^(i-1) here) (ppos refl p₁ (ppos refl p₂ … pnil)) refl
```

Here `cᵢ` is the rule named `@r` of `p` (and `i` its position), `X₁ … Xₙ` are the rule's variables,
bound as implicit patterns under the names they have in the rule, and `p₁ … pₖ` are the premises in
body order. A comparison in the body becomes a `pcmp` premise that is not written. As an expression,
`@r e₁ … eₖ` builds the same term: the variables are inferred, or given by `{X := e}`, and the
equations are `refl`. `@input I` stands for `input t I`, where `t` is the proof of `so (p.edb r)`;
it is `tt` when that evaluates to `unit`. The elaboration needs:

1. `p` in the scrutinee's type evaluates to a closed `program`: a quote, `compile` of a quote, or
   `compile (body f)`.
2. Rule names are unique in `p`. Unnamed rules cannot be matched by name (D11).
3. Coverage is the ordinary one over the generated patterns. The split on `member` enumerates the rules
   of the closed list. A rule whose head symbol differs from the goal atom's is refuted by the symbol
   conflict rule, and `@input` is refuted for a relation with rules, because `so false` is empty.
4. The editor and diagnostics print `derives p d (atom '(r) [v̄])` as `p ⊢ r v̄`, offer the rule
   patterns in case splits, and name hidden variables after the rule's variables.

Termination needs no change: a premise is a variable below the `fire` constructor in the matched
pattern, so it is a subterm. Rule patterns are pattern synonyms (Agda,
`doc/user-manual/language/pattern-synonyms.lagda.rst`) computed from a program value, not declared.
No family, constructor or lemma is generated.

### 7.4 Connecting reflection, semantics and the engine

The chain from a theorem to the facts that a run prints has three links.

1. **Theorem → `derives`.** This link is checked by the meta level, including `compile`, which is meta
   code.
2. **`derives` → staged program.** A program written as data (`m : module = '( … ). $m.`) is the
   shortest path, since theorems about `compile m` are about what is reflected. For hand-written rules,
   the module a module-wide directive receives is the same reification (reference `directives.md`), and
   `body f` reifies a functor body. The trusted steps are re-elaboration of reflected data, hygiene
   renaming, formula-function inlining and the Scala transforms (`obj/transform/{Disjunctions,Records}.scala`).
   The semantics models the source forms (`fdisj`, records as facts), so these transforms stay inside
   the trusted base.
3. **Staged program → output.** This is the engine: semi-naive evaluation in
   `runtime/{Engine,Evaluation}.scala`. The adequacy statement says that a run of the module `m` on the
   input facts `d` prints `a` iff `derives (compile m) d a`. It is one statement for all programs,
   written in the reference (P7b) and checked per run by `--certify` (P8b).

### 7.5 Trusted, verified or certified engine

| option | what it gives | cost | verdict |
|---|---|---|---|
| trusted | theorems hold of the reference semantics; the engine is tested against it | none | default |
| verified (Benzaken et al.) | the engine is the proof | the engine would have to be meta code or proven Scala: a rewrite, and orders of magnitude slower | rejected |
| meta-level reference engine | a naive `IC` fixpoint in Hugin, proven against `derives`, evaluated at compile time for closed programs | P5 plus about 400 lines of Hugin; feasible only for small programs | optional: differential testing of the engine |
| certificate per run (Tantow et al.) | soundness from proof trees (`%derivations` plus negative premises); completeness from a one-round model check | P8 | recommended as an opt-in mode |

### 7.6 Certificates (P8)

`%derivations` already gives, for each rule instance, the derived fact and its positive premises
(reference `object/io.md`). A certificate needs, in addition, the instances' negative premises and
aggregate witnesses, plus the input facts. With those, P8a exports the derivation facts as Tantow et
al.'s JSON proof DAG for the pure fragment, so that their verified Lean checker validates a run. That
is useful immediately for debugging and auditing, and needs no proofs in Hugin. P8b adds a post-run
phase (`--certify`): the driver reifies the input, the output and the derivations as meta data, and the
evaluator runs `check : program -> facts -> derivs -> bool`, proven in Hugin against `derives`:
`check … = true -> ∀ a ∈ out, derives … a`. A model check (`closed : program -> facts -> bool`, one
naive round) adds completeness, and negation then rests on checked lower strata. The meta evaluator is
slow on large outputs, so this is a CI and audit mode, not the default. Rule patterns change nothing
here: the certificate is about `derives`, the one judgment.

### 7.7 The code bridge: `quote` and `unquote` (P7a)

Hugin has two notions of object code: `⇑A`, staged and opaque (reference `meta/staging.md`), and the
reflective syntax (`term`, `quoted A`, `formula`, `module`), which programs can take apart (reference
`reflection.md`). The bridge makes the compiler guarantee that the two interconvert faithfully, so that
code written as ordinary object code can be the object of proof. For Hugin's first-order object
language this is Kovács's "analysable deep embedding" escape (ICFP 2022, §6); chapter 9 explains why
it is sound here.

**What exists today.**

| direction | today | reference |
|---|---|---|
| source syntax → data | `'( … )` quotes, typed where written; quoted patterns; `qvar` | `reflection.md`, "Quotes", "Quoted patterns", "Typed variables" |
| data → object code | at object positions, a `term`, `formula` or `quoted A` "stands for the term it describes", re-typed, closed data only (E0918); `$e.` reflects items | `reflection.md`, "Typed terms", "Reflecting data into the program" |
| shared data → both | `T.lift` (to `⇑`) and `T.reify` (to `term`) | `meta/families.md`, "Shared data" |
| `⇑A` → data | **missing**: "a quoted term is not object code `⇑A`", and a hole whose value is `⇑A` is E0901 | `reflection.md`, "Quotes" |
| data → `⇑A` as a meta value | **missing**: the conversion exists only at object positions, not as a meta function | same |
| `as`, ascription, projection, update | **missing** from the syntax: quoting them is E0917 | `reflection.md`, "Quotes" |
| a functor body as data | **missing** | — |

**Types.**

```hugin
quote    : {A : ⇑type} -> ⇑A -> quoted A.          (* terms *)
unquote  : {A : ⇑type} -> quoted A -> ⇑A.
quoteF   : ⇑prop -> formula.                       (* formulas, e.g. a formula function's result *)
unquoteF : formula -> ⇑prop.
symOf    : {R : Type} -> ⇑R -> sym.                (* relation code; R a relation type (proposal) *)
body f   : module                                  (* special form: f names a functor with a body *)
```

All of them are primitives in P7a. `body f` is a special form, not a function, since a functor is a meta
function and cannot be inspected. It reifies the body's rules, with the parameter relations as fresh
input symbols (one per parameter field), and is what `compile (body tc)` in chapter 1 uses.

**Equations.**

1. `quote` *computes* on canonical code, structurally: constants to symbols, literals to `tint`/`tstr`,
   applications to `tapp`, object arithmetic to `tarith`, aggregates to `fagg` with their bound variable
   as a `tbound` index, and so on through every `ObjForm` (`core/ObjForm.scala`). Positions (`Loc`) are
   dropped, as unification already looks through them. Rule-local variables named by hygiene
   (`Tm.Fresh`, `X#k`) are renamed canonically by first occurrence, so that `quote` does not depend on
   the hygiene counter. A persisted meta value quotes to its literal (`quote ⟨$k⟩ = qterm (tint k)`),
   and a lifted shared value to its reification (`quote (T.lift ℓ v) = T.reify … v`). These are
   definitional: they are how `quote` evaluates.
2. `quote` is *stuck* on neutral code: a variable of type `⇑A`, or a splice of a stuck meta application.
   It never decides anything about code it cannot see, which is what makes it stable under the
   substitutions Hugin performs (chapter 9).
3. `unquote (quote c) ≡ c` is **definitional**, for every `c`. For canonical `c` it follows by
   computation (up to positions and canonical names, which conversion ignores). For neutral `c` it is
   a conversion rule, like today's `$⟨t⟩ = t`.
4. `quote (unquote q) = q` holds only for well-typed data in canonical form, because `unquote` must
   type the data (as reflection does today: E0402, E0918), and `qterm` makes data without a check. It
   is **propositional**: a trusted lemma for data made by quotes (which are typed where written), listed
   by `--print-assumptions`, or D12's alternative, `unquote` taking typing evidence.

**Interaction with stage inference.** `quote` is never inserted implicitly: it is an intensional
operation, and a program should say where it inspects code. `unquote` generalises what object
positions already do with data, and is inserted where a `quoted A` is used as `⇑A`, which today is
E0901. A hole `$c` with `c : ⇑A` inside a reflection quote stops being E0901 and means `$(quote c)`.

**Interaction with monomorphisation and generativity.** Families are memoised meta functions from
object types to constants (reference `meta/staging.md`, "Instances"). `quote` of code that uses
`len` at `list int` yields the symbol of the instance `len[int]`, created on demand as staging would
create it. Code inside a functor body sees its parameter relations as neutral, so `quote` is stuck on
them, except under `body f`, which binds them to input symbols. Instances of generative modules quote to
their own symbols: two items that apply the same functor quote to two programs, as they stage to two.

**What proofs gain.** Programs no longer have to be written as quotes to be proved about. A functor
written as ordinary rules is `compile (body tc)`. A formula function's result is
`quoteF (cheap X)`, which a theorem can analyse, for example "reads only input relations". A meta
function that generates code (`gen : nat -> ⇑prop`) can be verified through `quoteF (gen n)`. And the
untyped `qterm` escape matters less, since typed code converts to typed data.

**Cost.** 900–1400 lines: `quote` over every object form, the missing syntax constructors (`as`,
ascription, projection, update), `body`, the cancellation rule, the canonical naming and tests. It fits
before rule patterns: P7a, then P7b.

## 8. Alternatives to `%semantics`

The previous version of this note had `%semantics r as fam (c₁, …)`, a per-relation directive that
generated a matchable inductive family with one constructor per rule, tied to the deep semantics by a
generated adequacy lemma per relation. The designer found it workable but "like a workaround", and
asked whether theory or prior art offers a more principled way for a meta level to reason about Horn
clause or Datalog programs. This chapter surveys the candidates and shows Proof A's key lemma,
transitivity, in each style.

### 8.1 What any answer must provide

Proof A needs four things:

1. A statement form: "program `P` derives `path x z` from input `d`".
2. An elimination principle, giving one case per rule whose head matches, with the rule's variables and
   premises.
3. Induction on derivations.
4. A link to what the engine prints.

The per-relation directive provides (2) by generating families, and pays for (4) with one adequacy
lemma per relation. The question is whether (2) can come from a single judgment, and (4) from a single
statement.

### 8.2 The baseline: inductive predicates, or judgments as types

Isabelle's `inductive`, Rocq's `Inductive … : Prop`, Lean's `inductive` and Twelf's LF signatures all
turn Horn clauses into an inductive predicate: one constructor per clause. That is "judgments as types"
(Harper, Honsell and Plotkin, JACM 1993; Pfenning and Schürmann, *System description: Twelf*, CADE
1999). Twelf checks meta-theorems as total relations; see the `%total` declarations in
`examples/tapl-ch13/theorems.elf` (twelf/twelf 4224d07). Shahin's Lean embedding of Datalog (2026) is
exactly this, and so are the hand-written families of chapter 10:

```hugin
lin : (m : graph.model) -> m.node -> m.node -> Type.
lin1 : {m : graph.model} -> {X Y : m.node} -> m.edge X Y -> lin m X Y.
lin2 : {m : graph.model} -> {X Z Y : m.node} -> m.edge X Y -> lin m Y Z -> lin m X Z.
linTrans (lin1 E) Q = lin2 E Q.
linTrans (lin2 E P) Q = lin2 E (linTrans P Q).
```

`%semantics` automated this encoding. Its weakness is not the encoding: in Twelf and λProlog the
clauses *are* the program, while in Hugin the family duplicates rules that also exist as object code.
Hence the generated adequacy lemma per relation, and generated names to learn.

- **Core change:** none, beyond generation.
- **Soundness:** that of inductive families.
- **Adequacy:** one lemma per relation.
- **Cost:** 1200–1800 lines (the old P7).

### 8.3 Abella's two-level logic approach

McDowell and Miller (*Reasoning with higher-order abstract syntax in a logical framework*, ToCL 3(1),
2002) and Gacek, Miller and Nadathur (*A two-level logic approach to reasoning about computations*,
JAR 49(2), 2012) separate a *specification logic*, hereditary Harrop formulas run as λProlog, from a
*reasoning logic* G, a first-order logic with inductive definitions, nominal ∇ and λ-terms (Baelde et
al., *Abella: A system for reasoning about relational specifications*, JFR 7(2), 2014). The
specification judgment `{L ⊢ A}` is one atom of G for all programs: `Obj` in `src/metaterm.ml`:53
(abella/abella 957bb74). The program is the `.mod` file, loaded by `Specification "add".` into the
prover's clause list (`src/prover.ml`:161). Three mechanisms do the work:

- `case H` on a hypothesis `{A}` *backchains*: it unifies `A` with the head of every program clause and
  produces one case per match, with the clause's body as new hypotheses (`src/tactics.ml`, `case`
  :450, its `focus`).
- `induction on 1` is induction on the height of the specification derivation.
- `search` builds derivations.

`examples/first-order/add.thm` proves commutativity of `add`, which is defined in `add.mod` by two
clauses, without any per-predicate encoding.

The match with Datalog is close but not exact. Datalog rules are Horn clauses: no `∀` or `⇒` in goals,
so Abella's dynamic context `L` serves only as the input facts, and nominal ∇ is never needed. Abella
needs a primitive judgment because G is a first-order logic without inductive families or dependent
matching. Hugin has both. So `{L ⊢ A}` is definable as an ordinary family, `derives p d a` (7.2), and
Abella's backchaining `case` is ordinary dependent matching on `fire`, once the program is closed and
the representation avoids stuck indices. Rule patterns (7.3) are the syntax for that case split.

Proof A, transitivity, written as a core primitive (an Abella-style judgment `derives` built into the
type theory, with `case` computed by unification against clause heads) looks the same as with the
library family:

```hugin
linTrans : {d : db} -> {x y z : value} -> derives linP d (pathAt x y) -> derives linP d (pathAt y z) -> derives linP d (pathAt x z).
linTrans (@base E) Q = @step E Q.
linTrans (@step E P) Q = @step E (linTrans P Q).
```

- **Core change, as a primitive:** a judgment former, its intro and elim rules, case trees over computed
  clause instances, coverage and termination for them, and a consistency argument for the extension.
  **As a library family:** none; P5 representation plus P7b sugar.
- **Soundness:** as a primitive, it must be argued, for example by a model in which `derives` is the
  inductive family. As a library, it is inherited.
- **Adequacy:** one statement for every program, in both cases.
- **Cost:** a primitive, 2000–3000 lines of core and a new proof obligation. A library, P5 (1500–2200,
  mostly Hugin) plus P7b (800–1200).

### 8.4 Beluga, contextual modal type theory and Mœbius

Beluga (Pientka and Dunfield, IJCAR 2010; Pientka, POPL 2008) programs and proves over LF objects in
contexts, `[Ψ ⊢ M]`, which are the types of contextual modal type theory (Nanevski, Pfenning and
Pientka, ToCL 9(3), 2008). Proofs are recursive functions that pattern-match on LF derivations.
Mœbius (Jang, Gélineau, Monnier and Pientka, POPL 2022) brings contextual types and pattern matching
on code to a System F metaprogramming language, with type refinement during matching. In Beluga
style, Proof A would read:

```text
rec trans : [⊢ path X Y] → [⊢ path Y Z] → [⊢ path X Z] =
  fn p ⇒ fn q ⇒ let [⊢ Q] = q in case p of
  | [⊢ base E]   ⇒ [⊢ step E Q]
  | [⊢ step E P] ⇒ let [⊢ R] = trans [⊢ P] [⊢ Q] in [⊢ step E R];
```

The relations are still LF type families declared per judgment, as in 8.2. What contextual types add
is principled handling of binders and contexts. Datalog has no binders apart from the variable an
aggregate binds (already locally nameless in `std/reflect`), so this machinery buys nothing here.

- **Core change:** contextual types and first-class substitutions.
- **Soundness:** studied.
- **Adequacy:** per family, as in 8.2.
- **Cost:** a new core (5000+ lines).

### 8.5 Layered modal type theory

Hu and Pientka, *Layered Modal Type Theory: Where Meta-programming Meets Intensional Analysis* (ESOP
2024, LNCS 14576), puts a modal layer with contextual `□` types over a simply typed core and allows
pattern matching on (open) layer-0 code, while keeping normalisation (by NbE over a presheaf model).
*A Dependent Type Theory for Meta-programming with Intensional Analysis* (POPL 2025, DeLaM, arXiv
2404.17065) scales this to dependent types for type-safe tactics. This is the principled answer to
"let the meta level inspect object code": `⇑A` would become matchable at a higher layer. For Hugin it
would replace the untyped reflective types (`term`, `formula`, `quoted A`) with typed, matchable code.
Proof A would match on the program's code rather than on reified data, but it would still need the
semantics, a `derives`, over that code. Layering answers how code is inspected, not what code means.

- **Core change:** layers in the core and a staging redesign.
- **Soundness:** proven for those calculi, not for Hugin's.
- **Adequacy:** it narrows link 2 of 7.4 (no reification), and links 1 and 3 remain.
- **Cost:** a redesign.

### 8.6 Two-level type theory and multimodal type theory

Annenkov, Capriotti, Kraus and Sattler (MSCS 2023) reason about inner types through the outer level's
strict equality. That gives syntactic equalities of inner terms, not the least-model meaning of a
Datalog relation. Kovács (ICFP 2022, §6 "Intensional analysis") discusses analysing values of `⇑A` and
finds a basic feature, decidable definitional equality of object terms, incompatible with the standard
presheaf model, because object-level inequality is not stable under substitution. He names three ways
out. One is "inductive deeply embedded syntaxes, which can be analyzed". The others are restricting to
weakenings, or a closed modality for closed object terms (Licata et al. 2018), with pattern matching
left as future work. Hugin's reflective types are such a deep embedding, of closed syntax: object
variables are data (`tvar "X"`). So 2LTT theory endorses exactly the route of 7.2: semantics over
reflected syntax, with `⇑A` left opaque. Multimodal type theory (Gratzer, Kavvos, Nuyts and Birkedal,
LICS 2020) could host `⇑` and further modalities; Kovács lists it as future work. No existing modal
system supplies a semantics modality for Horn clauses.

- **Core change:** none needed; MTT would be a redesign.
- **Soundness:** keeping `⇑A` opaque preserves 2LTT's conservativity argument.
- **Adequacy:** unchanged.

### 8.7 Other prior art

- **LPTP** (Stärk, *The theoretical foundations of LPTP (a logic program theorem prover)*, JLP 36,
  1998) proves properties of pure Prolog programs in the *inductive extension of the completion* of the
  program. Each predicate's induction schema is read off its clauses, with no per-predicate
  declaration. That is the same idea as Abella's backchaining case, for first-order Horn programs.
- **Refinement reflection** (Liquid Haskell, Vazou et al., POPL 2018) lifts a function into the logic
  through a per-function `reflect` annotation. So per-definition annotations are common in practice, but
  they reflect the definition itself, not a copy.
- **Datalog equivalence and containment.** Equivalence of Datalog programs is undecidable (Shmueli,
  JLP 1993). Uniform containment is decidable (Sagiv, *Optimizing Datalog programs*, 1988) and is the
  classic sufficient test for optimisations. It cannot replace proofs: `tc` and `tc2` are not uniformly
  equivalent, since with input `path` facts and no edges, only `tc2` closes them. A uniform-containment
  `decider` is a possible P4 extension. Constrained Horn clause solvers (Bjørner, Gurfinkel, McMillan and
  Rybalchenko, 2015) automate inductive invariants and are likewise an automation layer.
- **Hoare type theory and F*** address effectful programs; Datalog rules are pure logic, so only their
  erasure discipline is relevant, and staging already provides it.

### 8.8 Comparison

| approach | per-relation declarations | core change | adequacy | Proof A text | cost |
|---|---|---|---|---|---|
| `%semantics` (8.2, automated) | generated families | none | one lemma per relation | `lin1`/`lin2` | 1200–1800 |
| Abella-style primitive (8.3) | none | judgment former and elimination | one statement | `@base`/`@step` | 2000–3000 and a consistency argument |
| **library `derives` + rule patterns** (8.3, 7.2–7.3) | none | none (sugar only) | one statement | `@base`/`@step` | P5 + P7b, about 2300–3400 |
| Beluga / CMTT (8.4) | LF families | contextual types | per family | as 8.2 | 5000+ |
| layered modal (8.5) | none | layers, staging redesign | narrows link 2 | needs `derives` anyway | redesign |
| 2LTT / MTT (8.6) | — | none / redesign | — | — | — |

### 8.9 Recommendation: combine

Replace `%semantics` with a primitive judgment that the language does not need to make primitive.

1. **One judgment, as a library family.** `derives p d a` in `std/semantics` (P5–P6) is the two-level
   approach's specification judgment, defined in the reasoning logic. Hugin's inductive families and
   index unification make it definable, so it needs no core former, and its consistency is that of
   families.
2. **Abella's `case` as rule patterns.** For a closed program, `@r p̄` matches and builds derivations by
   rule name (P7b). This is sugar, elaborated to `fire`, and needs no generated declarations.
3. **One adequacy statement** for every program (7.4), checked per run by `--certify`.
4. **Optional naming** comes from the rule names `@r` that Hugin already has, not from a directive.

Two things are lost, and the note accepts both. First, typed abstract carriers: a functor's
`g.node` disappears, since nodes are `value`s and "for every graph" becomes "for every input database".
Second, matching on derivations of an abstract program (generic theorems use `fire` and `input` directly,
as in 10.3). The plan changes accordingly: P7 becomes the code bridge (P7a, 7.7) and rule patterns with
the `⊢` display and the adequacy statement (P7b), instead of derived families and per-relation lemmas
(chapter 11).

## 9. Is a (layered) modal foundation worth it?

The designer's question: Hugin has two notions of object code, `⇑A` (staged, opaque) and reflection (a
deep embedding that can be matched on). Layered modal type theory would unify them; is a modal
foundation therefore more fitting? This chapter answers it against the code bridge of 7.7.

### 9.1 What would be unified

| today | layered / contextual modal (one code type `□A`) |
|---|---|
| `⇑A`, written with inferred quotes `⟨t⟩` and splices `$e` (reference `meta/staging.md`) | `□A` with `box` and `letbox`/unbox, or a Fitch-style lock |
| `quoted A`, `term`, `formula`, `rule`, `item`, `module`, made by `'( … )` | `□A` again: a quote is a box |
| quoted patterns and holes `$X`, `$..Xs`, `$F[V]` | pattern matching on `□` code at a higher layer, with pattern variables for subterms |
| `$e.` (reflecting items), data at object positions | splicing code of item type |
| `T.lift` / `T.reify` for shared data | a lift into `□`, with matching replacing `reify` |
| `qterm` (unchecked), E0918 (data not closed) | gone: code is typed by construction, and open code carries its context |

The candidates:

- **Layered modal type theory** (Hu and Pientka, ESOP 2024): layer 0 is a core calculus, and layer 1
  adds contextual `□` types whose values can be pattern-matched while normalisation is preserved. The
  dependent version, DeLaM (POPL 2025), has three layers: static syntax, MLTT with computation, and
  meta-programming.
- **Contextual modal type theory** (Nanevski, Pfenning and Pientka 2008) and Beluga give `[Ψ ⊢ A]` with
  first-class contexts.
- **Mœbius** (POPL 2022) adds polymorphism over code with type refinement during matching.
- **Fitch-style and multimodal type theory** (Gratzer, Kavvos, Nuyts and Birkedal, LICS 2020) would make
  `⇑` one modality among several. Kovács notes that 2LTT is the degenerate case, with `⇑` as its only
  modality and no restriction on contexts (ICFP 2022, §8).

### 9.2 The core question: does first-order Datalog make the two coincide?

LMTT needs layers because matching on code conflicts with equality of code up to computation. If code
is identified up to β and η, a match can distinguish β-equal terms and break conversion. Layering
keeps the matched code at a layer where it is static syntax (Hu and Pientka 2024). Kovács (2022,
§6) states the same obstruction semantically. In the standard presheaf model, code is stable under
*substitution*, and even decidable equality of object terms is not, since unequal variables can be
mapped to equal terms. He also states the escape: if the object theory needs only *weakenings*, "a wide
range of intensional analysis features" are stable, at the price that the object theory then cannot
have dependent or polymorphic types.

Hugin's object level fits that escape. Where does its equality of code go beyond syntax?

| source | equality of object code | verdict |
|---|---|---|
| β, η | none: the object level has no lambdas or object functions (E0908); records and facts are data, and projections and updates are evaluated by the engine, not by conversion (`core/ObjForm.scala`: object code is "inert data for evaluation, unification and read-back") | no conflict |
| object-variable substitution | never at compile time: rule variables are instantiated only by the engine, at run time. Formula-function inlining is a *meta* β-step whose arguments are object terms | weakening only, Kovács's escape |
| meta computation inside splices | `⟨… $e …⟩` is equal up to conversion of `e`; `$⟨t⟩ = t`, `⟨$e⟩ = e` | `quote` acts on normal forms and is stuck on neutral `e` (7.7, equations 1–3) |
| persisted values | object arithmetic on two meta operands is computed at compile time; `T.lift` builds object terms from meta data | equations `quote ⟨$k⟩ = tint k`, `quote ∘ T.lift = T.reify` |
| positions | `Loc` is transparent to unification | `quote` drops positions |
| α | rule variables, hygiene names `X#k` (`Tm.Fresh`), the variable an aggregate binds | canonical names and `tbound` indices |
| functor application | generative instances: the same source code gives different constants in different items | an evaluation effect, not an equation; `quote` sees the instance's symbols |
| typed object code (#56) | `⇑` is covariant, and subtyping inserts nothing; unions and refinements are types, not terms | no term equations |
| `%open` types | constructors can be added in any file | no equation, but no closed "syntax of `A`" exists: matching on code of an open type needs a default case (as reflection over `sym` has today) |
| families (monomorphisation) | memoised by normalised type arguments | type arguments are meta; the object theory stays simply typed, as the weakening escape requires |
| stage polymorphism (`docs/design/stage-polymorphism.md`) | shared data exists at both stages, related by `lift` | structural |

So equality of object code in Hugin is syntactic, modulo α and modulo the meta level's own computation
inside splices. There is no object β or η, and no object-level substitution in conversion. The conflict
that LMTT's layers resolve therefore does not arise, and a `quote` that is a homomorphism stuck on
neutral code is sound in Kovács's weakening-only model. In practice the two approaches coincide:
matching on layer-0 code at layer 1 *is* `quote` followed by matching on the reflected data.

### 9.3 What a modal foundation would add, and what it would cost

**Gains over the bridge.**

- One code type instead of two, and one set of quote syntax.
- Typed matching on code with type refinement (Mœbius), instead of matching untyped data with a
  phantom index (`quoted A`). This removes `qterm`'s unchecked escape and the re-typing at reflection.
- Open code with explicit contexts (contextual types), instead of E0918's closedness rule and names
  as variables.
- `unquote` total by construction, with `quote (unquote q) = q` definitional.

**Costs.** The core, elaboration and inference would all change.

| part | what changes |
|---|---|
| core (`core/Syntax.scala`, `Value.scala`, NbE) | `□` types with contexts or layers, box and letbox or locks, pattern matching on code in case trees; `Obj` stops being inert |
| unification | higher-order pattern unification for contextual objects (Abel and Pientka, TLCA 2011, as Beluga does), pruning across layers |
| stage inference | Kovács's inference works because `⇑` imposes no context restriction (2022, §8). Boxes restrict contexts, and no published inference exists for layered or contextual boxes. Hugin's promise that "a program does not write these quotes" (reference `meta/index.md`) would be given up or would become research |
| monomorphisation and families | families as memoised meta functions from object types must be rephrased for layer-0 types; the `⇑type : Type₀` refinement (NOTES "Decisions (B1)") is re-proved |
| typed object code (#56) | the one checker over `ObjForm` (`core/objtype/*`) must run on contextual code; `⇑` covariance becomes modal subtyping |
| redesign B1–B3 | the staging handover (`core/handover/*`) reads normalised core terms with inert `Obj` nodes; it would be rebuilt |
| directives | generic directives over all relations (`%demand`) work on untyped `term`; they would need `Σ A. □A` or keep an untyped layer anyway |

### 9.4 Maturity

- **Beluga** is implemented (OCaml), with contextual types and higher-order pattern unification for them
  (Abel and Pientka, TLCA 2011).
- **Mœbius** (POPL 2022) is a calculus with an operational semantics and type preservation; no
  production implementation was found.
- **LMTT** (ESOP 2024): its NbE algorithm is mechanised and implemented in Agda.
- **DeLaM** (POPL 2025) is a theory for type-safe tactics; no production implementation was found.
- **mitten** (Stassen, Gratzer and Birkedal, TYPES 2022, LIPIcs 2023) is a prototype proof assistant for
  multimodal type theory, with NbE and bidirectional checking for any decidable preordered mode theory.
  Agda ships modalities (`doc/user-manual/language/flat.lagda.rst`) but no intensional analysis of code.
- **Stage inference** exists only for 2LTT's degenerate `⇑` (Kovács 2022), which Hugin implements.

None of these is a dependently typed language with inferred staging and pattern matching on code.

### 9.5 Recommendation

**Do not adopt a modal foundation now. Adopt the code bridge (7.7, P7a).**

For Hugin's object level, `quote`/`unquote` give the unification the designer is after: one direction
is a structural homomorphism, the round trip `unquote ∘ quote` is definitional, and the converse holds
for well-typed data. They give it at a fraction of the cost and without giving up stage inference. The
bridge is also forward-compatible: if a modal core comes later, `quoted A` becomes `□A`, `quote`
becomes the identity, and proofs over `derives` are unchanged.

The recommendation flips if any of these happens:

1. **The object level gains lambdas, higher-order rules or object functions.** Code equality then
   includes β/η, and matching needs layers (LMTT's original motivation).
2. **Conversion starts substituting object variables:** object-level `let`, inlining of rules by
   conversion, or polymorphic object types instantiated in the object theory. Kovács's weakening-only
   escape then no longer applies.
3. **Analysing open code becomes central**, such as meta functions that take rules apart under object
   binders, where E0918 and names as variables hurt. Contextual types then pay off.
4. **Hugin wants tactics over its own meta level.** Reflecting meta terms is DeLaM's motivation, and
   2LTT does not provide it.
5. **A mature implementation appears** that combines dependent types, inferred staging and modal pattern
   matching.

## 10. Worked examples against hand-written families

This chapter is the baseline of 8.2: proofs over families written by hand, in today's syntax. 10.1 and
10.2 use only features that exist today. They show that inductive families as evidence already work;
chapter 1 states the same theorems over `derives`, which ties them to the program. 10.3 is a generic
theorem over `derives` and needs P2 and P5.

### 10.1 Reachability is transitive

The rules of `tc` (`std/graph`: `path X Y :- g.edge X Y.` and `path X Z :- g.edge X Y, path Y Z.`) as a
family written by hand:

```hugin
model : Type = { node : Type, edge : node -> node -> Type }.   (* a model of `graph` *)

path : (m : model) -> m.node -> m.node -> Type.
step1 : {m : model} -> {x y : m.node} -> m.edge x y -> path m x y.
step2 : {m : model} -> {x y z : m.node} -> m.edge x y -> path m y z -> path m x z.

trans : {m : model} -> {x y z : m.node} -> path m x y -> path m y z -> path m x z.
trans (step1 E) Q = step2 E Q.
trans (step2 E P) Q = step2 E (trans P Q).
```

Coverage: the two constructors. Termination: `P` is a variable inside the constructor pattern
`step2 E P`. Universes: `model : Type₁`. `path` stays in `Type₀` only because `m`, `x` and `y` are
forced implicit binders, which is today's exemption. Under D2, `m` is a fixed first index promoted to a
parameter, so `path` still lives in `Type₀`.

The family is a copy of the rules. Nothing ties it to the relation that `tc g` computes, which is the
gap that `derives` (7.2) and rule patterns (7.3) close: in 1.2, `linTrans` is this proof, over the
program itself.

### 10.2 Two closure programs derive the same facts

The left-linear rule `path X Z :- path X Y, g.edge Y Z.` in place of the right-linear one:

```hugin
lpath : (m : model) -> m.node -> m.node -> Type.
lstep1 : {m : model} -> {x y : m.node} -> m.edge x y -> lpath m x y.
lstep2 : {m : model} -> {x y z : m.node} -> lpath m x y -> m.edge y z -> lpath m x z.

lcons : {m : model} -> {x y z : m.node} -> m.edge x y -> lpath m y z -> lpath m x z.
lcons E (lstep1 F) = lstep2 (lstep1 E) F.
lcons E (lstep2 P F) = lstep2 (lcons E P) F.

toL : {m : model} -> {x y : m.node} -> path m x y -> lpath m x y.
toL (step1 E) = lstep1 E.
toL (step2 E P) = lcons E (toL P).

toR : {m : model} -> {x y : m.node} -> lpath m x y -> path m x y.
toR (lstep1 E) = step1 E.
toR (lstep2 P F) = trans (toR P) (step1 F).

iff : Type -> Type -> Type = [a] [b] { to : a -> b, from : b -> a }.
sameFacts : {m : model} -> {x y : m.node} -> iff (path m x y) (lpath m x y) = { to = toL, from = toR }.
```

The same proof over `derives`, with `@`-patterns in place of the constructors, states that the two
programs derive the same facts from every input; 1.2 does this for the doubling rule.

### 10.3 A module-wide rewrite preserves the derived facts (generic)

A rewrite that reverses the body of every rule, of the kind a join-order optimiser would apply. On
compiled programs:

```hugin
%use "std/list". %use "std/eq". %use "std/semantics".
revC : crule -> crule = [c] (c with { body = reverse c.body }).
revP : program -> program = [p] (p with { rules = map revC p.rules }).

memberMap : {c : crule} -> {cs : list crule} -> member c cs -> member (revC c) (map revC cs).
memberMap here = here.
memberMap (there M) = there (memberMap M).

(* premises are order-independent; by induction on bs, with premSnoc *)
premRev : {q : program} -> {d : db} -> {n : nat} -> {xs : vec value n} -> {bs : list (cbody n)} ->
          premises q d xs bs -> premises q d xs (reverse bs).

sound : {p : program} -> {d : db} -> {a : gatom} -> derives p d a -> derives (revP p) d a.
premMap : {p : program} -> {d : db} -> {n : nat} -> {xs : vec value n} -> {bs : list (cbody n)} ->
          premises p d xs bs -> premises (revP p) d xs bs.
sound (input T I) = input T I.
sound (fire M Ps H) = fire (memberMap M) (premRev (premMap Ps)) H.
sound (sub D S) = sub (sound D) S.
premMap pnil = pnil.
premMap (ppos E D Ps) = ppos E (sound D) (premMap Ps).
premMap (pcmp C Ps) = pcmp C (premMap Ps).
```

A generic theorem cannot use rule patterns, since the program is abstract, so it matches `fire` and
`input` directly. Record updates make the cases go through without splitting the rule:

- `(revP p).edb` evaluates to `p.edb`, so `T` serves for both programs.
- `(revC c).arity` evaluates to `c.arity` and `(revC c).head` to `c.head`, so `xs` and the head
  equation `H` carry over.

`sound` and `premMap` are mutually recursive, and each call is on a subterm. `complete`, the converse,
is the same proof plus `reverse (reverse bs) = bs`, a `std/eq` lemma used with `rewrite … in`. The lemma
`compile (revBodies m) = revP (compile m)` connects the theorem to a module-wide directive
`revBodies : module -> module`; it is a statement about `compile`, proved by induction on the module.
Together, they make `%reorder` a *verified* directive: using it changes no fact.

## 11. Batches

Each batch is one PR. Line counts are rough (Scala plus Hugin library plus reference and tests).
"Standalone" marks batches that are useful even if the full goal is never reached.

| batch | content | lines | unlocks | risks | standalone |
|---|---|---|---|---|---|
| **P1** honest logic | `x : A = %postulate.`; an unmarked postulate is a warning, then an error (D1); `--safe`; `--print-assumptions` / `%assumptions f.` (postulates, trusted primitives); index promotion to parameters and forced-binder rule (D2); reference: a "Consistency" section | 500–800 | trustworthy proofs | migration of programs that rely on silent postulates; D2 may move a few families up a level | **yes**: catches typos that make postulates |
| **P2** proof basics | `std/eq` (J, `subst`, `cong`, `sym`, `trans`), `empty`, `unit`, `either`, `dec`, `iff`; explicit implicits `f {n := e}` and implicit patterns; `%opaque` theorems (no unfolding, no eager evaluation, W0003 exempt); `decEq` for atoms and the symbol conflict rule; polymorphic families confirmed | 900–1400 | all of chapter 1's lemmas | the spelling `{n := e}` (`{n = e}` clashes with a record value argument; reference `meta/records.md`, "Syntax") | **yes** |
| **P3** `match` and `rewrite` | right-hand-side `match e with \| p => e'`, `match H : e with` (abstraction in the goal after normalising with definitions unfolded; desugared to a `where`-local function); `rewrite H in e` via `subst` | 700–1000 | shorter proofs; case expressions in all meta code | which occurrences are abstracted (4.2); error messages for ill-typed abstractions (Agda's experience) | **yes**: Hugin has no case expression today |
| **P4** numbers and decision | inductive meta `int` (`ofNat`, `negSucc`), unbounded, native arithmetic checked against its clauses (#184's method), comparison functions, literals; the range check at the meta→object crossing (D8a); `std/decide` (`so`, `decider`, `decide`), `nat`/`int` lemmas | 1000–1500 | arithmetic in proofs; `add64` in the semantics; meta comparisons | migration of meta `int` code (overflow becomes a crossing error instead of a stuck value); performance of the native path | **yes** |
| **P5** `derives`, positive | `std/semantics`: `value`, `gatom`, `program`, `compile`, `derives`/`premises` with `fire`, `input`, `sub`; `add64` and friends; monotonicity; the model-theoretic equivalence | 1500–2200, mostly Hugin | generic theorems (9.3); the target of P7b and P8b | positivity of the mutual families; meta evaluation speed of `compile` | partly: a reference semantics in the language |
| **P6** negation and aggregates | strata, `cneg`, `count`/`sum`/`min`/`max` with finite witnesses; bound columns maybe later | 1000–1500 | full stratified Datalog∃! | aggregate proofs are heavy | no |
| **P7a** code bridge | `quote : ⇑A -> quoted A`, `unquote`, `quoteF`/`unquoteF`, `symOf`, `body f`; `unquote (quote c) ≡ c` as a conversion rule; canonical names; the missing syntax forms (`as`, ascription, projection, update); holes of type `⇑A` in quotes (7.7) | 900–1400 | programs written as ordinary object code (functors, formula functions, generators) as objects of proof | the converse round trip (D12); quote of open code under functor parameters | **yes**: typed code analysis for directives |
| **P7b** rule patterns | `@r p̄` and `@input` patterns and expressions over closed programs, elaborated to `fire`/`input` (7.3); case splits and `p ⊢ a` display in the editor; the adequacy statement in the reference | 800–1200 | chapter 1's proofs tied to the program | evaluation of `compile` during elaboration; name resolution of `@r` by the scrutinee's type | no |
| **P8a** proof-tree export | negative premises in `%derivations`; Tantow et al. JSON export | 300–500 | external verified checking of runs | format drift | **yes** |
| **P8b** certified runs | `--certify`: reified output checked by a meta checker proven against `derives` | 800–1200 | per-run guarantees without a verified engine | meta evaluator speed on large outputs | no |

Order: P1 → P2 → (P3, P4) → P5 → P7a → P7b → P6 → P8b. P8a can go at any time. Compared with the previous
version, P7 changes: instead of derived families and per-relation adequacy lemmas (1200–1800 lines and
a lemma generator), it adds the code bridge (P7a) and rule patterns with one adequacy statement (P7b; chapters 8, 9).

## 12. Decisions for the designer

D3 (as below), D4, D8 and the `match`/`rewrite` form are accepted. The others are open.

| | decision | options | recommendation |
|---|---|---|---|
| D1 | postulate syntax and policy | keep silent postulates; marker `= %postulate` with a warning; marker required (error) | marker, a warning for one release, then an error with a quick fix; `--safe` rejects marked ones too |
| D2 | forced large indices | keep; Agda 2.6.4 (count forced large binders); Lean (promote fixed indices to parameters, exempt only parameters); exclude forced large binders from size-change | Lean's promotion, which keeps `vec A`, `quoted A`, `eq` and 10.1 small, plus Agda's default for the rest |
| D3 | form of the semantics | per-relation families (`%semantics`); Abella-style core judgment; library judgment with rule patterns | **accepted:** library `derives` with rule patterns (chapter 8): no core former, no per-relation declarations, one adequacy statement |
| D4 | carrier of values | **accepted:** one universal `value` over the existing base types (`int`, `float`, `string`) and symbols for facts | `vint`, `vfloat`, `vstr`, `vfact`; no copies of base types |
| D5 | engine | trusted; verified; certificate | trusted by default, certificate mode (P8); no verified engine |
| D6 | `Prop`, irrelevance | add `Prop`/`SProp`; none | none for now; revisit if quotients or subset types with proof fields are needed |
| D7 | automation and kernel | tactics; meta reflection; proof by reflection; core re-checker | proof by reflection (P4) and the language server's goals; a core re-checker only if proofs must convince third parties |
| D8 | integers | **accepted:** the meta `int` is inductive (`ofNat`, `negSucc`), unbounded, native-accelerated with an equation check (#184); the object `int` stays 64-bit; semantics via `add64 : int -> int -> option int` | as accepted; see 4.3 |
| D8a | the meta→object crossing of `int` | implicit range check with an error (as E0909 for undefined arithmetic today); explicit function (`toInt64 : int -> option …`) | implicit check with an error, which matches today's rule for persisted values, plus `fits64 : int -> bool` for proofs and for code that wants to branch |
| D9 | K | keep; `--without-K` | keep: UIP is consistent, simplifies matching, and Hugin has no univalent ambitions |
| D10 | generativity | ignore; forbid functor instantiation in opaque theorems; theorems about programs only | theorems about programs (`compile`, `body f`), never about instances; audit whether memoised closed applications can share a module instance across items |
| D11 | syntax of the proof features | as proposed in chapter 1; alternatives per item | decide per batch: `= %postulate` (as `= %builtin`), `{x := e}` and `{X := p}`, `%opaque f.`, `match H : e with \| p => e'` and `rewrite H in e` on right-hand sides, `@r p̄` and `@input` (unnamed rules not matchable, or `@2` by position), `p ⊢ r v̄` in display, `body f`, the flags `--print-assumptions`, `--export-proofs`, `--certify` |
| D12 | the converse round trip `quote (unquote q) = q` | trusted lemma for data made by quotes, listed by `--print-assumptions`; `unquote` taking typing evidence; none | trusted, listed lemma: quotes are typed where written, and evidence would burden every use |
| D13 | a layered or contextual modal foundation (chapter 9) | adopt now; the code bridge now and revisit | the code bridge; revisit if the object level gains β (lambdas, higher-order rules), object-level substitution in conversion, or heavy open-code analysis, or if Hugin wants tactics over its own meta level |

## 13. Sources

- agda/agda a3f41e8: `doc/user-manual/language/{safe-agda,postulates,prop,irrelevance,runtime-irrelevance,with-abstraction,reflection,without-k,two-level,termination-checking,opaque-definitions}.lagda.rst`,
  `doc/user-manual/tools/command-line-options.rst` (`--large-indices`, `--forced-argument-recursion`),
  `src/data/lib/prim/Agda/Builtin/Equality.agda`, `src/full/Agda/TypeChecking/Rules/LHS/Unify.hs`,
  `src/full/Agda/TypeChecking/Forcing.hs`, `src/full/Agda/Termination/TermCheck.hs`,
  `test/Fail/Issue6654{a,b,c}.agda`,
  `src/data/lib/prim/Agda/Builtin/{Int,Word}.agda`, `doc/user-manual/language/pattern-synonyms.lagda.rst`;
  agda/agda-stdlib 2ffa8b7: `src/Data/Integer/Base.agda` (`+_`, `-[1+_]`), `src/Data/Word64/Base.agda`; issue agda/agda#6654, PR #6661, CHANGELOG 2.6.4.
- leanprover/lean4 0bb12a8: `src/Init/Data/Int/Basic.lean` (`inductive Int` :46, `ofNat` :52, `negSucc` :58,
  `lean_int_add` :162), `src/Init/Data/SInt/Basic.lean` (`Int64` :65), `src/Lean/Elab/Match.lean` (`h :`
  discriminants, :62–69), `src/Lean/Elab/BuiltinNotation.lean` (`▸`, `elabSubst` :457), `src/Init/Prelude.lean` (`Eq` :73, `lcProof` :242, `sorryAx` :794),
  `src/Init/Core.lean` (`propext` :1605), `src/kernel/inductive.cpp` (`elim_only_at_universe_zero`
  :510), `src/kernel/type_checker.cpp` (`reduce_nat` :668), `src/Lean/Elab/MutualInductive.lean`
  (`inductive.autoPromoteIndices` :52, `fixedIndicesToParams`), `src/Lean/Elab/PreDefinition/{Structural,WF,MkInhabitant}`,
  `src/Lean/Elab/Tactic/{Rewrite,Induction,Decide,Omega,Grind}.lean`, `src/Lean/Elab/Print.lean`.
- rocq-prover/rocq 29f5238: `doc/sphinx/language/core/{sorts,inductive}.rst`,
  `doc/sphinx/addendum/{sprop,extraction,rewrite-rules}.rst`,
  `doc/sphinx/proofs/writing-proofs/equality.rst`, `theories/Corelib/Init/Logic.v` (`eq` :379),
  `theories/Corelib/Numbers/BinNums.v` (`Z` :68), `theories/Corelib/Numbers/Cyclic/Int63/PrimInt63.v`,
  `doc/sphinx/language/core/primitive.rst`, `doc/sphinx/proofs/writing-proofs/reasoning-inductives.rst`
  (`destruct … eqn:`).
- idris-lang/Idris2 1c630e6: `src/Idris/Doc/Keywords.idr` (`with`, `proof`: withabstraction),
  `docs/source/tutorial/theorems.rst` (`rewrite … in`, :226), `docs/source/tutorial/views.rst`.
- abella/abella 957bb74: `src/metaterm.ml` (`Obj` :53), `src/tactics.ml` (`case` :450, `focus`),
  `src/prover.ml` (`clauses` :161), `examples/first-order/{add.mod,add.thm}`. twelf/twelf 4224d07:
  `examples/tapl-ch13/theorems.elf`.
- V. Benzaken, É. Contejean, S. Dumbrava: Certifying Standard and Stratified Datalog Inference Engines
  in SSReflect, ITP 2017, LNCS 10499, 171–188 (doi 10.1007/978-3-319-66107-0_12; HAL hal-01745566).
- A. Bonifati, S. Dumbrava, E. J. Gallego Arias: Certified Graph View Maintenance with Regular Datalog,
  TPLP 18(3–4), 2018 (arXiv 1804.10565).
- P.-L. Bégay, P. Crégut, J.-F. Monin: Developing and Certifying Datalog Optimizations in Coq/MathComp,
  CPP 2021.
- A. Schlichtkrull, R. R. Hansen, F. Nielson: Stratified Datalog, Archive of Formal Proofs, 2025
  (theories `Datalog`, `Bit_Vector_Framework`, `Reaching_Definitions`, …); SAC 2024.
- J. Tantow, L. Gerlach, S. Mennicke, M. Krötzsch: Verifying Datalog Reasoning with Lean, ITP 2025,
  LIPIcs 352, 36.
- R. Shahin: A Shallow Embedding of Datalog in Lean, arXiv 2605.02113.
- N. Vazou et al.: Refinement Reflection: Complete Verification with SMT, POPL 2018. F* and Meta-F*
  (Martínez et al., ESOP 2019).
- D. Annenkov, P. Capriotti, N. Kraus, C. Sattler: Two-level type theory and applications, MSCS 2023
  (arXiv 1705.03307). A. Kovács: Staged compilation with two-level type theory, ICFP 2022.
- D. Zhao, P. Subotić, B. Scholz: Debugging Large-scale Datalog: A Scalable Provenance Evaluation
  Strategy, TOPLAS 2020. M. Arntzenius, N. Krishnaswami: Datafun, ICFP 2016.
- R. McDowell, D. Miller: Reasoning with higher-order abstract syntax in a logical framework, ACM ToCL
  3(1), 2002. A. Gacek, D. Miller, G. Nadathur: A two-level logic approach to reasoning about
  computations, JAR 49(2), 2012. D. Baelde et al.: Abella: A system for reasoning about relational
  specifications, JFR 7(2), 2014.
- B. Pientka: A type-theoretic foundation for programming with higher-order abstract syntax and
  first-class substitutions, POPL 2008. B. Pientka, J. Dunfield: Beluga (system description), IJCAR
  2010. A. Nanevski, F. Pfenning, B. Pientka: Contextual modal type theory, ToCL 9(3), 2008.
- J. Jang, S. Gélineau, S. Monnier, B. Pientka: Mœbius: Metaprogramming using Contextual Types — The
  Stage Where System F Can Pattern Match on Itself, POPL 2022 (arXiv 2111.08099).
- J. Z. S. Hu, B. Pientka: Layered Modal Type Theory: Where Meta-programming Meets Intensional
  Analysis, ESOP 2024 (LNCS 14576); A Dependent Type Theory for Meta-programming with Intensional
  Analysis, POPL 2025 (arXiv 2404.17065).
- A. Kovács: Staged compilation with two-level type theory, ICFP 2022 (arXiv 2209.09729), §6
  "Intensional analysis" and §8. D. Gratzer, G. A. Kavvos, A. Nuyts, L. Birkedal: Multimodal dependent
  type theory, LICS 2020.
- A. Abel, B. Pientka: Higher-order dynamic pattern unification for dependent types and records, TLCA
  2011. P. Stassen, D. Gratzer, L. Birkedal: mitten: a flexible multimodal proof assistant, TYPES 2022
  (LIPIcs 269, 2023). Agda `doc/user-manual/language/flat.lagda.rst`. Hugin `core/ObjForm.scala`,
  `docs/design/stage-polymorphism.md`.
- R. Harper, F. Honsell, G. Plotkin: A framework for defining logics, JACM 40(1), 1993. F. Pfenning,
  C. Schürmann: System description: Twelf, CADE 1999.
- R. F. Stärk: The theoretical foundations of LPTP (a logic program theorem prover), JLP 36(3), 1998.
- O. Shmueli: Equivalence of DATALOG queries is undecidable, JLP 15(3), 1993. Y. Sagiv: Optimizing
  Datalog programs, in Foundations of Deductive Databases and Logic Programming, 1988. N. Bjørner,
  A. Gurfinkel, K. McMillan, A. Rybalchenko: Horn clause solvers for program verification, 2015.
- C. S. Lee, N. D. Jones, A. M. Ben-Amram: The size-change principle for program termination, POPL 2001.
  J. Cockx, A. Abel: Elaborating dependent (co)pattern matching, ICFP 2018.
- Hugin 28dbcb1: `reference/src/meta/{index,universes,families,clauses,coverage,termination,functions,staging,records}.md`,
  `reference/src/{reflection,directives}.md`, `reference/src/std/{nat,reflect}.md`,
  `reference/src/object/{index,facts,arithmetic,bound-columns,aggregates,io,termination}.md`;
  `core/elab/{SplitProblem,SizeChange,Inductives}.scala`, `core/{Primitives,Unification,NatArithmetic}.scala`,
  `src/main/resources/hugin/stdlib/{prelude.hgn,std/reflect.hgn,std/graph.hgn,std/directives.hgn,std/nat.hgn}`;
  `docs/NOTES.md` (Architecture, Decisions B1/B2, Typed object code, Glued evaluation, Approximate
  conversion); `docs/REDESIGN.md` §3.3, §6.3, §6.5.
