# Proving properties of Datalog programs in the meta language

Design note for [issue #186](https://github.com/k0uks1/hugin/issues/186): the meta level should state and
prove properties of object-level Datalog programs, such as "this derived relation is transitive" and
"this rewrite derives the same facts". Status: approved by the designer (rev. 2); implementation in
progress, P1 first. Written against `ccr-48027e29-daam41`. No program in this note was compiled; the
task allowed no builds. Statements about today's behaviour are read from the reference, `docs/NOTES.md` and the sources, and are cited.

Revision history. The first review added chapter 1. The second review accepted these revisions: an
inductive meta `int` (D8), base types reused in values (D4), right-hand-side `match` and `rewrite`
(P3). It also asked for alternatives to a per-relation `%semantics` directive, and chapter 8 recommends
one library judgment instead. The third review accepted that, added the code bridge (7.7), and asked
about a modal foundation (chapter 9: not now). The designer then approved the plan and every decision
(#190). In r2, the designer found chapter 1's examples too low-level: programs written as quotes, a
label on every rule, the run program spliced, and a confusing `compile`. The approved changes:

- programs and specifications are ordinary functors, modules and rules;
- `programOf` replaces `compile`;
- a judgment notation `P ⊢ r x y` with typed arguments;
- automatic rule names `path.1`, `path.2`;
- `decide` works with the notation;
- a new chapter on relations as propositions (levels 3.5 and 4), decided as D14: levels 1–3
  approved, level 3.5 designed after them (P9, design first), level 4 recorded, not planned.

Contents: 1 the end state (a tour and two complete proofs), 2 recommendations, 3 Hugin today, 4 gap
analysis, 5 logical consistency today, 6 prior art, 7 a meta-level semantics of Datalog programs,
8 alternatives to `%semantics`, 9 is a (layered) modal foundation worth it?, 10 relations as
propositions (levels 3.5 and 4), 11 worked examples against hand-written families, 12 batches,
13 decisions, 14 sources, 15 implementation decisions.

> **Syntax versus semantics, and why Lean doesn't need this.** Reflection gives a program as *data*:
> its rules, as the meta level can take them apart. `derives` gives its *meaning*: which facts the
> rules derive from which inputs. Lean proves things about Lean programs directly, because program and
> logic are one language: a Lean function *is* a term of the logic, and its equations are theorems.
> For a program in *another* language, a semantics is defined once inside the logic and the program is
> related to it: C in CompCert (Leroy, CACM 2009), Datalog in Tantow et al.'s Lean checker (ITP 2025).
> Hugin has both situations. Its meta functions are like Lean, since a meta function is a term of the
> meta logic and proofs about it need nothing new (P2, P3). Its Datalog is "the other language", run by
> a different engine with a least-fixpoint semantics. So Datalog needs a semantics in the meta logic,
> and it is defined once, in `std/semantics` (P5–P6). Users never write semantics. They write
> ordinary rules, and state theorems in the notation `tc ⊢ path x y`, which elaborates to that one
> judgment.

## 1. The end state: proving with Hugin

This chapter shows the language once batches P1–P8 (chapter 12) are in, and proves two properties end
to end, as a user would write them. Programs and specifications are ordinary functors and rules: no
quotes, no splices, no required labels. Everything is hypothetical syntax built on today's syntax from
`reference/src`. Places marked **(proposal)** follow D11, whose details are fixed in each batch.
Nothing in this chapter has been compiled; the programs were checked by hand against the rules of
chapters 3–9 and of the reference.

### 1.1 A tour of the additions

**No silent postulates; `%postulate`, `--safe` and assumptions.** A meta function declared without
clauses is a coverage error, exactly as if its clauses were missing. A deliberate axiom says so with
`= %postulate`, as a primitive says `= %builtin`. `--safe` rejects postulates, and `%assumptions` lists
what a definition rests on.

```hugin
boom : (A : Type) -> A.                                            (* now E0911 *)
plusComm : (m n : nat) -> m + n ≡ n + m = %postulate.
%assumptions sameFacts.
```

```text
$ hugin check closure.hgn
error[E0911]: missing cases in `boom`: `boom _`
note: assumptions of `sameFacts`: none (no postulates)
$ hugin check --safe closure.hgn
error[E0925]: postulate `plusComm` is not allowed with --safe          (proposal: code and text)
```

Only a function with an empty argument type may have no clauses, which coverage already accepts.
Abstract declarations in functor signatures and interface files are parameters, not postulates, and do
not change. → **P1**.

**`std/eq`.** The identity family and its library are written as ordinary clauses: J is dependent
matching on `refl`, with K (D9).

```hugin
%use "std/eq".
eq : {A : Type} -> A -> A -> Type.                 (* (proposal) an implicit binder in a family's type *)
%infix ≡ eq.                                       (* P2b: `x ≡ y` (ASCII `x == y`) is `eq x y` *)
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
zeroPlus : (n : nat) -> 0 + n ≡ n.                 (* `+` is `plus` of std/nat (P2b) *)
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
```

`plus 0 (N + 1)` evaluates to `suc (plus 0 N)` by the second clause of `plus`, so `cong suc (zeroPlus N)`
has the goal's type. The family is closed in `std/eq`, so no program can add a constructor. → **P2**.

**Explicit implicit arguments and implicit patterns.** An implicit argument can be given by name, and
a constructor's implicit argument can be bound in a pattern.

```hugin
three : plus 0 3 ≡ 3 = zeroPlus 3.                 (* `0 + 3` alone would add integers *)
viaTrans : plus 0 (plus 0 3) ≡ 3 = trans {y := plus 0 3} (zeroPlus (plus 0 3)) three.
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
maxIs : (m n : nat) -> either (maxN m n ≡ m) (maxN m n ≡ n).
maxIs M N = match less M N with                     (* (proposal) syntax *)
  | true => right refl
  | false => left refl.

below : (m n : nat) -> less m n ≡ true -> maxN m n ≡ n.
below M N H = match E : less M N with
  | true => refl
  | false => absurdBool (trans (sym E) H).         (* E : less M N ≡ false here *)

twice : (n : nat) -> 0 + (0 + n) ≡ n.
twice N = rewrite zeroPlus N in zeroPlus N.          (* (proposal) syntax *)
```

Here `absurdBool : {A : Type} -> false ≡ true -> A` is the `std/eq` lemma with the single absurd
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
small : 2 + (-5) ≡ -3 = refl.                (* -3 is negSucc 2; native, one step *)
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

**The judgment notation.** `P ⊢ r t̄` (ASCII `|-`) states that the program `P` derives the fact
`r t̄`. `P` is a functor, a module, or a functor applied to arguments. The atom is written in object
syntax. Its arguments are checked against the relation's declared column types, so statements range
over typed nodes.

```hugin
%use "std/graph".            (* tc: path X Y :- g.edge X Y.   path X Z :- g.edge X Y, path Y Z. *)
%use "std/semantics".
oneStep : {x y : g.node} -> tc ⊢ g.edge x y -> tc ⊢ path x y.      (* (proposal) syntax *)
oneStep E = path.1 E.
```

The statement says: in the transitive closure of any graph `g`, from any input, an edge from `x` to `y`
gives a path. It elaborates to

```hugin
oneStep : {d : db} -> {g : graph} -> {x y : ⇑g.node} ->
          derives (programOf (tc g)) d (atom (arg "edge") [v x, v y]) ->
          derives (programOf (tc g)) d (atom (own 0) [v x, v y]).
```

- The functor `tc`'s parameter `g` and the input database `d` are *generalised*: they become implicit
  binders of the declaration. This is how free uppercase variables already become implicit binders
  (reference `meta/functions.md`), and how Agda's `variable` and Lean's auto-bound implicits work. The
  binders are shared by all judgments of the declaration, and `⊢[e]` gives a database explicitly.
- `x y : g.node` is object code of type `g.node`, so `x` and `y` are typed nodes, abstract in `g`.
- `v` injects object code into the semantics' values (7.2).
- `arg "edge"` and `own 0` are program-relative references to relations (7.2).

→ **P7b** (notation), **P5** (`derives`).

**`programOf`.** The explicit form reifies a functor, a module or the current file's rules as written.

```hugin
tcP : program = programOf tc.
fileP : program = programOf here.              (* (proposal) `here`: this file's object rules *)
```

`programOf` is a meta function that produces `std/semantics`'s `program` value: names resolved to
relation references, rules numbered, variables typed, inputs and strata computed. It generates no code.
The notation inserts it wherever a functor or module stands before `⊢`. It is built on the code bridge
between `⇑A` and the reflective syntax (7.7). → **P7a**.

**Automatic rule names and case analysis.** The rules of a relation `r` are `r.1`, `r.2`, … in the
order they are written, like Isabelle's `tc.intros(1)`. The name `given` is for facts of the input
database. A rule name is both a pattern on derivations and a way to build them. Its premises are the
rule's body atoms in order, and the rule's variables can be bound by name. An optional label
(`@step path X Z :- …`) adds a second name; labels are never required.

```hugin
firstHop : {x z : g.node} -> tc ⊢ path x z -> g.node.
firstHop (path.1 E) = z.
firstHop (path.2 {Y := w} E P) = w.            (* w : ⇑g.node, typed by the rule *)
```

In the editor, splitting a hypothesis `P : tc ⊢ path x z` offers exactly the rules whose head can match:
`path.1` and `path.2`, but not `given`, since `path` has rules, and no rule of another relation. This
is Abella's `case`, with the rule's variables bound. Hovers show goals in `⊢` notation. → **P7b**.

**`decide` with the notation.** For a finite program whose inputs are facts in the file, a judgment
is proved by evaluation.

```hugin
city : type. berlin, paris, rome : city.
demo : city -> city -> rel.
demo berlin paris. demo paris rome.
tiny = tc { node = city, edge = demo }.
viaParis : here ⊢ tiny.path berlin rome = decide 3 tt.
```

`decide n` is `std/semantics`'s lemma `so (holds n p a) -> p ⊢ a`. It is valid for any database when
`p` has no input relations, and `holds n` is `n` rounds of naive evaluation. Here three rounds derive
`tiny.path berlin rome`, `holds` evaluates to `true`, and `so true` is `unit`. → **P4** (`so`,
`decide`), **P5** (`holds` and its soundness), **P7b** (the notation).

**One adequacy statement.** For every module `m` of a program and every run on the input facts `d`,
the run prints `m.r t̄` exactly when `m ⊢[d] r t̄`. This is one statement for all programs and
relations, trusted, written in the reference, and checked per run by `--certify`. A theorem about a
functor applies to each of its instances: `programOf (tc2 roads)` is the program of the instance
`tc2 roads`, found through the origin that a functor application records (NOTES, "Modules are
generative records"). → **P7b** (statement), **P8b** (check).

**Derivations and certified runs.** `%derivations` exists today. P8 adds negative premises, an export
in a verified checker's format, and a run mode that checks the output against `derives`.

```text
$ hugin run --export-proofs proofs.json europe.hgn        (proposal: flag; Tantow et al.'s JSON)
$ hugin run --certify --facts roads.facts europe.hgn       (proposal: flag and report)
eu.areached de.
eu.areached fr.
certified: 41 facts; 41 derivations checked by std/semantics.check (check.sound);
model check passed; 1 query, no answers
```

→ **P8a** (export), **P8b** (`--certify`).

### 1.2 Proof A: an optimising rewrite derives exactly the same facts

**The program.** The specification is the standard library's transitive closure `tc`, unchanged. The
program runs an optimised variant, `tc2`, with the non-linear *doubling* rule, which needs
logarithmically many rounds. Both are ordinary functors:

```hugin
%use "std/graph".
%use "std/eq".
%use "std/semantics".

tc2 (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- path X Y, path Y Z.
}.

city : type. berlin, paris, rome : city.
road : city -> city -> rel.
%input road.
fast = tc2 { node = city, edge = road }.
%output fast.path.
```

`tc`'s rules are `path.1` (`path X Y :- g.edge X Y`) and `path.2` (`path X Z :- g.edge X Y, path Y Z`).
`tc2`'s are `path.1` (the same base rule) and `path.2` (`path X Z :- path X Y, path Y Z`).

**The statement.** For every graph and every input, `tc` and `tc2` derive the same paths:

```hugin
sameFacts : {x y : g.node} -> iff (tc ⊢ path x y) (tc2 ⊢ path x y).
```

Both functors name their parameter `g`, of signature `graph`, so generalisation gives one `{g : graph}`
(and one `{d : db}`). Their parameter relation `g.edge` is the same reference, `arg "edge"`, in both
programs, so both read the same input edges.

**The proof**, with every lemma:

```hugin
(* an input edge is an input edge in either program *)
edgeIn : {x y : g.node} -> tc ⊢ g.edge x y -> tc2 ⊢ g.edge x y.
edgeIn (given I) = given I.
edgeOut : {x y : g.node} -> tc2 ⊢ g.edge x y -> tc ⊢ g.edge x y.
edgeOut (given I) = given I.

(* tc's paths are transitive *)
tcTrans : {x y z : g.node} -> tc ⊢ path x y -> tc ⊢ path y z -> tc ⊢ path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

(* every derivation in tc is one in tc2 *)
toTc2 : {x y : g.node} -> tc ⊢ path x y -> tc2 ⊢ path x y.
toTc2 (path.1 E) = path.1 (edgeIn E).
toTc2 (path.2 E P) = path.2 (path.1 (edgeIn E)) (toTc2 P).

(* every derivation in tc2 is one in tc *)
toTc : {x y : g.node} -> tc2 ⊢ path x y -> tc ⊢ path x y.
toTc (path.1 E) = path.1 (edgeOut E).
toTc (path.2 P Q) = tcTrans (toTc P) (toTc Q).

sameFacts : {x y : g.node} -> iff (tc ⊢ path x y) (tc2 ⊢ path x y) = { to = toTc2, from = toTc }.
%opaque sameFacts.
```

Each case, checked by hand. Rule variables are bound by unifying the rule's head with the goal atom.

- `edgeIn (given I)`: `I : d (atom (arg "edge") [v x, v y])`. `g.edge` has no rules in either program,
  so `given` is its only case, and `given I` builds the derivation in `tc2`. Its hidden argument says
  that `arg "edge"` is an input of `programOf (tc2 g)`; that evaluates to `unit` and is filled by `tt`.
- `tcTrans (path.1 E) Q`: `path.1` binds `X := x` and `Y := y`, so `E : tc ⊢ g.edge x y`.
  `path.2 E Q`, with `X := x`, `Y := y`, `Z := z`, derives `path x z`.
- `tcTrans (path.2 E P) Q`: `X := x`, `Z := y`, and `Y` is a fresh node `Y : g.node`.
  `E : tc ⊢ g.edge x Y` and `P : tc ⊢ path Y y`. The call `tcTrans P Q : tc ⊢ path Y z`, and
  `path.2 E (…)` derives `path x z`.
- `toTc2 (path.2 E P)`: `path.1 (edgeIn E) : tc2 ⊢ path x Y` and `toTc2 P : tc2 ⊢ path Y y`, joined by
  `tc2`'s `path.2`.
- `toTc (path.2 P Q)`: in `tc2`, `P : tc2 ⊢ path x Y` and `Q : tc2 ⊢ path Y y`, so `tcTrans` joins
  their translations.
- No clause handles `given` for `path`: `path` has rules, so the hidden argument "`own 0` is an input"
  evaluates to `so false`, which is `empty`. Coverage refutes the case (reference `meta/coverage.md`,
  "Cases and probes").

**What the compiler checks.**

- `programOf tc` and `programOf tc2` evaluate to closed programs (7.2).
- Coverage, over the cases that rule names produce: one per rule whose head unifies with the goal atom,
  and `given` where the relation is an input.
- Termination: `P` and `Q` are premises below the matched rule, so they are subterms (reference
  `meta/termination.md`).
- The type of every clause, with the rule variables typed as the rules type them.
- `--safe`: no postulates.

A correct file prints nothing:

```text
$ hugin check --safe closure.hgn
$ hugin check closure.hgn --print-assumptions sameFacts
note: assumptions of `sameFacts`: none
```

**What the editor shows.** The user writes the statement and a hole, and splits `P`:

```hugin
toTc : {x y : g.node} -> tc2 ⊢ path x y -> tc ⊢ path x y.
toTc P = ?.
```

The split produces `toTc (path.1 E) = ?.` and `toTc (path.2 P Q) = ?.`. Hovering over the second hole
shows the goal in E0924's format (`tests/neg/e0924_holes.check`), in `⊢` notation, with the rule's
unnamed variable shown under its name in the rule:

```text
error[E0924]: unsolved goal `?`
  --> closure.hgn:38:20
   |
38 | toTc (path.2 P Q) = ?.
   |                     ^ goal: `tc g ⊢ path x y`
   |
   = note: the hole stands for a meta value of type `tc g ⊢ path x y`
   = note: in scope: `g : graph`, `x : g.node`, `y : g.node`, `Y : g.node`,
           `P : tc2 g ⊢ path x Y`, `Q : tc2 g ⊢ path Y y`
   = help: replace the hole with an expression of type `tc g ⊢ path x y`
```

A mistake gives an ordinary type error. `toTc2 (path.2 E P) = path.2 (toTc2 P) (path.1 (edgeIn E)).` is
E0901: `path.1 (edgeIn E)` derives `path x Y` where `path y ?Z` is expected, and `x` is not `y`. A
recursive call that does not decrease, such as `toTc (path.2 P Q) = toTc (path.2 P Q)`, is E0912.

**The guarantee.** For every input of `road`, `fast.path` prints exactly the pairs that the standard
transitive closure of `road` contains: instantiate `sameFacts` at `g := { node = city, edge = road }`,
and apply the adequacy statement to the instance `fast`.

| link | status |
|---|---|
| `sameFacts`: `tc` and `tc2` derive the same paths, for every graph and input | checked by the meta level |
| `programOf tc`, `programOf tc2` are the rules as written | checked: `programOf` is meta code over the bridge (7.7) |
| `programOf fast` is `programOf (tc2 { node = city, edge = road })` | by the recorded origin of the functor application (compiler) |
| `fast` prints exactly what `fast ⊢ path …` derives (one statement for all programs) | trusted, or checked for each run by `--certify` (P8b) |

**Bridges.** `iff`, `%opaque`, `--print-assumptions` → P1, P2. `derives` → P5. `programOf` → P7a. `⊢`,
rule names, generalisation and the editor → P7b. `--certify` → P8b. The same proof against
hand-written families is in chapter 11; chapter 8 compares the alternatives, and chapter 10 asks
whether `(tc2 g).path x y` could be the proposition itself.

### 1.3 Proof B: a program analysis over-approximates

**The program.** This is a classic of abstract interpretation: reachability on a *coarsened* graph.
Concrete nodes map to abstract nodes through `alpha`, and the analysis computes the reachable abstract
nodes. The property: every abstraction of a reached node is reached by the analysis. So an abstract
node the analysis reports unreached contains no reached node, which is what a user relies on when
pruning by the analysis.

```hugin
%use "std/eq".
%use "std/semantics".

abstraction : Type = {
  node : type, edge : node -> node -> rel, seed : node -> rel,
  anode : type, alpha : node -> anode -> rel }.

coarse (a : abstraction) = {
  reached : a.node -> rel.
  reached X :- a.seed X.
  reached Y :- reached X, a.edge X Y.
  aedge : a.anode -> a.anode -> rel.
  aedge A B :- a.edge X Y, a.alpha X A, a.alpha Y B.
  areached : a.anode -> rel.
  areached A :- a.seed X, a.alpha X A.
  areached B :- areached A, aedge A B.
}.

city : type. country : type.
road : city -> city -> rel. start : city -> rel. located : city -> country -> rel.
%input road. %input start. %input located.
eu = coarse { node = city, edge = road, seed = start, anode = country, alpha = located }.
%output eu.areached.
?- eu.reached X, not located X _.      (* the hypothesis `placed` below: must have no answers *)
```

The rule names are `reached.1`, `reached.2`, `aedge.1`, `areached.1` and `areached.2`.

**The hypothesis.** Every reached node has an abstraction. It is a property of the *input*, so it is a
hypothesis of the theorem, stated with an explicit database and parameter, since it is a definition:

```hugin
placed (d : db) (a : abstraction) : Type =
  (x : a.node) -> coarse a ⊢[d] reached x -> { b : a.anode, ok : coarse a ⊢[d] a.alpha x b }.
```

**The statement and the proof**, complete:

```hugin
(* every abstraction of a reached node is reached by the analysis *)
sound : placed d a -> {x : a.node} -> {b : a.anode} ->
        coarse ⊢ reached x -> coarse ⊢ a.alpha x b -> coarse ⊢ areached b.
sound T (reached.1 S) H = areached.1 S H.
sound T (reached.2 {X := w} R E) H = areached.2 (sound T R (T w R).ok) (aedge.1 E (T w R).ok H).

(* so an abstract node reported unreached contains no reached node *)
safe : placed d a -> {x : a.node} -> {b : a.anode} ->
       (coarse ⊢ areached b -> empty) -> coarse ⊢ a.alpha x b -> coarse ⊢ reached x -> empty.
safe T N H R = N (sound T R H).
%opaque sound. %opaque safe.
```

Generalisation inserts `{d : db} -> {a : abstraction} ->` in front, so `placed d a` refers to the same
`d` and `a` as the judgments. Checked by hand:

- `sound T (reached.1 S) H`: `reached.1` binds `X := x`, so `S : coarse ⊢ a.seed x` and
  `H : coarse ⊢ a.alpha x b`. `areached.1 S H`, with `A := b` and `X := x`, derives `areached b`.
- `sound T (reached.2 {X := w} R E) H`: `reached.2` binds `Y := x` and `X := w : a.node`, so
  `R : coarse ⊢ reached w` and `E : coarse ⊢ a.edge w x`. `T w R : { b : a.anode, ok : … a.alpha w b }`.
  The recursive call `sound T R (T w R).ok : coarse ⊢ areached (T w R).b`. Then `aedge.1 E (T w R).ok H`
  (with `X := w`, `Y := x`, `A := (T w R).b`, `B := b`) derives `aedge (T w R).b b`, and `areached.2`
  derives `areached b`.
- `safe T N H R`: `sound T R H : coarse ⊢ areached b`, and `N` maps it to `empty`.

The converse of `sound` is false (an abstract edge may combine two unrelated concrete edges), so the
analysis is sound but not complete, and no proof of it is attempted.

**What the compiler checks.**

- Coverage of `sound`: the rules with head `reached`. `reached` has rules, so there is no `given` case.
- Termination: `R` is a premise below the matched rule.
- The dependent record `{ b : a.anode, ok : … }` (reference `meta/records.md`).
- The types: `w : a.node` because `X`'s column type in `reached.2` is `a.node`.

**What the editor shows.** Splitting `R : coarse ⊢ reached x` in `sound T R H = ?` produces
`sound T (reached.1 S) H = ?.` and `sound T (reached.2 {X := X} R E) H = ?.`. At the second hole, the
goal is `coarse a ⊢ areached b`, with `T : placed d a`, `X : a.node`, `R : coarse a ⊢ reached X`,
`E : coarse a ⊢ a.edge X x` and `H : coarse a ⊢ a.alpha x b` in scope. Writing `areached.2 ? ?` yields
two goals, `coarse a ⊢ areached ?A` and `coarse a ⊢ aedge ?A b`.

**The guarantee.** If the query has no answers in a run, every country of a reached city is printed by
`eu.areached`, and a country that is not printed contains no reached city.

| link | status |
|---|---|
| `sound`, `safe` for every abstraction and input | checked by the meta level |
| `placed` holds for `eu`'s run | the query has no answers; tied to `placed` by the adequacy statement (trusted) and the query semantics; `--certify` checks the empty answer with the certificate |
| `programOf eu` is `programOf (coarse { … })` | by the recorded origin of the functor application (compiler) |
| `eu` prints exactly what `eu ⊢ …` derives | trusted, or checked by `--certify` |

**Bridges.** `{X := w}`, `empty`, `%opaque` → P2. `derives` → P5. `programOf` → P7a. `⊢`, rule names,
`given`, generalisation → P7b. `--certify` and checked queries → P8b.

### 1.4 Where each piece comes from

| piece | batch | standalone |
|---|---|---|
| E0911 for functions without clauses, `= %postulate`, `--safe`, `%assumptions`, parameter promotion | P1 | yes |
| `std/eq`, `empty`/`unit`/`either`/`iff`, `{x := e}`, implicit patterns, `%opaque`, `decEq` | P2 | yes |
| `match … with`, `match H : … with`, `rewrite … in` | P3 | yes |
| inductive meta `int`; `std/decide` (`so`, `decider`, `decide`) | P4 | yes |
| `std/semantics` (positive): typed values, relation references, `program`, `derives`, `holds`, `monotone` | P5 | partly |
| negation and aggregates in `derives` | P6 | no |
| the code bridge and `programOf` (functors, modules, `here`) | P7a | yes |
| `P ⊢ r t̄`, automatic rule names, `given`, generalisation, case splits and hovers, the adequacy statement | P7b | no |
| `--export-proofs` | P8a | yes |
| `--certify` | P8b | no |
| `(tc2 g).path x y` as an abbreviation, with rule pattern synonyms (level 3.5, chapter 10) | P9, design first (D14) | no |

## 2. Recommendations

1. **First make the logic honest (batch P1).** Today False takes three lines: any meta declaration that
   is not a family or a constructor is a *postulate* (reference `meta/index.md`, "Meta items"), and
   `boom : (A : Type) -> A.` is one. The fix needs no new concept: a meta function declared without
   clauses is a coverage error (E0911), exactly as if clauses were missing; only an empty argument type
   needs none. Abstract declarations in functor signatures and interface files stay parameters. A
   deliberate axiom is written `x : A = %postulate.`, like `= %builtin`, and `--safe` rejects it. A
   command lists the assumptions a definition depends on (Lean's `#print axioms`, Rocq's
   `Print Assumptions`). Apart from postulates, this note found no way to derive False (chapter 5). One
   combination should still be closed before proofs matter: forced large indices together with
   recursion on forced arguments, which Agda forbids under `--safe` (Agda issue #6654).
2. **A small proof library and proof ergonomics (P2, P3).** This means a closed `std/eq` (`refl`, `sym`,
   `trans`, `cong`, `subst`, J by clauses, plus `empty`, `unit`, `either`, `iff`, `dec`). Also explicit
   implicit arguments `f {n := e}` and implicit patterns; *opaque theorems*, never unfolded or eagerly
   evaluated and exempt from W0003; and decidable equality of atoms with evidence. P3 adds the
   right-hand-side `match` (with an optional equation name) and `rewrite … in`. All of this is useful
   without the Datalog goal.
3. **An inductive meta `int` (P4).** It is defined the Lean way (`ofNat`, `negSucc`), unbounded, with
   native arithmetic checked against its clauses as #184 did for `nat`, plus comparison functions. The
   object level keeps 64 bits, and the crossing checks the range (D8a). P4 also adds `std/decide`.
4. **One semantic judgment, defined once (P5, P6).** `std/semantics` defines `derives : program -> db ->
   gatom -> Type` as an ordinary inductive family. Its values are typed object code, its relations
   program-relative references, and it is closed under subfacts. Stratified negation and aggregates
   (P6) work stratum by stratum, as in Benzaken, Contejean and Dumbrava (ITP 2017). Users never write
   semantics.
5. **Ordinary programs, a judgment notation, automatic rule names (P7a, P7b).** P7a's `programOf`
   reifies a functor, a module or the current file as written, over the code bridge (7.7). P7b adds
   `P ⊢ r t̄`, with typed arguments and the database and functor parameters generalised. It adds the
   rule names `r.1`, `r.2` and `given` as patterns and constructors, which is Abella's `case`. It adds
   case splits and hovers in `⊢` notation, and one adequacy statement for all programs. Example 1.2
   proves the doubling closure equal to the standard library's `tc`, and 1.3 an analysis sound, with
   ordinary functors.
6. **The engine stays trusted, with a certificate mode (P8).** P8a exports derivations as Tantow et al.'s
   JSON proof trees, whose Lean checker is verified. P8b adds `--certify`, which checks the reified
   output against `derives` with a checker proven in Hugin.
7. **Relations as propositions (chapter 10, D14 decided).** Levels 1–3 now. Level 3.5,
   per-relation abbreviations `(tc2 g).path x y` with rule pattern synonyms, defined through
   `derives`, gets a detailed design after levels 1–3 are implemented (P9, design first). Level 4,
   every relation *is* a meta inductive predicate, is recorded with its conditions, not planned.
8. **Not now:** a `Prop` universe or definitional proof irrelevance, tactics or meta-level elaborator
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
| inductive families as evidence | yes | yes | yes | yes (examples 1.2, 11.1) | already there |
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
   in a family of the same file is one. P1 makes a function without clauses an E0911 error and adds
   `= %postulate` for deliberate axioms.
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
After P1, `boom` is E0911 (missing cases), and only `boom : (A : Type) -> A = %postulate.` is
accepted, which `--safe` rejects.

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
  directives are; a "rewrite preserves the facts" theorem (1.2, 11.3) is the same kind of result.
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

The semantics is a library, defined once. It is stated over the program as reified data (by
`programOf`, 7.7), so that the program as written *is* the object of proof.

```hugin
%use "std/reflect". %use "std/eq". %use "std/list".

(* values: closed object code of any object type (D4 as refined in r2) *)
value : Type.
v : {τ : ⇑type} -> ⇑τ -> value.

(* relations, relative to a program *)
rref : Type.
own : nat -> rref.                     (* the program's own relation number i *)
arg : string -> rref.                  (* a functor parameter's relation, by signature field *)
ext : sym -> rref.                     (* a relation outside the program, e.g. of the file *)

gatom : Type.
atom : rref -> list value -> gatom.
db : Type = gatom -> Type.             (* a set of facts, as a predicate *)

env : list ⇑type -> Type.              (* typed values of a rule's variables *)
enil : env [].
econs : {τ : ⇑type} -> {ts : list ⇑type} -> ⇑τ -> env ts -> env (τ :: ts).

crule : Type = { head : nat, index : nat, label : option string, vars : list ⇑type,
                 heads : list (catom vars), body : list (cbody vars) }.
program : Type = { relations : list string, rules : list crule, input : rref -> bool,
                   strata : list (list nat) }.
programOf …                            (* the special form of 7.7 *)
instAtom : {ts : list ⇑type} -> env ts -> catom ts -> option gatom.  (* none: undefined arithmetic *)
```

`catom ts` and `cbody ts` are atoms, comparisons and negations over the rule's variables, as de Bruijn
indices into `ts`.

**Values are object code.** A base-type value is an object literal (`⟨3⟩ : ⇑int`), and a fact's
identity is the object term of its constructor and arguments. This reuses the base types even more
than D4 asked: there are no copies at all. Index unification needs object constructors to be injective
and disjoint, and object literals to be disjoint. Chapter 9 shows that object code equality is
syntactic, which justifies both. Arithmetic in the semantics goes through the bridge and the
inductive meta `int`: `add64 : ⇑int -> ⇑int -> option ⇑int` computes on the literals' meta values
and is `none` outside 64 bits (reference `object/arithmetic.md`). Floats stay uninterpreted.

**Relations are program-relative.** `own i` is the program's own relation `i`. `arg "edge"` is the
parameter relation named by the signature field `edge`, so two functors over the same signature (`tc`
and `tc2` over `graph`) read the same input atoms. `ext s` is a relation outside the program. Nothing
depends on the symbol of an abstract parameter, and the input test `p.input (own i)` is decided by
closed data.

**Derivations.** For a positive program, derivations form two mutually inductive families:

```hugin
derives : program -> db -> gatom -> Type.
premises : program -> db -> {ts : list ⇑type} -> env ts -> list (cbody ts) -> Type.
given : {p : program} -> {d : db} -> {r : rref} -> {vs : list value} ->
        so (p.input r) -> d (atom r vs) -> derives p d (atom r vs).
fire  : {p : program} -> {d : db} -> {a : gatom} -> {c : crule} -> {xs : env c.vars} ->
        member c p.rules -> premises p d xs c.body -> memberSome a (map (instAtom xs) c.heads) ->
        derives p d a.
sub   : {p : program} -> {d : db} -> {a : gatom} -> {r : rref} -> {vs : list value} ->
        derives p d a -> subfactOf (atom r vs) a -> derives p d (atom r vs).
pnil  : {p : program} -> {d : db} -> {ts : list ⇑type} -> {xs : env ts} -> premises p d xs [].
ppos  : {p : program} -> {d : db} -> {ts : list ⇑type} -> {xs : env ts} -> {b : catom ts} ->
        {g : gatom} -> {bs : list (cbody ts)} -> eq (instAtom xs b) (some g) -> derives p d g ->
        premises p d xs bs -> premises p d xs (cpos b :: bs).
pcmp  : … -> holdsCmp o (inst xs t) (inst xs u) -> premises p d xs bs -> premises p d xs (ccmp o t u :: bs).
```

Three choices make rule names (7.3) work with ordinary dependent matching:

- **The goal atom is a variable index, and the head is a membership argument.** An index
  `instAtom xs c.head` would be stuck, which index unification postpones and then reports (reference
  `meta/coverage.md`, "Undecided splits"). This is the "green slime" problem.
- **Variables are typed values in an `env`.** Once `c` is a known rule, `c.vars` is a known list, `xs`
  splits into typed variables (`w : ⇑a.node`), and `instAtom` evaluates.
- **`atom`, `own`, `arg` and `v` are constructors, and so are object constructors.** A head with
  another relation, or a different literal, is then refuted, not stuck.

That Hugin's positivity check accepts the mutual pair `derives`/`premises` is a P5 prerequisite to
confirm. The model-theoretic reading, "the least `db` closed under the rules", follows as a theorem, as
in Tantow et al.'s `modelAndProofTreeSemanticsEquivalent`. P5 also proves `holds n p a = true ->
derives p d a` for programs without inputs, where `holds n` is `n` rounds of naive evaluation;
`decide` is that lemma.

- **Strata (P6).** For a stratified program, `derives p d` is defined by recursion over `p.strata`, a
  Type-valued recursion that Hugin allows (`sel : bool -> Type` in reference `meta/clauses.md`). Each
  stratum is a positive family as above, whose negated premises read the model of the strata below, as
  in Benzaken et al.'s stratified engine.
- **Aggregates (P6).** `count`, `sum`, `min` and `max` need finite sets: a list of valuations, a proof
  that it has no duplicates, and a proof that it is complete for the body over the lower strata. Bound
  columns come last and may stay out of scope.

Generic theorems over arbitrary programs use `fire` and `given` directly (11.3). Theorems about a
particular program use the notation and the rule names.

### 7.3 The notation `P ⊢ r t̄` and automatic rule names (P7b)

**Syntax (proposal).**

```text
Judgment ::= Expr ("⊢" | "|-") ("[" Expr "]")? Atom
```

**Elaboration of `P ⊢[e] r t₁ … tₙ`.**

1. *The program.* If `P` is the name of a functor `f`, its parameters are generalised (step 3) and `P`
   becomes `f g`. If `P` is a module, an instance, or a functor application `f a` (where `a` may be a
   variable), `programOf P` is inserted. If `P` already has type `program`, it is used as it is.
   `programOf (f a)` is the program of `f`'s body, with `a`'s relations as the parameter references.
2. *The atom.* `r` is resolved in the scope of `P`'s body: its own relations (`path`), and its
   parameters' relations under the paths the body uses (`g.edge`). Each `tᵢ` is checked as object code
   against `r`'s declared column type `τᵢ`, with object typing (#56) and `⇑` covariance, and becomes
   `v tᵢ`. So a statement's variables are typed nodes (`x : g.node`), abstract in the functor's
   parameter.
3. *Generalisation.* In the type of a declaration, the database is the name `d`, and a functor's
   parameters keep the names of its declaration (`g`). They become the declaration's first implicit
   binders, `{d : db}` and `{g : graph}`, shared by all its judgments. Parameters with the same name
   and type are merged, which is how `tc ⊢` and `tc2 ⊢` share `g`. Any other judgment writes `f a` or
   `⊢[e]`. This is the existing rule for free uppercase variables (reference `meta/functions.md`),
   extended to judgments, like Agda's generalisation of declared variables
   (`doc/user-manual/language/generalization-of-declared-variables.lagda.rst`) and Lean's auto-bound
   implicits. Inside a body or clause, `⊢` uses the `d` in scope.
4. *Result:* `derives (programOf P) d (atom ρ [v t₁, …, v tₙ])`, with `ρ` the reference of `r`.

The editor and diagnostics print `derives (programOf P) d (atom ρ vs)` back as `P ⊢ r t̄`, omitting `d`
when it is the generalised one.

**Automatic rule names.** A rule with head relation `r` is `r.k`, where `k` is its position among the
rules of `r` in the program as written (a rule with several heads gets a name for each). This is the
convention of Isabelle's `tc.intros(k)` (the `inductive` package). An optional label `@n` adds the
name `n`. `given` is the input case. As a pattern against `P ⊢ a`, with `P` closed after evaluation,
`r.k p₁ … pₘ` stands for

```
fire {c := c_rk} {xs := econs X₁ (… enil)} (member proof of c_rk) (ppos refl p₁ (… pnil)) (head proof)
```

The rule's variables `X₁ …` are bound as implicit patterns under their names in the rule, with the
types the rule gives them. `p₁ … pₘ` are the premises in body order; comparison premises are not
written. As an expression, `r.k e₁ … eₘ` builds the same term, with the variables inferred or given by
`{X := e}`. `given I` stands for `given t I`, where `t` proves `so (p.input r)` and is `tt` when that
evaluates to `unit`.

Coverage is the ordinary one over these patterns. The split on `member` enumerates the program's rules.
A rule whose head relation or literals conflict with the goal atom is refuted, and `given` is refuted
for a relation with rules, since `so false` is empty. Termination needs no change: premises are below
`fire`. No family, constructor or lemma is generated; rule names are pattern synonyms computed from a
program value (Agda, `doc/user-manual/language/pattern-synonyms.lagda.rst`).

**Prior art for the notation.** Abella writes the specification judgment as `{P |- A}` and reasons by
`case` on it (`src/metaterm.ml`, `Obj`). Iris writes entailment `P ⊢ Q` as surface notation in its
proof mode. Lean formalisations of programming languages define judgment notation (`Γ ⊢ e : τ`) with
`notation` and `macro`. Hugin's `⊢` is the same kind of notation for one library judgment.

### 7.4 Connecting reflection, semantics and the engine

The chain from a theorem to the facts that a run prints has three links.

1. **Theorem → `derives`.** This link is checked by the meta level, including `programOf`, which is meta
   code over the bridge (7.7).
2. **`derives` → staged program.** `programOf` reifies the rules as written. The trusted steps are
   reification itself, re-elaboration, hygiene renaming, formula-function inlining and the Scala
   transforms (`obj/transform/{Disjunctions,Records}.scala`). The semantics models the source forms
   (`fdisj`, records as facts), so these transforms stay inside the trusted base. That an instance's
   program is its functor's program at its argument relies on the origin that a functor application
   records (NOTES, "Modules are generative records").
3. **Staged program → output.** This is the engine: semi-naive evaluation in
   `runtime/{Engine,Evaluation}.scala`. The adequacy statement says that a run of module `m` on the
   input facts `d` prints `m.r t̄` iff `m ⊢[d] r t̄`. It is one statement for all programs, written in
   the reference (P7b) and checked per run by `--certify` (P8b).

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
slow on large outputs, so this is a CI and audit mode, not the default. The notation and rule names
change nothing here: the certificate is about `derives`, the one judgment.

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
programOf P : program                             (* special form: P a functor, module or `here` *)
```

All of them are primitives in P7a. `programOf` is a special form, not a function, since a functor is
a meta function and cannot be inspected. `programOf f` reifies `f`'s body as written; `programOf (f a)`
uses `a`'s relations for the parameters; `programOf m` reifies a module or an instance (through its
recorded origin); `programOf here` reifies the current file's object rules, so an item that uses it is
elaborated after the file's object items. The result is the semantics' `program`: relations resolved
to references (7.2), rules numbered as `r.1`, `r.2`, …, variables typed by object typing, inputs and
strata computed. No code is generated.

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
them, except under `programOf f`, which turns them into parameter references (`arg "edge"`). Instances of generative modules quote to
their own symbols: two items that apply the same functor quote to two programs, as they stage to two.

**What proofs gain.** Programs no longer have to be written as quotes to be proved about. A functor
written as ordinary rules is `programOf tc`, and `tc ⊢ path x y` states facts about it. A formula function's result is
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
exactly this, and so are the hand-written families of chapter 11:

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
the representation avoids stuck indices. The notation `tc ⊢ path x y` and the automatic rule names
(7.3) are the syntax for that judgment and that case split.

Proof A, transitivity, written as a core primitive (an Abella-style judgment `derives` built into the
type theory, with `case` computed by unification against clause heads) looks the same as with the
library family:

```hugin
tcTrans : {x y z : g.node} -> tc ⊢ path x y -> tc ⊢ path y z -> tc ⊢ path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).
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
| Abella-style primitive (8.3) | none | judgment former and elimination | one statement | `path.1`/`path.2` | 2000–3000 and a consistency argument |
| **library `derives` + rule patterns** (8.3, 7.2–7.3) | none | none (sugar only) | one statement | `path.1`/`path.2` | P5 + P7b, about 2300–3400 |
| Beluga / CMTT (8.4) | LF families | contextual types | per family | as 8.2 | 5000+ |
| layered modal (8.5) | none | layers, staging redesign | narrows link 2 | needs `derives` anyway | redesign |
| 2LTT / MTT (8.6) | — | none / redesign | — | — | — |

### 8.9 Recommendation: combine

Replace `%semantics` with a primitive judgment that the language does not need to make primitive.

1. **One judgment, as a library family.** `derives p d a` in `std/semantics` (P5–P6) is the two-level
   approach's specification judgment, defined in the reasoning logic. Hugin's inductive families and
   index unification make it definable, so it needs no core former, and its consistency is that of
   families.
2. **Abella's `case` as rule names.** For a closed program, `r.k p̄` matches and builds derivations by
   rule name (P7b). This is sugar, elaborated to `fire`, and needs no generated declarations.
3. **One adequacy statement** for every program (7.4), checked per run by `--certify`.
4. **Naming** is automatic (`path.1`, `path.2`); optional labels `@r` add names. No directive is needed.

Two things are lost, and the note accepts both. First, typed abstract carriers: a functor's
`g.node` disappears, since nodes are `value`s and "for every graph" becomes "for every input database".
Second, matching on derivations of an abstract program (generic theorems use `fire` and `input` directly,
as in 11.3). The plan changes accordingly: P7 becomes the code bridge (P7a, 7.7) and rule patterns with
the `⊢` display and the adequacy statement (P7b), instead of derived families and per-relation lemmas
(chapter 12). Revision r2 adds the notation `P ⊢ r t̄` (7.3) and asks, in chapter 10, whether a relation
could itself be the proposition.

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

## 10. Relations as propositions (levels 3.5 and 4)

**Decided (D14).** Levels 1–3 are approved. Level 3.5 gets a detailed design after levels 1–3 are
implemented; its implementation is approved subject to that design's approval (batch P9, "design
first"). Level 4 is recorded as an option with the conditions below; it is not planned.

The levels, for reference:

| level | what the user writes about `tc2`'s `path` |
|---|---|
| 1 | `derives (programOf tc2) d (atom (own 0) [v x, v y])` (the library judgment) |
| 2 | `programOf` from ordinary functors, modules and the file, instead of quotes |
| 3 | `tc2 ⊢ path x y`, with typed arguments, rule names `path.1`, generalised `d` and `g` |
| 3.5 | `(tc2 g).path x y`, an abbreviation for `tc2 g ⊢ path x y`, with pattern synonyms `base`/`join` or `path.1` |
| 4 | `(tc2 g).path x y` *is* a meta inductive predicate, whose constructors are the rules, executed by the engine |

### 10.1 Level 3.5: derived abbreviations

Per relation of a functor or module, the compiler derives a type abbreviation and the rule names as
pattern synonyms, all *defined through* `derives`:

```hugin
(* derived for tc2 (design first, P9) *)
(tc2 g).path : g.node -> g.node -> Type = [x] [y] tc2 g ⊢ path x y.
pattern (tc2 g).path.base E = path.1 E.          (* only if the user labelled the rule @base *)
```

Proof A's statement becomes `iff ((tc g).path x y) ((tc2 g).path x y)`, and its clauses are unchanged.
There is no per-relation adequacy: an abbreviation unfolds to the judgment, and the one adequacy
statement covers it. It fits positive relations of functors and modules, where `(f g).r` reads as a
proposition about the instance. For relations under negation or aggregates, the judgment stays the
honest form. Open questions for its design: name resolution of `(f g).r` at the meta level, where
today it denotes object code; display; and interaction with generativity, where an abbreviation over
the functor, not an instance, avoids it.

### 10.2 Level 4: every relation is an inductive predicate

At level 4, an object relation *is* a meta inductive predicate: its rules are its constructors, and
the engine executes it. This is the mirror image of two known designs:

- Isabelle's predicate compiler `code_pred` turns inductive predicates into executable functions
  (Berghofer, Bulwahn and Haftmann, *Turning inductive into equational specifications*, TPHOLs 2009);
- Rocq's extraction of inductive relations produces certified functional code from inductive
  specifications (Tollitte, Delahaye and Dubois, CPP 2012).

Hugin would go the other way: from rules that run to the predicate they define.

**Before and after, on Proof A.**

```hugin
(* levels 1–3 (approved) *)
tcTrans : {x y z : g.node} -> tc ⊢ path x y -> tc ⊢ path y z -> tc ⊢ path x z.
tcTrans (path.1 E) Q = path.2 E Q.
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).

(* level 4 (option) *)
tcTrans : {x y z : g.node} -> (tc g).path x y -> (tc g).path y z -> (tc g).path x z.
tcTrans (path.1 E) Q = path.2 E Q.               (* constructors of the predicate (tc g).path *)
tcTrans (path.2 E P) Q = path.2 E (tcTrans P Q).
```

The proofs are the same text; the difference is what `(tc g).path` *is*. At level 3 it is notation for
one judgment. At level 4 it is a family of its own, with its own constructors, and `E : g.edge x y`
is the parameter relation as a predicate.

**What level 4 enables.**

- *Relations as types in ordinary meta code:* `route : (x y : node) -> reachable x y -> list node` walks
  a derivation, which connects meta code to first-class facts.
- *Typed abstract carriers* everywhere, not only through a functor's parameter.
- *No visible database:* an input relation is an abstract predicate.
- *Uniformity* with inductive predicates in Lean, Rocq and Agda, and with Isabelle's `inductive`.

**Costs.**

- *Per-relation adequacy:* each relation's predicate must agree with what the engine computes, either
  generated as a proof per relation or certified per run. This is what chapter 8 removed.
- *Negation:* strata must be known to the type checker. `not r x` becomes `r x -> empty` for a relation
  of a lower stratum, and positivity is checked relative to strata.
- *Aggregates and bound columns* do not fit an inductive predicate: `count` needs the whole extension,
  and a bound column is a lattice value, not a derivation.
- *Run-time `%input` relations become abstract predicates,* so every theorem is implicitly over all
  inputs, and a theorem cannot mention the database.
- *A crack in 2LTT's separation:* one name would denote an object relation (stage 0, `⇑(A -> rel)`) and a
  meta type (stage 1). Stage inference (reference `meta/staging.md`) and name resolution (reference
  `meta/families.md`, "Names and stages") would need a new rule, much as shared data types have, but
  for relations, which are not data.
- *Object types as meta carriers:* `%open` types are extensible across files; subfacts, and heads that
  create facts (`∃!`), make a relation's predicate depend on the constructors' predicates.
- *Compile time and incrementality:* every relation would become a family to check, and an edit to a
  rule would change a type (docs/INCREMENTALITY.md).

### 10.3 Recommendation, as decided

Levels 1–3 now (P5, P7a, P7b). Level 3.5 as a design-first follow-up (P9): it removes the notation's
last indirection for the common case, at no cost in adequacy. Level 4 is recorded, not planned. It
would become attractive if:

1. relations-as-types in ordinary meta code (`route`-style functions over derivations) become a
   frequent need that the judgment serves badly;
2. per-relation adequacy can be certified cheaply, for instance by P8b's checker run per relation;
3. stratification can be made part of typing without restricting programs.

## 11. Worked examples against hand-written families

This chapter is the baseline of 8.2: proofs over families written by hand, in today's syntax. 11.1 and
11.2 use only features that exist today. They show that inductive families as evidence already work;
chapter 1 states the same theorems over `derives`, which ties them to the program. 11.3 is a generic
theorem over `derives` and needs P2 and P5.

### 11.1 Reachability is transitive

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
gap that `derives` (7.2) and the notation (7.3) close: in 1.2, `tcTrans` is this proof, over `tc` itself.

### 11.2 Two closure programs derive the same facts

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

The same proof in the notation, with rule names in place of the constructors, states that the two
programs derive the same facts from every input; 1.2 does this for the doubling rule.

### 11.3 A module-wide rewrite preserves the derived facts (generic)

A rewrite that reverses the body of every rule, of the kind a join-order optimiser would apply. On
reified programs:

```hugin
%use "std/list". %use "std/eq". %use "std/semantics".
revC : crule -> crule = [c] (c with { body = reverse c.body }).
revP : program -> program = [p] (p with { rules = map revC p.rules }).

memberMap : {c : crule} -> {cs : list crule} -> member c cs -> member (revC c) (map revC cs).
memberMap here = here.
memberMap (there M) = there (memberMap M).

(* premises are order-independent; by induction on bs, with premSnoc *)
premRev : {q : program} -> {d : db} -> {ts : list ⇑type} -> {xs : env ts} -> {bs : list (cbody ts)} ->
          premises q d xs bs -> premises q d xs (reverse bs).

sound : {p : program} -> {d : db} -> {a : gatom} -> derives p d a -> derives (revP p) d a.
premMap : {p : program} -> {d : db} -> {ts : list ⇑type} -> {xs : env ts} -> {bs : list (cbody ts)} ->
          premises p d xs bs -> premises (revP p) d xs bs.
sound (given T I) = given T I.
sound (fire M Ps H) = fire (memberMap M) (premRev (premMap Ps)) H.
sound (sub D S) = sub (sound D) S.
premMap pnil = pnil.
premMap (ppos E D Ps) = ppos E (sound D) (premMap Ps).
premMap (pcmp C Ps) = pcmp C (premMap Ps).
```

A generic theorem cannot use rule names, since the program is abstract, so it matches `fire` and
`given` directly. Record updates make the cases go through without splitting the rule:

- `(revP p).input` evaluates to `p.input`, so `T` serves for both programs.
- `(revC c).vars` evaluates to `c.vars` and `(revC c).heads` to `c.heads`, so `xs` and the head
  proof `H` carry over.

`sound` and `premMap` are mutually recursive, and each call is on a subterm. `complete`, the converse,
is the same proof plus `reverse (reverse bs) = bs`, a `std/eq` lemma used with `rewrite … in`. A second
lemma says that `programOf` of a file transformed by a module-wide directive `revBodies : module ->
module` is `revP` of the file's `programOf`; it connects the theorem to the directive and is proved by
induction on the module. Together, they make `%reorder` a *verified* directive: using it changes no fact.

## 12. Batches

Each batch is one PR. Line counts are rough (Scala plus Hugin library plus reference and tests).
"Standalone" marks batches that are useful even if the full goal is never reached.

| batch | content | lines | unlocks | risks | standalone |
|---|---|---|---|---|---|
| **P1** honest logic | a meta function declared without clauses is E0911 (missing cases), unless an argument type is empty, as coverage already allows; abstract declarations in functor signatures and interface files stay parameters; `x : A = %postulate.` (like `= %builtin`) for deliberate axioms; `--safe` rejects postulates; `--print-assumptions` / `%assumptions f.` (postulates, trusted primitives); index promotion to parameters and forced-binder rule (D2); reference: a "Consistency" section | 500–800 | trustworthy proofs | programs that relied on silent postulates now get E0911 (no transition period, D1) | **yes**: catches typos that made postulates |
| **P2** proof basics | `std/eq` (J, `subst`, `cong`, `sym`, `trans`), `empty`, `unit`, `either`, `dec`, `iff`; explicit implicits `f {n := e}` and implicit patterns; `%opaque` theorems (no unfolding, no eager evaluation, W0003 exempt); `decEq` for atoms and the symbol conflict rule; polymorphic families confirmed | 900–1400 | all of chapter 1's lemmas | the spelling `{n := e}` (`{n = e}` clashes with a record value argument; reference `meta/records.md`, "Syntax") | **yes** |
| **P3** `match` and `rewrite` | right-hand-side `match e with \| p => e'`, `match H : e with` (abstraction in the goal after normalising with definitions unfolded; desugared to a `where`-local function); `rewrite H in e` via `subst` | 700–1000 | shorter proofs; case expressions in all meta code | which occurrences are abstracted (4.2); error messages for ill-typed abstractions (Agda's experience) | **yes**: Hugin has no case expression today |
| **P4** numbers and decision | inductive meta `int` (`ofNat`, `negSucc`), unbounded, native arithmetic checked against its clauses (#184's method), comparison functions, literals; the range check at the meta→object crossing (D8a); `std/decide` (`so`, `decider`, `decide`), `nat`/`int` lemmas | 1000–1500 | arithmetic in proofs; `add64` in the semantics; meta comparisons | migration of meta `int` code (overflow becomes a crossing error instead of a stuck value); performance of the native path | **yes** |
| **P5** `derives`, positive | `std/semantics`: typed values (`v : ⇑τ -> value`), relation references (`own`, `arg`, `ext`), `program`, `derives`/`premises` with `fire`, `given`, `sub`; index unification on object code (injective constructors, disjoint literals); `add64` and friends; `holds` and its soundness (`decide`); monotonicity; the model-theoretic equivalence | 1600–2300, mostly Hugin | generic theorems (11.3); the target of P7b and P8b | positivity of the mutual families; meta evaluation speed | partly: a reference semantics in the language |
| **P6** negation and aggregates | strata, `cneg`, `count`/`sum`/`min`/`max` with finite witnesses; bound columns maybe later | 1000–1500 | full stratified Datalog∃! | aggregate proofs are heavy | no |
| **P7a** code bridge and `programOf` | `quote : ⇑A -> quoted A`, `unquote`, `quoteF`/`unquoteF`, `symOf`; `programOf` of functors, functor applications, modules, instances and `here`; `unquote (quote c) ≡ c` as a conversion rule; canonical names; the missing syntax forms (`as`, ascription, projection, update) (7.7) | 1000–1500 | ordinary programs as objects of proof | the converse round trip (D12); `here` needs a later elaboration phase | **yes**: typed code analysis for directives |
| **P7b** notation and rule names | `P ⊢[e] r t̄` with typed arguments, generalised `d` and functor parameters (7.3); automatic rule names `r.k`, optional labels, `given`, as patterns and expressions; `decide` with the notation; case splits and hovers in `⊢` notation; the adequacy statement in the reference | 1000–1500 | chapter 1's proofs, over ordinary code | name resolution of atoms in a program's scope; merging generalised parameters | no |
| **P8a** proof-tree export | negative premises in `%derivations`; Tantow et al. JSON export | 300–500 | external verified checking of runs | format drift | **yes** |
| **P8b** certified runs | `--certify`: reified output checked by a meta checker proven against `derives` | 800–1200 | per-run guarantees without a verified engine | meta evaluator speed on large outputs | no |
| **P9** level 3.5, *design first* | after P7b: a detailed design of derived abbreviations `(f g).r x y := f g ⊢ r x y` and rule pattern synonyms (chapter 10); implementation approved subject to that design's approval | design, then 500–900 | relations read as propositions | name resolution of `(f g).r` at the meta level | no |

Order: P1 → P2 → (P3, P4) → P5 → P7a → P7b → P6 → P8b → P9 (design first). P8a can go at any time. Compared with the previous
version, P7 changes: instead of derived families and per-relation adequacy lemmas (1200–1800 lines and
a lemma generator), it adds the code bridge (P7a) and rule patterns with one adequacy statement (P7b; chapters 8, 9).

## 13. Decisions

Every decision is approved by the designer (D1 in the revised form, and D3, D4 and D11 as refined in
rev. 2); D14 is decided as recorded in chapter 10.

| | decision | status | outcome |
|---|---|---|---|
| D1 | postulates | approved | A meta function declared without clauses is a coverage error, E0911, exactly as if clauses were missing; only an empty argument type needs none. Abstract declarations in functor signatures and interface files are parameters and stay unchanged. `x : A = %postulate.` for deliberate axioms; `--safe` rejects postulates; assumptions are listed. No warning period: an error directly. A postulate is a definition-side choice, like `= %builtin`, not a sort like `: data`, so it belongs after `=` |
| D2 | forced large indices | approved | Lean's promotion, which keeps `vec A`, `quoted A`, `eq` and 10.1 small, plus Agda's default for the rest |
| D3 | form of the semantics | approved | library `derives` (chapter 8), written in the notation `P ⊢ r t̄` with automatic rule names (7.3, r2): no core former, no per-relation declarations, one adequacy statement |
| D4 | carrier of values | approved | no copies of base types; refined in rev. 2 and approved: values are closed object code, `v : {τ : ⇑type} -> ⇑τ -> value`, so statements range over typed nodes (7.2) |
| D5 | engine | approved | trusted by default, certificate mode (P8); no verified engine |
| D6 | `Prop`, irrelevance | approved | none for now; revisit if quotients or subset types with proof fields are needed |
| D7 | automation and kernel | approved | proof by reflection (P4) and the language server's goals; a core re-checker only if proofs must convince third parties |
| D8 | integers | approved | the meta `int` is inductive (`ofNat`, `negSucc`), unbounded, native-accelerated with an equation check (#184); the object `int` stays 64-bit; semantics via `add64 : int -> int -> option int` (4.3) |
| D8a | the meta→object crossing of `int` | approved | implicit check with an error, which matches today's rule for persisted values, plus `fits64 : int -> bool` for proofs and for code that wants to branch |
| D9 | K | approved | keep: UIP is consistent, simplifies matching, and Hugin has no univalent ambitions |
| D10 | generativity | approved | theorems about programs (`programOf` of functors), applied to instances through their recorded origin; audit whether memoised closed applications can share a module instance across items |
| D11 | syntax of the proof features | approved | as proposed in chapter 1, details fixed per batch: `= %postulate`, `{x := e}` and `{X := p}`, `%opaque f.`, `match H : e with \| p => e'` and `rewrite H in e`, `P ⊢[e] r t̄` (ASCII `\|-`), rule names `r.k`, `given`, labels `@n`, `programOf`, `here`, the flags `--print-assumptions`, `--export-proofs`, `--certify` |
| D12 | the converse round trip `quote (unquote q) = q` | approved | trusted, listed lemma: quotes are typed where written, and evidence would burden every use |
| D13 | a layered or contextual modal foundation (chapter 9) | approved | the code bridge; revisit if the object level gains β (lambdas, higher-order rules), object-level substitution in conversion, or heavy open-code analysis, or if Hugin wants tactics over its own meta level |
| D14 | relations as propositions (chapter 10) | decided | levels 1–3 approved; level 3.5 gets a detailed design after 1–3 are implemented, and its implementation is approved subject to that design (P9, design first); level 4 recorded as an option with the conditions of 10.3, not planned |

## 14. Sources

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
- S. Berghofer, L. Bulwahn, F. Haftmann: Turning inductive into equational specifications, TPHOLs 2009
  (Isabelle's predicate compiler `code_pred`). P.-N. Tollitte, D. Delahaye, C. Dubois: Producing
  certified functional code from inductive specifications, CPP 2012.
- X. Leroy: Formal verification of a realistic compiler, CACM 52(7), 2009. Iris proof mode notation
  `P ⊢ Q`; Agda `doc/user-manual/language/generalization-of-declared-variables.lagda.rst`; Isabelle's
  `inductive` package (rule names `r.intros`).
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

## 15. Implementation decisions

Decisions made during implementation are listed here with their PR.

**P1 (honest logic).**

- *Clause-less functions.* A meta declaration that is not a family or a constructor is a function, also
  without clauses; its coverage is checked after the file's other declarations, when every constructor
  is known, so a family's constructors may follow the function. The check is skipped for the
  signatures of an imported file, which its own elaboration checks. `x : formula.` in a program is
  therefore E0911 (it cannot add a constructor to a library family).
- *`%postulate`.* Only the definition of a top-level declaration, with optional parameters
  (`f p̄ : A = %postulate.`); elsewhere E0103, in a module body E0907 (as other declarations without a
  value there). `--safe` reports E0925 for each postulate of the program and its imports, as chapter
  1 proposed; the language server has the setting `hugin.safe`, the web worker the option `safe`.
- *Assumptions.* They are the postulates and the *trusted primitives*: the `%builtin` operations of
  the library and the natively computing functions of `std/nat`, as Lean lists `Lean.ofReduceBool`.
  The arithmetic of the meta `int` and the evaluator are part of the language and are not listed.
  `%assumptions f.` is a directive with its own syntax, like `%use` and `%export`: it resolves `f` in
  the file's scope (E0101 otherwise; it counts as a use for W0003) and prints, with
  `--print-assumptions`, on the compiler's explanation output (the lines of `--explain-termination`),
  in source order, before the flags' lines. Hugin's diagnostics have no informational severity with a
  code, so the editor does not show these lines.
- *D2, promotion.* A family's parameters are its longest prefix of arguments that every constructor
  returns as distinct variables, with the same variable at that position in every occurrence of the
  family in its argument types (Lean's `fixedIndicesToParams`). It is recomputed as constructors are
  declared; a constructor that shortens it re-checks the constructors before it, and an error then
  names the earlier constructor's argument (E0914, with a note that it is at an index).
- *D2, forced binders.* Only implicit binders at parameter positions are exempt from predicativity:
  the exemption kept its condition of being implicit, and lost the forced binders at indices (Agda's
  default `--no-large-indices`). For termination, every binder of a constructor at a parameter position
  is not a subterm of the constructor's application, as parameters are not constructor arguments in
  Lean and Agda. Index unification and coverage are unchanged.

**P3 (`match` and `rewrite`).**

- *Keywords.* `match` and `rewrite` are reserved keywords and `=>` a token, as in Agda, Idris 2 and Lean
  4; they are rare as names, and using one gets a syntax error with a help that it is a keyword. `in`
  is a *contextual* keyword (as C#'s `var` and `where`, Rust's `union`, Kotlin's soft keywords): the
  lexer reads it as a name, and the parser takes it as the end of the equation of `rewrite h in e`
  only there, outside delimiters. Everywhere else, also in the body after it, it is a name, since `in`
  is a common relation name in Datalog (membership, `in X S`). `with` was a keyword before P3 (record
  and fact updates `(e with { … })`) and stays one.
- *Layout.* `|` ends a branch's pattern, its expression and the scrutinee (a union is parenthesised
  there); the last branch and the body of `rewrite` extend like a lambda's body. A branch pattern is
  parsed above `|`, so `| X :: Xs => …` needs no parentheses. An absurd branch `| ()` has no `=>`.
- *The equation is implicit and optional in the function.* `match e with` (no `H`) elaborates to
  `m : (y : A) -> G'`, `match H : e with` to `m : (y : A) -> {H : eq e y} -> G'` with clauses
  `m pᵢ {H := H} = eᵢ`: Lean's `match e` versus `match h : e`, Agda's `with e` versus `with e in eq`.
  The implicit binder keeps the equation out of missing-branch messages and case splits.
- *Which `eq`.* The equality of `std/eq`, found through its module value when the program loads it
  (Agda's `BUILTIN EQUALITY`, bound by loading instead of a pragma); E0929 otherwise. `rewrite` uses its
  `subst` and `sym` and adds the universe constraints such an application written by hand would.
- *Abstraction.* Syntactic on normal forms (§4.2), up to bound-variable names; numerals are atoms (as
  Agda's literals), and an offset `N + k` contains `N + j`, `j < k`. Without occurrences the goal is
  kept as written (folded). The abstracted goal is checked again by a small checker of normal forms
  (application arguments against their domains, universes skipped since abstraction cannot change
  levels); an ill-typed one is E0927, naming the term, the goal before and after, the argument that no
  longer fits and whether its type mentions the term (Agda's `w != e of type A` and Lean's `motive is not
  type correct` give none of this).
- *Diagnostics of the function.* Missing branches are E0911 at `match e` ("missing: `blue`", help `| blue
  => …`, and a quick fix inserting the branches); unreachable ones W0006; the function is named
  `f.match` and printed as `match e with …`. Termination errors now show a call on the cycle (before, the
  first call of the clause, which for a `match` was its scrutinee's).
- *Codes.* E0927 (ill-typed abstraction), E0928 (cannot rewrite: not an equation, no occurrence, no
  expected type), E0929 (equality library not loaded).

**P2b (operators of the meta level).**

- *Syntax.* `%infix op f.` binds a symbol to a meta function; it has no associativity or precedence,
  since the symbol keeps its place in the one operator table (`+ -` 6 left, `* /` 7 left, `≡` between
  `|` and `::`, non-associative). A binding therefore never changes how a file parses, and parsing stays
  independent of imports (the `%infix` prescan and slices are unchanged). Lean 4's `infixl:65 " + " =>
  HAdd.hAdd` also binds a notation to a function in one command; fixing the fixity per symbol is OCaml's
  rule (an operator's precedence is given by its first character). The name form `%infix assoc p name.`
  is unchanged.
- *Symbols.* `+ - * / ^ ≡`, with `==` as the ASCII spelling of `≡` (a new token; `=` stays the sign of
  definitions and object comparisons). The comparisons `< <= > >= <>` are not bindable: they are object
  formulas. `≡` sits at internal level 42, below `::` (45) and arithmetic and above `->` and `|`, so
  `x :: xs ≡ ys` and `(n m : nat) -> n + m ≡ m + n` need no parentheses: Agda's `infix 4 _≡_` below
  `infixr 5 _∷_`. In the user-level table it is in the column of level 4 with `|`.
- *`^`.* It stays at level 6, left, where the object level has it as string concatenation; Agda's
  `infixr 8 _^_` would change the object grammar. `^` is bindable, and the library binds it to nothing
  (`std/nat` has no power function).
- *Where a binding may be declared.* In the file that declares the function (Haskell's rule for fixity
  declarations, Agda's for operators); the function is a meta constant with at least two explicit
  arguments. Otherwise E0701, as for `%opaque`. In a module body it is E0907.
- *Scope.* A binding travels with its function: it is in effect wherever the function's name denotes
  the function (declared in the file, opened by `%use`, opened by the prelude), as an Agda operator is
  its name. `%use "std/nat" (minus).` brings `-` and not `+`. Module values carry their file's bindings
  (`ImportedModule.operators`).
- *Overloading.* Idris 2's type-directed choice among alternatives, without classes. Idris prunes the
  alternatives by the target's head and then elaborates each and keeps those that succeed
  (`TTImp.Elab.Ambiguity`); here the candidates are compared by the heads of their types only: results
  against the expected type, then, if several remain, the first explicit domain against the type of the
  left operand (the right one if the left one is a literal), which is inferred once and passed on as
  the argument. Each operand is elaborated exactly once, so nested operators are linear and nothing is
  backtracked or undone. An unknown head (an unsolved type, a stuck type-level application) fits every
  candidate; a type variable of the context is rigid and fits only a generic domain. Several fit:
  E0932; none fits and no built-in meaning applies: E0933, listing the candidates.
- *Built-in meanings.* A fitting binding is preferred; the built-in operators remain the fallback where
  none fits (meta `int` via `std/int`, meta floats and strings). The successor `e + k` on a nat-like
  type comes first, also where `+` is bound. An integer literal next to an operand of unknown type still
  makes it an `int`, and literals alone are integers (`1 + 1 ≡ 2` is about `int`): the literal default is
  not changed by bindings. Object code never applies bindings; `≡` there is E0933.
- *Patterns.* `p op q` is a constructor pattern if `op` denotes a constructor of the expected type (the
  infix constructors of Agda and Haskell); a binding to a function is not a pattern (E0915, naming the
  function), since clause heads stay constructor patterns (D11). `std/nat`'s `plus` is a function, so
  `N + M` is not a pattern; `N + k` stays the successor pattern.
- *`std/int`.* It binds `+ - * /` to `iplus`, `iminus`, `itimes`, `idiv`, the functions the built-in
  operators apply anyway, so that the editor shows them at the operator and the two `+` are told apart
  by types.
- *Printing.* Types and goals still print in prefix form (`eq {nat} (plus 0 n) n`); printing bound
  functions as operators is left open, since printing does not depend on the scope of a file and every
  stored output that shows `plus` or `eq` would change. The arithmetic of `std/int` already prints as
  operators.
- *Tooling.* The operator's position refers to the function: hover shows it with its type, go to
  definition goes to it, and the annotation table of the web editor lists operators. The TextMate
  grammar and the playground colour `≡` and `==` as operators. The inlay hint of the implicit type
  argument of `eq` is shown after `≡` (`≡{nat}`), as after any applied name.
- *Codes.* E0932 (ambiguous operator), E0933 (no binding of the operator fits); E0701 for an invalid
  binding.

**P5a (`std/semantics`: values, programs, `derives`).**

- *Mutual positivity.* Hugin's check looked at each family alone, so `mkA : (b -> empty) -> a.` and
  `mkB : a -> b.` both passed and proved `empty` (an inconsistency, independent of P5). The *mutual
  block* of a family (the strongly connected component of "a constructor of `F` mentions `G`") is now
  recomputed when a constructor is declared, and every family of the block must occur strictly
  positively in every constructor of the block (Agda's `Positivity` over the occurrence graph, Lean 4's
  and Rocq's checks of a mutual block). No `mutual` keyword, since items are unordered; the error (E0913)
  is reported at the constructor that closes the block, before any function can use it. `derives` and
  `premises` are such a block.
- *Index unification on object code.* Quotes are decomposed, spliced variables solved, object constants
  (relations, constructors, types) are injective and pairwise disjoint, object literals and base types
  disjoint, `x = ⟨c $x⟩` a cycle. Object arithmetic and persisted meta values against literals are
  postponed (not computed), so the rules agree with conversion, which compares object code syntactically
  (chapter 9). This is the core change that 7.2 asks for; no new typing rule.
- *Constructor applications checked against the expected type.* `fire M (ppos refl E pnil) H` could not
  be checked: Hugin checked arguments before unifying the result type, and `refl`'s type depends on the
  rule, which only the expected type gives. A meta constructor application (with named implicits before
  its positional arguments) now unifies its result type with the expected type first, if the result does
  not depend on the explicit arguments; undone on failure. Agda's `checkConstructorApplication`, Lean 4's
  `propagateExpectedType`. 11.3's `fire (memberMap M) …` needs the same.
- *No `sub`.* Nested facts are heads: `crule.heads` lists the head and its nested constructor terms, and
  T_R's `subfacts(H[v/x])` equals `subfacts(H)[v/x]` plus facts already present (reference
  `object/facts.md`: every bound value has only facts as constructor subterms); the input database holds
  nested facts as loading adds them. A `subfactOf` relation would need to take object code apart, which
  meta code cannot (D13; P7a's bridge could, later).
- *Instantiated atoms keep their relation outside the partiality.* `instAtom : env ts -> catom ts -> patom`
  with `pat : rref -> option (list value) -> patom`; `fire` ends in `member (pat r (some vs)) (map
  (instAtom xs) c.heads)` and derives `atom r vs`, and `ppos` takes `eq (instAtom xs b) (pat r (some
  vs))`. With `option gatom`, arithmetic in a head over proof variables hid the relation, and a rule of
  another relation could not be refuted (green slime, 7.2).
- *Terms.* `cterm ts τ`: `cv` (a variable, `member τ ts`), `cc` (closed code), `capp` (object code built
  by a meta function from the values of argument terms: constructor terms without object-level
  application), `carith` over `std/reflect`'s `arith_op`, `cneg`. Variables are `member`, as rules in
  `p.rules`. Comparisons `ccmp o l r` with `holdsCmp` (a family over `option ⇑τ`: syntactic equality and
  disequality on any type, integer order); `pcmp C Ps` as in 11.3.
- *Arithmetic.* `intOf : ⇑int -> int`, a trusted primitive (listed by `%assumptions`): the meta value of
  an object integer literal, and `intOf ⟨$m⟩ = m`; stuck elsewhere. `add64`, `sub64`, `mul64`, `div64`
  (none on zero; toward zero), `neg64`: `none` outside 64 bits. Floats and string concatenation are not
  interpreted (`arith64 ocat = none`).
- *Names.* `member`/`here`/`there` as in 11.3 (clashes with `std/list`'s relation `member` only if both
  are opened unselectively, E0109 at the use).

**P5b (`holds`, monotonicity, the least model).**

- *Certifying `holds`.* Naive evaluation carries a derivation with every fact (`dfact p d`): a round
  matches body atoms against the facts (unchecked candidate valuations: variables bound by casting a
  value to the variable's type with `decEq` on `⇑type`, other terms compared by value), then checks each
  candidate with proofs (`checkBody`: `ppos` with the derivation found among the facts, `pcmp` by a
  decision of `holdsCmp`) and builds `fire`. So `holdsSound` is `fromSome`; there is no proof of the
  search. The rounds run at the empty database, and `monotone` carries the derivations to every `d`, so
  `holds : nat -> program -> gatom -> bool` takes no database, and it is sound for programs with input
  relations too (they contribute nothing). `derivable n p : decider gatom (derives p d)` is the `decide`
  of 1.1. Certifying evaluation rather than a verified one follows the proof-producing approach of
  Tantow et al.'s certificates and of Lean's `decide` by kernel evaluation.
- *`same` on closed object code.* `same` (and with it `sameTrue`, `apart`, `decEq`) compares closed object
  code in canonical form (literals, base types, object constants applied to such code) syntactically, as
  index unification and conversion do; stuck on object arithmetic. Quoted patterns keep `atomKey`.
- *Monotonicity* in the database (`monotone`, `included d e`) and in the program (`grow`, `extends p q`:
  rules and input relations mapped). *Least model:* `model p d m` is a family with the one constructor
  `isModel` (a record type made the implicit arguments of `least` unsolvable: a record type unifies field
  by field against unknowns applied to bound variables); `least`, `derivesModel`, and `leastModel a`, a
  record of both directions of "derived iff in every model" (Tantow et al.'s
  `modelAndProofTreeSemanticsEquivalent`), in place of `iff`, whose `Type` arguments are in `Type₀`.
- *Expected type for all meta constants.* The P5a propagation now applies to functions, definitions and
  postulates as well as constructors (Lean 4's `propagateExpectedType` is for any first-order
  application), still only for results that are family applications: 11.2's `lstep2 (lcons E P) F`
  needs it.
- *Memo keys.* Values of `std/semantics` carry types in implicit arguments (`here {A := crule}`), so the
  memo of closed applications read them back at every call although such keys are never closed: a
  `Pi`, `Lam`, `⇑A` or record type is now read back once per value object (its key is never used), and a
  function by clauses applied below its arity is stable data. p5_holds went from 22 s to 4 s; memo hits
  and misses are unchanged.
- *11.3* uses `premAcc` over `foldl` (std/list's `reverse` is a `foldl`) instead of `premSnoc`; `complete`
  is not in the test.

**P7a (the code bridge and `programOf`).**

- *Module.* `std/quote` holds the bridge: `quote`, `unquote`, `quoteF`, `unquoteF` and `symOf` are `%builtin`
  primitives (trusted, listed by `%assumptions`); the constructors they build and read are found by name
  among those the declared types reach, as for `qatom`. It is separate from `std/semantics`, which it
  does not need.
- *The missing syntax forms.* `tas term term`, `tascribe term ⇑type`, `tproj term string`, `twith term
  (list update)` with `uset : string -> term -> update`, and `fas formula term`: one constructor per object
  form of `core/ObjForm.scala`, as `Lean.Expr` has one per core form. The type of an ascription is code
  (`⇑type`, like the index of `quoted`), since types are not data (Q5); an ascription is therefore not a
  quoted pattern (E0917). Lambdas and records stay E0917.
- *`quote`.* Structural on canonical code; stuck as a whole if any subterm is not canonical (equation 2),
  instead of pushing `raw (quote x)` inside, so its result is closed data whenever it reduces. Object
  arithmetic on two literals is already computed when the code is built (chapter 9), so `quote ⟨1 + 2⟩`
  is `tint 3`. `quoteF` nests n-ary conjunctions and disjunctions to the left, as `a, b, c` parses.
- *Canonical names.* A hygiene name `X#k` is renamed by its first occurrence, with one counter for the
  whole code (`X#0`, `Y#1`): the canonical form of locally nameless syntax (Charguéraud, JAR 2012), here
  for the free variables a formula function introduces. Other names (`qvar`'s `x#v`, written names) are
  kept. Conversion compares object variables by name, so `unquote (quote c)` is `c` up to this renaming
  for code with hygiene variables; for terms without them, and for neutral `c`, it is exact.
- *`unquote`.* Structural and untyped: code is typed where it is staged, as reflected data is (equation
  4). It rebuilds arithmetic as evaluation does (literals computed), and a meta integer outside 64 bits
  as a persisted value, which staging reports (E0930). The aggregate variable of `fagg` becomes `V#bₙ`
  (`n` the depth), a name neither source syntax nor `quote` writes.
- *The conversion rule.* `unquote` (`unquoteF`) applied to a stuck `quote c` (`quoteF c`) reduces to `c`, in
  the primitive's reduction: like `$⟨t⟩ = t`, no change to the unifier.
- *D12, realised by a proof.* `quoteUnquote : {A : ⇑type} -> (c : ⇑A) -> eq (quote (unquote (quote c)))
  (quote c)` (and `quoteUnquoteF`) hold by `refl`: by computation on canonical code, by the conversion
  rule on a variable. The unrestricted statement `quote (unquote q) = q` is false (`qterm (tarith oadd
  (tint 1) (tint 2))` unquotes to `⟨3⟩`), so a trusted postulate of it would be inconsistent; D12's
  "trusted, listed lemma" becomes a proved lemma on the image of `quote`, which covers the data of code.
- *Insertion.* With `std/quote` loaded (found through its module value, as `std/eq` for `match`):
  `unquote` is inserted where `quoted A` is used as `⇑B` with `A ≤ B`, and for a quoted term in object
  code whose data depends on a variable (closed data is still reflected where it is elaborated, which
  types it early and keeps its positions); `quote` only in a hole of a quote (`$c`, `c : ⇑A`), and
  `quoteF` in a formula hole (`c : ⇑prop`), the symmetric case the note did not name. Without
  `std/quote`, both stay E0901 / E0918 as before.
- *`symOf : {R : ⇑type} -> ⇑R -> sym`*, the identity on the code of an object constant (a symbol is that
  code), stuck otherwise.
- *`programOf`, syntax.* A contextual special form, like P3's `in`: `programOf e` is the form unless a
  `programOf` is declared or opened; `programOf f a b` reads as `programOf (f a b)`. Lean's `quote` and
  Agda's `quoteTerm` are syntax for the same reason: the argument (a functor, a meta function) cannot be
  inspected as a value.
- *How the body is read.* The functor is applied to fresh variables, so its body is a module in an open
  environment and no instance is created (generativity, D10, is untouched). The rules are evaluated as
  staging evaluates them, with the environment and the object members abstract, which runs splices and
  inlines formula functions; the normal forms are read as data. The data is built as a term over the
  body's environment and applied to the actual arguments, so `programOf (tc g)` is meta code in `g` and
  computes under substitution (`programOf (tc { node = city, edge = road })` gives the rules over `city`).
  A module body records its context's names and types (`ModuleBody.context`) for the column types of
  parameter relations.
- *Instances.* `programOf m` finds the instance among the recorded module instances (its object constants)
  and reads its body at the instance's recorded environment: the "recorded origin" of 7.4 and D10, so
  `programOf fast` is `programOf (tc2 { … })` by `refl`.
- *A bare functor* `programOf f` is `[x̄] programOf (f x̄)`, of type `graph2 -> program`, not chapter 1's
  `tcP : program`: a closed program would need code for the abstract `g.node`. P7b's generalisation
  writes `f g` anyway.
- *References and numbering.* The body's relations, structs and constructors are `own i` in source order;
  a parameter relation is `arg l` by its path in the parameter (`edge`), qualified by the parameter's name
  only if the body has several environment variables; everything else `ext s`. Variables are numbered by
  first occurrence, heads first (as P5a's examples); `index` counts from 1 (`path.1`).
- *Variable types.* Object typing's solution; for a wildcard and a formula function's variable (not rule
  variables of the core), the type of the column it stands in. Without either, E0942.
- *Inputs and strata.* The input test is `inputOf is`, added to `std/semantics`: `arg` and `ext` relations, and the
  own relations without rules (the extensional relations, Abiteboul, Hull and Vianu, ch. 12), so
  `given` is refuted for a relation with rules (chapter 1). `std/quote` does not load `std/semantics`
  (whose proofs take most of a compilation); `programOf` needs both loaded (E0940).
  Strata are Tarjan's components of the own relations, dependencies first; P6 refines them for negation.
- *Heads and `as`.* A rule's heads are its head and its constructor terms, outermost first (P5a's "no
  `sub`"); `(r t̄ as X)` in a body is the atom plus `ccmp ceq X t` with the fact's identity `t`, `X` of the
  fact type.
- *Outside the fragment* (E0942): negation, disjunction, aggregates, floats, `^`, ascriptions,
  projections, updates, and constructor terms of a constant the body declares (generative: no code
  outside an instance). E0940: `std/quote` not loaded; E0941: not a functor, application or module.
- *`here` is deferred.* The file's object rules are elaborated after all its meta declarations (reference
  `meta/index`, "Order of elaboration"), so `programOf here` needs a new phase after the object items, with
  the items that use it and everything that depends on them moved there, and a rule that splices such a
  value rejected as a cycle. That is the risk 12 names; it is left to a follow-up, and `programOf here` is
  E0941 with a note.
- *Proof A over `programOf`.* `tests/run/p7a_program.hgn` proves `sameFacts` for `tc` and `tc2` over
  `programOf (tc g)` and `programOf (tc2 g)` with `fire`/`given`. `g` must be passed (`{g := G}`):
  `programOf (tc g)` mentions `g` only in variable types, so unification does not determine it, which is
  what P7b's generalised parameters address.

**P7b (the judgment notation and rule names).**

- *Syntax.* `⊢` and its ASCII spelling `|-` are one new token; `P ⊢[e] r t̄` sits between `->` and `|`/`≡`
  (non-associative), so `tc ⊢ path x y -> tc ⊢ path y x` needs no parentheses; `[e]` follows the turnstile
  directly, and the atom is an application. Abella writes `{L |- A}`, Iris `P ⊢ Q`, Lean formalisations a
  `notation`; here it is a tree of its own (`Judgment`), elaborated to `derives` with no core rule.
- *Rule names lex after a name.* `.` directly after a name and directly before a digit makes `path.1` (a
  `Select` with digits), as Isabelle names `tc.intros(1)`; every other `.` before a digit still ends an item.
- *Only `std/semantics`.* The notation inserts `programOf` but needs neither `std/quote` nor its name
  (E0945 without `std/semantics`): it is notation for the library judgment, as Lean's `quote` is internal
  syntax of its elaborator.
- *The program.* A functor written alone is generalised; an application or a module gets `programOf`; a
  value of type `program` is used as it is (its relations by the names it lists, its argument types
  inferred). Which one is decided from the head's declared type, so that a functor application is never
  evaluated for it (that would create an instance, D10).
- *Atoms resolve as `programOf` reads bodies.* The body's own relations by their member names, numbered in
  source order as `programOf` numbers them; a parameter's relation by its path (`g.edge`), with the same
  label rule (`arg "edge"`, or `arg "g.edge"` with several parameters); any other name in the scope of the
  judgment, as `ext s`. A symbol is the relation itself, so the file's name denotes the constant the body
  uses wherever both see it (Abella resolves atoms in the specification's signature the same way). The
  arguments are checked against the column types evaluated at the application's arguments.
- *Generalisation.* In a declaration's type and its parameters' types: `{d : db}` first if a judgment has
  no `[e]`, then each alone-written functor's parameters by name and type, in order of occurrence, then the
  free uppercase variables. Parameters of one name are one binder if their types unify (E0946 otherwise);
  a declaration's own parameter or a name in scope is used, not rebound. Elsewhere the names must be in
  scope (E0946, E0947), as Agda generalises declared variables only in signatures and Lean auto-binds only
  in a declaration's header.
- *Folded programs, unified by their arguments.* The generated program of a body stays folded in normal
  forms and in index-unification solutions, and two applications of it unify their arguments first, solving
  unknowns, before unfolding (Lean 4's lazy delta reduction tries the arguments of the same constant first).
  The unfolded program mentions `g` only in variable types (`g.node`), so this is what determines `g`: P7a's
  `{g := G}` is gone from p7a_program. The argument solution may be less general than another one (the
  program is not injective in `g`), never unsound.
- *Rule names are pattern synonyms computed from the program value* (Agda's pattern synonyms), not
  generated constructors. `r.k` is the rule with `head` `r` and `index` `k`, P7a's numbering by the first
  head: a rule with several written heads is named by its first, and its other heads are derived with
  `fire` (a deviation from 7.3's "a name for each", which would disagree with `crule.index`). A label `@n`
  names its rule where `n` denotes nothing else: globals and variables win, so a label never shadows.
- *Patterns.* `r.k p̄` is `fire {xs := econs X₁ …} (there^j here) (ppos refl p₁ … pnil) here`, comparisons as
  `pcmp _`. The rule's variables are implicit-binder pattern variables under their names: in scope unless
  a pattern variable or an earlier (outer, left) rule variable has the name, Agda's hidden arguments bound
  by name. This also fixes a latent order bug: an explicit pattern variable now always shadows an implicit
  binder of the same name. `{X := p}` binds by name; a rule name elsewhere than at a known derivation type
  is E0948. Chapter 1's `{X := w}` is written `{X := W}`: pattern variables are uppercase.
- *Expressions.* `fire` is checked against the goal, then the rule (its member proof), the variables as
  unknowns (or `{X := e}`), the head (which determines its variables from the goal), the premises in body
  order, and the comparisons last, proved by evaluation, `fromSome (decideCmp o x y) tt` (E0948 if they do
  not evaluate to true), as Lean's `decide` proves by evaluation. `given I` with one argument is `given t I`,
  `t` the constructor of `so true` when the input test evaluates to `true`, E0949 when to `false`; with two
  arguments it is the constructor.
- *Coverage splits a derivation into the program's rules.* Below a `given` or `fire` of a program whose
  rules evaluate, Π holds the positions of `fire`'s member and head proofs and their `there` chains (as many
  as rules and heads), so clauses for the goal relation's rules cover, and other relations' rules and
  `given` for a relation with rules are refuted: 7.3's "coverage over the cases rule names produce". Agda
  would need the absurd clauses, Lean's match compiler closes them by `contradiction`; extending Π only for
  derivations keeps the one-level emptiness rule for everything else.
- *Splits and hovers.* A split of a derivation offers the goal relation's rule names, premises named by the
  initials of their relations (fresh per case, the split variable's name reusable), and `given` if the
  relation is an input; `derives (programOf (f ā)) d (atom ρ vs)` prints as `f ā ⊢ r t̄`, without `[d]` for
  the database named `d`. The functor's name is recorded at its first use as a functor; a body reached only
  through an instance prints as `programOf m ā`. Binder types in a hole's context still print unfolded
  (`g : { node : type, … }`), as for any record type alias.
- *`decide`.* `decide : {d : db} -> {p : program} -> {a : gatom} -> (n : nat) -> so (holds n p a) -> derives
  p d a`, appended to `std/semantics` (additive). It shares its name with `std/decide`'s generic `decide`,
  kept because chapter 1 writes `decide 3 tt`; p5_holds opens `std/semantics` selectively, and the
  reference's `holds` example reaches the generic one through `%import "std/decide"`. With `programOf here` deferred (P7a), the example proves
  `trip ⊢ path berlin rome` of a module whose facts are in its body: input relations contribute nothing to
  `holds`, so chapter 1's `tiny` over the input relation `demo` would not evaluate.
- *Adequacy.* Stated in the reference (std/semantics, "Adequacy") for the positive fragment: a run derives
  `m.r t̄` exactly if `m ⊢[d] r t̄`, with `d` the run's facts of the relations that `arg l`, `ext s` and the
  input `own i` denote for `m`; trusted, to be checked per run by P8b.
- *Codes.* E0945 (atom: unknown relation, arity, not an atom, no `std/semantics`), E0946 (generalisation),
  E0947 (no database), E0948 (rule names), E0949 (`given` for a relation with rules).

**P6 (stratified negation and aggregates).**

- *Formulation.* `derives` is unchanged and stays the positive fragment, monotone in the database and the
  program, so P7b's notation over it is unaffected. A stratum is read by a new mutual pair
  `nderives`/`npremises`: `derives` with `nneg` and `nagg`, whose premises read the database parameter `d`
  (the completed strata below), never the derivations. The families are therefore strictly positive and
  P5a's per-block check accepts them unchanged, with no stratum or size index. The perfect model is the
  Type-valued recursion over the strata that 7.2 names: `perfect p d = layers p p.strata (inputs p d)`,
  `layers p (s :: ss) m = layers p ss (nderives (layer p s) m)`. This is the iterated least fixpoint of
  Apt, Blair and Walker and the perfect model of Przymusinski (both 1988), as Benzaken, Contejean and
  Dumbrava's DatalogCert evaluates strata in order with negations read in the interpretation of the strata
  below. Tantow et al.'s checker validates proof trees of positive programs; Hugin's proof export reads a
  negated atom in the Gelfond–Lifschitz reduct of the computed model, which for a stratified program is
  its perfect model (its unique stable model): reading negations in a fixed database is the same idea.
- *Strata in detail.* `layer p s` has the rules with *any* head in `s` (a rule that builds a nested fact
  of an earlier stratum belongs to it as well, as the compiler adds it there: reference `object/facts`),
  and every relation as input, so the facts of all strata below, nested facts derived early included,
  are `ngiven`. The start is `inputs p d`, the facts of `d` in the program's input relations.
- *Negation.* `cnot us a`, not 7.2's `cneg`: `cneg` is the integer negation of terms since P5a. Its local
  variables `us` come first (`catom (append us ts)`, `eappend ys xs`), and `absent` quantifies over them:
  no values make the atom a fact (reference `object/negation`). An undefined instantiated atom makes the
  negation fail (`notIn`), since a formula with an undefined operation does not hold.
- *Aggregates.* `cagg us o x t bs`, with the finite witness `aggHolds d xs us o x t bs`, a record of the
  valuations of the local variables, their soundness and completeness for the body read in `d` (`sat`),
  `distinct`, and the value. It is a record-valued function, not a family, so an aggregate inside an
  aggregate's body raises no positivity question (the recursion is structural on the body). The value
  (`aggOf`) is computed on meta integers and range-checked once, so it does not depend on the order of the
  witness or on partial sums; an undefined term, and `min`/`max` of no valuation, give `none`. `count`
  counts valuations; `programOf` reads its term as the constant `1`. `sum`, `min` and `max` are over
  `int` only (floats are not interpreted, the order of strings is not modelled): E0942 otherwise.
- *Separate module.* The stratified semantics is `std/strata`. With it inside `std/semantics`, the
  elaboration of `%use "std/semantics".` went from 2191 ms to 2567 ms (minimum of six runs, `--stats`),
  which every golden that loads it pays; split, `std/semantics` stays at 2192 ms and `std/strata` takes
  2558 ms in all. The families of a file are closed, so `cnot` and `cagg` stay in `std/semantics`, with
  clauses for them in `holdsIn` (empty), `fromHolds`, `search` and `checkBody`: a rule with a negation or
  an aggregate never fires in `derives` or `holds`. The name is flat, like the other modules of `std/`.
- *`programOf`.* The local variables of a negation or an aggregate are its variables that the rule does
  not bind outside negations and aggregates, by an atom, a comparison or an aggregate's result (the
  binders of the canonical order, reference `object/aggregates`), in the order of the rule's variables;
  they are not the rule's variables, and two aggregates may both have a local `P`. Negated atoms and
  all atoms of aggregate bodies are negative edges for the strata; a negative edge inside a component is
  E0950. The compiler stratifies a module only where it is instantiated (E0601), and `programOf` reads
  functors that may have none.
- *`holds`.* Not extended. Proving a negation or an aggregate by evaluation needs the completeness of the
  facts of the strata below, that is a certified model check of the computed facts, which is P8b's
  `closed` (7.6); `nmodel` and `nleast`, the lemma it rests on, are in `std/strata`. `holds` remains sound,
  and rules with negations or aggregates derive nothing in it.
- *Monotonicity.* `derives` is monotone in the database and the program (P5b); `nderives` is monotone in
  the program (`ngrow`: negations read `d`, not the program's derivations) but not in `d`; each stratum is
  the least model of its rules with negations and aggregates read in `d` (`nleast`, `nderivesModel`,
  `nleastModel`); `perfect` is not monotone in the input facts, which `tests/run/p6_negation.hgn` proves
  for a functor with a negation. Not proved here: `perfect p d a ↔ derives p d a` for a program without
  negations and aggregates (it needs a lemma that the strata order the rules).
- *Codes.* E0950 (a module that `programOf` cannot stratify); E0942 no longer covers negation and integer
  aggregates. Bound columns stay out of scope: `programOf` now rejects an atom of a relation with a bound
  column (E0942), whose best-value reading the program values do not model; before, only arithmetic on
  such a column happened to be rejected.
