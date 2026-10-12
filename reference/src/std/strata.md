# `std/strata`

The module `std/strata` defines the meaning of stratified programs with negation and aggregates, over
the program values of [`std/semantics`](semantics.md). Each stratum is read with the facts of the strata
below it as its database: a negated atom holds if no fact of that database matches it, and an aggregate
ranges over the valuations for which its body holds in that database. The *perfect model* `perfect p d`
is the result of reading the strata in order, from the input facts `d`. A program writes
`%use "std/strata".` next to `%use "std/semantics".`

| declaration | meaning |
|---|---|
| `eappend : {us ts : list ⇑type} -> env us -> env ts -> env (append us ts).` | the values of a literal's local variables before those of the rule |
| `notIn : db -> patom -> Type.` | an instantiated atom that is defined and not a fact |
| `absent : db -> {ts : list ⇑type} -> env ts -> (us : list ⇑type) -> catom (append us ts) -> Type.` | when a negated atom holds |
| `distinct : {A : Type} -> list A -> Type.` | a list without repetitions |
| `aggOf : agg_op -> list (option ⇑int) -> option ⇑int.` | the value of an aggregate over the values of its term |
| `sat : db -> {ts : list ⇑type} -> env ts -> list (cbody ts) -> Type.` | when a body holds in a database |
| `aggHolds` | an aggregate's finite witness |
| `nderives : program -> db -> gatom -> Type.`, `npremises` | the derivations in a stratum |
| `layer : program -> list nat -> program.` | the rules of a stratum |
| `inputs : program -> db -> gatom -> Type.` | the facts of a database in the input relations |
| `layers : program -> list (list nat) -> db -> gatom -> Type.` | the strata read in order |
| `perfect : program -> db -> gatom -> Type.` | the perfect model |
| `kept`, `perfectInput` | the facts of a stratum stay facts of the strata above it; an input fact is in the perfect model |
| `toN : {p : program} -> {d : db} -> {a : gatom} -> derives p d a -> nderives p d a.` | a derivation of the positive fragment is one in a stratum |
| `ngrow : {p q : program} -> {d : db} -> extends p q -> {a : gatom} -> nderives p d a -> nderives q d a.` | more rules derive more facts in a stratum |
| `nmodel`, `isNModel`, `nleast`, `nderivesModel`, `nleastModel` | the derived facts of a stratum are its least model |
| `take : nat -> list A -> list A.`, `stratumAt : list (list nat) -> nat -> list nat.` | the first `k` strata; the stratum `k` (`[]` beyond the last) |
| `upTo : program -> nat -> db -> db.` | the facts of the strata before `k` |
| `judged : program -> nat -> db -> db.` | the stratum-local judgment: the derivations of the stratum `k` |
| `lastIn : program -> rref -> list (list nat) -> nat -> bool.` | `k` is a stratum, and no later one has a rule with a head of `r` |
| `adequate` | a fact is in the perfect model exactly if the judgment of its relation's stratum derives it |
| `staysFor`, `lower`, `raise`, `absentOf`, `refuted` | a judgment of a lower stratum in the database of a higher one; negated premises and refutations |

## Negation and aggregates in bodies

The body literals of `std/semantics` include negated atoms and aggregates
([Negation](../object/negation.md), [Aggregates](../object/aggregates.md)). Both have *local
variables* `us`, which come before the rule's variables `ts`: a literal over `append us ts` refers to
local variable `i` by position `i`, and to the rule's variable `j` by position `j` after the local ones.

```hugin,ignore
cnot : (us : list ⇑type) -> catom (append us ts) -> cbody ts.
cagg : (us : list ⇑type) -> agg_op -> cterm ts int -> cterm (append us ts) int ->
       list (cbody (append us ts)) -> cbody ts.
```

`cnot us a` is `not a`, whose variables `us` occur nowhere else in the rule. `cagg us o x t bs` is
`x = o { t | bs }`: `us` are the aggregate's local variables, `x` its result, `t` its term and `bs` its
body. [`programOf`](quote.md#programs-as-values) reads `count { t | φ }` with the term `1`, since the
count does not depend on the term.

## Strata

```hugin,ignore
nneg : absent d xs us b -> npremises p d xs bs -> npremises p d xs (cnot us b :: bs).
nagg : aggHolds d xs us o x t cs -> npremises p d xs bs -> npremises p d xs (cagg us o x t cs :: bs).
```

`nderives` and `npremises` are `derives` and `premises` with the constructors `ngiven`, `nfire`, `nnil`,
`npos` and `ncmp` in place of `given`, `fire`, `pnil`, `ppos` and `pcmp`, and two more premises.
`absent d xs us b` holds if, for all values `ys` of the local variables, the atom `b` instantiated with
`eappend ys xs` is defined and not a fact of `d` (`notIn`): a formula with an undefined operation does
not hold ([Arithmetic and comparisons](../object/arithmetic.md)). `aggHolds d xs us o x t cs` is a record:

| field | meaning |
|---|---|
| `all : list (env us)` | the valuations of the local variables |
| `sound` | the body `cs` holds in `d` for each of them (`sat`) |
| `complete` | each valuation for which the body holds in `d` is among them |
| `once : distinct all` | each is listed once |
| `value` | the aggregate `o` of the term `t` over them is the value of `x` (`aggOf`) |

`aggOf` computes on the meta integers of [`std/int`](int.md): `count` is the number of valuations, `sum`
the sum of the term's values, `min` and `max` the least and the greatest value. It is `none`, so that the
aggregate does not hold, if the result is outside 64 bits, if the term is undefined for a valuation, or
for `min` and `max` of no valuation. The result does not depend on the order of `all`.

Both premises read the database `d`, not the derivations of the stratum, so the families are strictly
positive ([Strict positivity](../meta/families.md#strict-positivity)), and they are correct when `d`
holds the complete facts of the relations that the negations and aggregates read. That is what the
strata give. `layer p s` has the rules of `p` with a head in the stratum `s`, a list of own relations,
and every relation as input. `layers p ss m` reads the strata `ss` in order, each with the facts of the
ones before it as its database, starting from `m`: `layers p (s :: ss) m` is
`layers p ss (nderives (layer p s) m)`. `perfect p d` is `layers p p.strata (inputs p d)`, where
`inputs p d` holds the facts of `d` in the input relations of `p`. A rule with a head in an earlier
stratum, such as a nested fact of a constructor ([Facts and identity](../object/facts.md#facts-derived-in-other-components)),
belongs to that stratum as well.

## Monotonicity

`derives` is monotone in the database and in the program ([`std/semantics`](semantics.md#monotonicity-and-the-least-model)).
In a stratum, `ngrow` shows that more rules and more input relations derive more facts. More facts in the
database do not: a negation or an aggregate that held may fail, and the perfect model is not monotone in
the input facts. Each stratum is the least model of its rules with its negations and aggregates read in
the database: `nleast` maps its derivations into every `nmodel`, a database that contains the input facts
and is closed under the rules, read with the atoms in it and the negations and aggregates in `d`, and
`nderivesModel` shows that its derived facts are one: the iterated least fixpoint of
[Apt et al. 1988](../notation.md#references).

The following program proves that `sink paris` is in the perfect model of a functor with a negation,
for the input fact `road berlin paris`: the edge is given, and no edge leaves `paris`.

```hugin,run
%use "std/eq" (refl, empty, tt).
%use "std/semantics".
%use "std/strata".
%use "std/quote".
complete_graph : Type = { node : type, edge : node -> node -> rel, %complete edge }.
sinks (g : complete_graph) = {
  sink : g.node -> rel.
  sink N :- g.edge _ N, not g.edge N _.
}.
city : type. berlin, paris : city.
road : city -> city -> rel.
%input road.
sinksP : program = programOf (sinks { node = city, edge = road }).
roads : gatom -> Type.
bp : roads (atom (arg "edge") [v (<berlin>), v (<paris>)]).
noRoadFrom : {y : ⇑city} -> roads (atom (arg "edge") [v (<paris>), v y]) -> empty.
noRoadFrom ().
noOut : (ys : env [city]) -> notIn (inputs sinksP roads) (instAtom (eappend ys (econs (<paris>) (econs (<berlin>) enil)))
          (cat (arg "edge") (tcons (cv (there here)) (tcons (cv here) tnil)))).
noOut (econs Y enil) H = noRoadFrom H.snd.
sinkParis : perfect sinksP roads (atom (own 0) [v (<paris>)]) =
  nfire {xs := econs (<paris>) (econs (<berlin>) enil)} here
    (npos refl (ngiven tt { fst = tt, snd = bp }) (nneg noOut nnil)) here.
%opaque sinkParis.
proved : string -> rel.
proved "sink".
```

```output
proved "sink".
```

The rule's variables are `N` and the first wildcard; the second wildcard is local to the negation, so
the negated atom is over `[city, city, city]`, the local variable first. `noOut` takes the value `Y` of
the local variable and a fact `road paris Y`, which `roads` does not hold.

## The stratum-local judgment

The [judgment notation](semantics.md#the-judgment-notation) `P ⊢[d] r t̄` over a program with a negation or
an aggregate in a rule is the *stratum-local judgment* of `r`:

```hugin,ignore
upTo : program -> nat -> db -> db = [p] [k] [d] [a] layers p (take k p.strata) (inputs p d) a.
judged : program -> nat -> db -> db = [p] [k] [d] nderives (layer p (stratumAt p.strata k)) (upTo p k d).
```

`P ⊢[d] r t̄` is `nderives (layer p sₖ) (upTo p k d) (atom ρ vs)`, which is `judged p k d (atom ρ vs)`, for
`p = programOf P`: the derivations of the stratum `sₖ` read with the facts of the strata before it,
where `k` is the last stratum with a rule that has a head of `r` (the first stratum, `0`, for a relation
without rules). It is an error ([E0961](../errors/E0961.md)) if the file does not load `std/strata`. The
facts of `r` are made by the layers up to `k` and kept by the later ones, so the judgment is adequate:

```hugin,ignore
adequate : {p : program} -> {d : db} -> {r : rref} -> {vs : list value} -> (k : nat) -> so (lastIn p r p.strata k) ->
           iff (perfect p d (atom r vs)) (judged p k d (atom r vs)).
```

`lastIn p r ss k` is `true` if `k` is a stratum of `ss` and no later stratum's layer has a rule with a
head of `r`, which evaluates for a program whose rules do, so that `tt` proves it for the `k` of the
notation. A fact of a lower stratum `k` is a fact of the database `upTo p j d` of a higher one `j` if no
layer in between has a rule with a head of its relation (`staysFor p r p.strata k j`): `raise` and
`lower` convert, and for a negated atom without local variables `absentOf k j t` builds the premise
`absent (upTo p j d) xs [] b` from a refutation of the judgment of its relation, `notIn (judged p k d)
(instAtom xs b)`, and `refuted k j t` reads one from it.

[Rule names](semantics.md#rule-names) derive the stratum-local judgment with `nfire`, and the facts of the
strata below with `ngiven`. The following program proves that the module `m` derives `ok berlin`, by
its rule with a negated premise: the fact `node berlin` and a refutation of `bad berlin`, which has no
derivation since the one rule of `bad` derives `bad paris` and `bad` is not an input. A rule pattern
binds the negated premise, whose instance `N enil` refutes the facts of `bad x` below the stratum of
`ok`, which `given` lifts `F` to.

```hugin,run
%use "std/semantics".
%use "std/strata".
%use "std/eq" (empty, emptyElim).
city : type. berlin, paris : city.
m = {
  node : city -> rel.
  bad : city -> rel.
  node berlin. node paris. bad paris.
  ok : city -> rel.
  ok X :- node X, not bad X.
}.
noBad : m ⊢ bad berlin -> empty.
noBad (given I) = emptyElim I.fst.
okBerlin : m ⊢ ok berlin = ok.1 node.1 noBad.
okNotBad : {x : city} -> m ⊢ ok x -> m ⊢ bad x -> empty.
okNotBad (ok.1 B N) F = N enil (given F).
okNotBad (given I) F = emptyElim I.fst.
%opaque noBad okBerlin okNotBad.
proved : string -> rel.
proved "okBerlin".
```

```output
m.bad paris.
m.node berlin.
m.node paris.
m.ok berlin.
proved "okBerlin".
```

The run derives `m.ok berlin`, the fact that `okBerlin` proves. `given I` at a stratum-local judgment reaches the input facts, `inputs p d`, a record whose field `fst`
is the proof that the relation is an input: for `bad`, which has rules, `so false`, which is empty.

> **Rationale.** Reading a relation at the last stratum that makes its facts, with the strata below as a
> database, is the iterated fixpoint of Apt et al. 1988 read stratum by stratum, as
> [Benzaken et al. 2017](../notation.md#references) evaluate a stratum with negations read in the strata
> below. A negated premise takes a refutation, as an inductive definition of Lean or Rocq accepts a
> premise `¬ q x` for a `q` defined before and takes a function into the empty type for it.

> **Note.** `holds` of `std/semantics` evaluates the positive fragment: a rule with a negation or an
> aggregate derives nothing there. Evaluating a negation with a proof needs the facts of the strata below
> to be complete, which a model check of the computed facts shows (`nleast`): `decidePerfect` of
> [`std/certify`](certify.md#deciding-the-perfect-model) evaluates stratified programs with negation so,
> and decides membership in the perfect model both ways. Aggregates are not evaluated there.

> **Rationale.** Reading the strata in order, with the negations read in the completed strata below, is
> the perfect model (Apt et al. 1988; [Przymusinski 1988](../notation.md#references)), as the verified
> engine of [Benzaken et al. 2017](../notation.md#references) computes it. Reading the lower strata as a database parameter,
> not as derivations, keeps the families strictly positive without a size or stratum index. A separate
> module keeps the many programs that load `std/semantics` for the positive fragment from elaborating
> it.
