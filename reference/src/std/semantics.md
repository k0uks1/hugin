# `std/semantics`

The module `std/semantics` defines the meaning of Datalog programs in the meta level. A *program value*
is a program as data: its rules over typed variables, its own relations and its input relations. The
inductive family `derives p d a` holds the *derivations* of the fact `a` by the program `p` from the
input facts `d`, so that a property of a program is a meta type, and its proof a meta function. This
page defines the positive fragment: atoms and comparisons in bodies, and the object level's 64-bit
arithmetic. A program writes `%use "std/semantics".`; it builds on [`std/eq`](eq.md) and
[`std/decide`](decide.md).

| declaration | meaning |
|---|---|
| `value : Type.`, `v : {t : ⇑type} -> ⇑t -> value.` | a value: closed object code of any object type |
| `rref : Type.`, `own : nat -> rref.`, `arg : string -> rref.`, `ext : sym -> rref.` | a relation, relative to a program |
| `gatom : Type.`, `atom : rref -> list value -> gatom.` | a fact: a relation with its arguments |
| `db : Type = gatom -> Type.` | a database: a set of facts, as a predicate |
| `member : {A : Type} -> A -> list A -> Type.`, `here`, `there` | membership in a list, by position |
| `env : list ⇑type -> Type.`, `enil`, `econs` | the values of a rule's variables, typed |
| `cterm`, `cterms`, `catom`, `cbody` | the terms, atoms and body literals of a rule |
| `crule : Type.`, `program : Type.` | a rule and a program |
| `intOf : ⇑int -> int.` | the meta integer of an object integer literal |
| `add64`, `sub64`, `mul64`, `div64 : ⇑int -> ⇑int -> option ⇑int.`, `neg64 : ⇑int -> option ⇑int.` | the object level's arithmetic |
| `instTerm`, `instTerms`, `instAtom` | instantiating terms and atoms with the values of the variables |
| `holdsCmp : {t : ⇑type} -> cmp_op -> option ⇑t -> option ⇑t -> Type.` | when a comparison holds |
| `derives : program -> db -> gatom -> Type.` | the derivations of a fact |
| `premises : program -> db -> {ts : list ⇑type} -> env ts -> list (cbody ts) -> Type.` | the proofs that a body holds |
| `monotone : {p : program} -> {d e : db} -> included d e -> {a : gatom} -> derives p d a -> derives p e a.` | more input facts derive more facts |
| `grow : {p q : program} -> {d : db} -> extends p q -> {a : gatom} -> derives p d a -> derives q d a.` | more rules derive more facts |
| `model : program -> db -> db -> Type.`, `isModel` | a database closed under the rules that contains the input facts |
| `least : {p : program} -> {d m : db} -> model p d m -> {a : gatom} -> derives p d a -> m a.` | every model contains the derived facts |
| `derivesModel : {p : program} -> {d : db} -> model p d (derives p d).` | the derived facts are a model |
| `leastModel` | a fact is derived exactly if it is in every model |
| `holds : nat -> program -> gatom -> bool.` | `n` rounds of naive evaluation derive a fact |
| `holdsSound : {d : db} -> (n : nat) -> (p : program) -> (a : gatom) -> so (holds n p a) -> derives p d a.` | `holds` is sound |
| `derivable : {d : db} -> nat -> (p : program) -> decider gatom (derives p d).` | a decider for `decide` of [`std/decide`](decide.md) |

## Values and relations

A value is closed object code ([Staging](../meta/staging.md#object-code)) of any object type: a literal,
`v ⟨3⟩`, or the identity of a fact, its object term, `v ⟨edge berlin paris⟩`
([Facts and identity](../object/facts.md#identity)). Two values are equal exactly if they are the same
code. [Index unification](../meta/coverage.md#index-unification) treats object constants as
constructors and distinct literals as distinct, so a proof can match on values: an equation between two
facts of different constants, or with different literals, has no proof.

A relation is named relative to the program: `own i` is the program's own relation number `i`, `arg l`
the relation of a functor parameter by the field `l` of its signature, and `ext s` a relation outside the
program, by its symbol. So two programs over the same signature read the same input relations, and a
program's input relations are known from its data.

## Programs

The rules of a program are data over their variables. The program of an ordinary functor or module
is built by `programOf` of [`std/quote`](quote.md#programs-as-values); a program can also be written by
hand, as below. A rule with the variables of the object types
`τ₁ … τₙ` has the list `[τ₁, …, τₙ]` of its variables' types, and a variable is its position in that
list, a proof of `member τᵢ [τ₁, …, τₙ]`. The values of the variables are an `env [τ₁, …, τₙ]`, built by
`econs` from code of the types `τᵢ`.

```hugin,ignore
cterm : list ⇑type -> ⇑type -> Type.               (* a term of an object type, over the variables *)
cv : member t ts -> cterm ts t.                     (* a variable *)
cc : ⇑t -> cterm ts t.                              (* a constant or literal *)
capp : (env ss -> ⇑t) -> cterms ts ss -> cterm ts t. (* object code built from the values of terms *)
carith : arith_op -> cterm ts int -> cterm ts int -> cterm ts int.
cneg : cterm ts int -> cterm ts int.
catom : list ⇑type -> Type.                         (* a relation and its argument terms *)
cat : rref -> cterms ts ss -> catom ts.
cbody : list ⇑type -> Type.                         (* an atom, or a comparison *)
cpos : catom ts -> cbody ts.
ccmp : cmp_op -> cterm ts t -> cterm ts t -> cbody ts.
crule : Type = { head : nat, index : nat, label : option string, vars : list ⇑type,
                 heads : list (catom vars), body : list (cbody vars) }.
program : Type = { relations : list string, rules : list crule, input : rref -> bool,
                   strata : list (list nat) }.
```

The fragment above leaves out the implicit arguments. `capp f ts` is a constructor term: `circle (X + 1)`
is `capp` applied to a function that builds `⟨circle $x⟩` from the value `x` of the term `X + 1`. A rule
has a list of head atoms: its head, and the nested facts that the head builds
([Facts and identity](../object/facts.md#constructor-terms-in-heads)). `head` and `index` are the head
relation and the position of the rule among the rules of that relation, and `label` the rule's name `@n`
if it has one. `strata` are the program's strata, lists of its own relations.

`instTerm xs t` is the value of the term `t` for the values `xs` of the variables, and `instAtom xs a` the
instantiated atom `pat r vs`, with the relation `r` of `a` and its argument values `vs`. Arithmetic is the
object level's ([Arithmetic and comparisons](../object/arithmetic.md)), computed on the meta integers of
[`std/int`](int.md): `add64 a b` is the literal of the sum if it is in the 64-bit range, and `none`
otherwise. `div64` is `none` on a division by zero, and rounds toward zero. An instantiated term or
argument list is `none` where the arithmetic in it is undefined. `intOf` is a trusted primitive
([Consistency](../meta/consistency.md#assumptions)): `intOf ⟨n⟩` is `n` for a literal `n`, and
`intOf ⟨$m⟩` is `m` for a persisted meta integer `m`. It is stuck on other object code.

A comparison holds by `holdsCmp`: `ceq` of two values that are the same code, `cne` of two values that
are not, and the order comparisons of two integers by `iless` and `ileq` of `std/int`.

## Derivations

`derives` and `premises` are mutually inductive families
([Strict positivity](../meta/families.md#strict-positivity)):

```hugin,ignore
given : so (p.input r) -> d (atom r vs) -> derives p d (atom r vs).
fire  : {c : crule} -> {xs : env c.vars} ->
        member c p.rules -> premises p d xs c.body -> member (pat r (some vs)) (map (instAtom xs) c.heads) ->
        derives p d (atom r vs).
pnil  : premises p d xs [].
ppos  : eq (instAtom xs b) (pat r (some vs)) -> derives p d (atom r vs) -> premises p d xs bs ->
        premises p d xs (cpos b :: bs).
pcmp  : holdsCmp o (instTerm xs l) (instTerm xs r) -> premises p d xs bs -> premises p d xs (ccmp o l r :: bs).
```

A fact of an input relation is derived if it is in the database (`given`). A rule of the program fires
for values `xs` of its variables for which its body holds, and derives each of its instantiated head
atoms (`fire`). The body holds if each of its atoms is derived for the values (`ppos`) and each of its
comparisons holds (`pcmp`). The facts that `derives p d` holds of are the facts of the least model of
the program's rules that contains the facts of `d` in its input relations.

A derivation is built with these constructors and matched on with them. Once the rule of a `fire` is
known, by its membership proof, and its environment is split into variables (`econs X (econs Y enil)`),
its instantiated atoms evaluate, and index unification decides which rules can derive a fact: a rule
whose head has another relation or another constant conflicts with the fact, and its case needs no
clause, or an absurd pattern. `given` is impossible for a relation that is not an input, since
`so false` is the empty type.

The following program states the rule `linked X Y :- road X Y.` as a program value, derives `linked
berlin paris` from the input fact `road berlin paris`, and proves that `linked paris berlin` is not
derived: its only rule needs the input fact `road paris berlin`, which is not in the database, and no
rule derives `road`.

```hugin,run
%use "std/eq" (refl, empty, tt).
%use "std/semantics".
city : type. berlin, paris : city.
inputs : rref -> bool.
inputs (arg S) = true.
inputs (own N) = false.
inputs (ext S) = false.
linkedRule : crule = { head = 0, index = 1, label = none, vars = [city, city],
  heads = [cat (own 0) (tcons (cv here) (tcons (cv (there here)) tnil))],
  body = [cpos (cat (arg "road") (tcons (cv here) (tcons (cv (there here)) tnil)))] }.
linkedP : program = { relations = ["linked"], rules = [linkedRule], input = inputs, strata = [[0]] }.
roads : gatom -> Type.
bp : roads (atom (arg "road") [v (<berlin>), v (<paris>)]).
onward : derives linkedP roads (atom (own 0) [v (<berlin>), v (<paris>)]) =
  fire {xs := econs (<berlin>) (econs (<paris>) enil)} here (ppos refl (given tt bp) pnil) here.
noWayBack : derives linkedP roads (atom (own 0) [v (<paris>), v (<berlin>)]) -> empty.
noWayBack (given () I).
noWayBack (fire {xs := econs X (econs Y enil)} here (ppos refl (given T ()) pnil) here).
noWayBack (fire {xs := econs X (econs Y enil)} here (ppos refl (fire here Ps (there ())) pnil) here).
%opaque onward noWayBack.
proved : string -> rel.
proved "linked".
```

```output
proved "linked".
```

In `onward`, the expected type determines the program and the rule of `fire`
([Implicit arguments](../meta/functions.md#implicit-arguments)), and the environment gives the values of
the rule's variables. In `noWayBack`, the second clause has the input fact `road paris berlin` as its
premise, which `roads` does not hold, and the third a rule deriving `road`, whose head `linked` has
another relation: in both, an absurd pattern refutes the case.

## Monotonicity and the least model

A program derives more facts from more input facts: `monotone` maps a derivation from `d` to one from `e`
if `included d e`, that is, if every fact of `d` is a fact of `e`. A program with more rules and more input
relations derives more facts: `grow` maps a derivation by `p` to one by `q` if `extends p q`, a record of
a map of the rules of `p` into those of `q` and of the input relations of `p` into those of `q`.

A *model* of a program from the input facts `d` is a database `m` that contains the facts of `d` in the
input relations, and the instantiated heads of every rule whose body holds in `m` (`holdsIn m xs bs`).
`model p d m` is the family with the one constructor `isModel`, which takes these two closure conditions.
The derived facts form the least model: `least` maps a derivation into every model, by induction on the
derivation, and `derivesModel` shows that `derives p d` is a model. `leastModel a` combines the two: a
record of the two directions of "`a` is derived exactly if `a` is in every model".

## Proof by evaluation

`holds n p a` is `true` if `n` rounds of naive evaluation of the rules of `p` derive `a` from no input
facts. Each round matches the body atoms of every rule against the facts so far, which gives candidate
values of the rule's variables, and checks each candidate by evaluating the rule's body. The evaluation is
*certifying*: every fact it finds carries its derivation, built with `fire` from the derivations of the
facts its body uses, so `holdsSound` reads the derivation off the result. The derivations use no input
fact, so they hold for every database, by `monotone`. `derivable n p` is a decider for `decide`
([`std/decide`](decide.md)): a fact that `n` rounds derive is proved by `tt`.

The following program states the fact `road berlin paris` and the rule `linked X Y :- road X Y.` as a
program value without input relations, and proves `linked berlin paris` by evaluation, for every database.

```hugin,run
%use "std/eq" (tt).
%use "std/decide" (decide).
%use "std/semantics".
city : type. berlin, paris : city.
noInputs : rref -> bool.
noInputs R = false.
roadFact : crule = { head = 1, index = 1, label = none, vars = [],
  heads = [cat (own 1) (tcons (cc (<berlin>)) (tcons (cc (<paris>)) tnil))], body = [] }.
linkedRule : crule = { head = 0, index = 1, label = none, vars = [city, city],
  heads = [cat (own 0) (tcons (cv here) (tcons (cv (there here)) tnil))],
  body = [cpos (cat (own 1) (tcons (cv here) (tcons (cv (there here)) tnil)))] }.
roads : program = { relations = ["linked", "road"], rules = [roadFact, linkedRule], input = noInputs, strata = [[1], [0]] }.
onward : {d : db} -> derives roads d (atom (own 0) [v (<berlin>), v (<paris>)]) =
  decide (derivable 2 roads) (atom (own 0) [v (<berlin>), v (<paris>)]) tt.
%opaque onward.
proved : string -> rel.
proved "linked".
```

```output
proved "linked".
```

Two rounds are needed: the first derives `road berlin paris`, the second `linked berlin paris`. With
`derivable 1 roads`, `holds` is `false`, `so false` is the empty type, and `tt` is rejected
([E0901](../errors/E0901.md)). Matching a body atom binds a variable to a value of the variable's type,
compares the other terms by their values, and leaves the comparisons to the check. A rule whose body binds
a variable only in a comparison or a constructor term derives nothing in `holds`, so `holds` may be
`false` for a derived fact, but never `true` for a fact that is not derived.

> **Note.** The rules and derivations are written out here. A later batch of the proofs note (#186)
> adds `programOf`, which builds the program value of a functor or module, and the notation `P ⊢ r t̄`
> with rule names, which elaborates to `derives` and `fire`.

> **Rationale.** The judgment is an inductive family of the library, not a rule of the core calculus:
> its consistency is that of inductive families, and a proof about a program is an ordinary meta
> function. This is the specification judgment of the two-level logic approach
> ([Gacek et al. 2012](../notation.md#references)) defined in the reasoning logic, as Tantow et al.
> define the semantics of Datalog in Lean ([Tantow et al. 2025](../notation.md#references)). The goal
> atom of `fire` is made of variables and its head is a membership, so that matching does not meet an
> index `instAtom xs c.head` that is stuck.

> **Limitation.** Floats and the concatenation of strings are not interpreted: `carith` takes the
> integer operations, and `arith64` is `none` for `ocat`. An atom whose head has arithmetic over
> variables of a proof is told apart from another of the same relation only once its arithmetic is
> computed.
