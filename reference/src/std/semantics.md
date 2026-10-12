# `std/semantics`

The module `std/semantics` defines the meaning of Datalog programs in the meta level. A *program value*
is a program as data: its rules over typed variables, its own relations and its input relations. The
inductive family `derives p d a` holds the *derivations* of the fact `a` by the program `p` from the
input facts `d`, so that a property of a program is a meta type, and its proof a meta function. This
page defines the positive fragment: atoms and comparisons in bodies, and the object level's 64-bit
arithmetic. Bodies may also have negated atoms and aggregates, whose meaning, stratum by stratum, is
defined by [`std/strata`](strata.md). A program writes `%use "std/semantics".`; it builds on [`std/eq`](eq.md) and
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
| `inputOf : list nat -> rref -> bool.` | the input test of the programs that `programOf` builds ([`std/quote`](quote.md#programs-as-values)) |
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
| `decide : {d : db} -> {p : program} -> {a : gatom} -> (n : nat) -> so (holds n p a) -> derives p d a.` | proof by evaluation of a [judgment](#the-judgment-notation) |

A property of an ordinary program is stated in the [judgment notation](#the-judgment-notation), `tc G ⊢
path x y`, which elaborates to `derives`, and proved with [rule names](#rule-names), `path.1 E`, which
elaborate to its constructors.

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
cbody : list ⇑type -> Type.                         (* an atom, a comparison, a negation, an aggregate *)
cpos : catom ts -> cbody ts.
ccmp : cmp_op -> cterm ts t -> cterm ts t -> cbody ts.
cnot : (us : list ⇑type) -> catom (append us ts) -> cbody ts.
cagg : (us : list ⇑type) -> agg_op -> cterm ts int -> cterm (append us ts) int ->
       list (cbody (append us ts)) -> cbody ts.
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
if it has one. `strata` are the program's strata, lists of its own relations. `cnot` and `cagg` are a
negated atom and an aggregate, with their local variables `us` ([`std/strata`](strata.md#negation-and-aggregates-in-bodies)).

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
comparisons holds (`pcmp`). A rule with a negation or an aggregate in its body does not fire in
`derives`: these are read by `nderives` of [`std/strata`](strata.md), which has `derives` as its positive
part (`toN`). The facts that `derives p d` holds of are the facts of the least model of
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

## The judgment notation

```text
Judgment ::= Expr ("⊢" | "|-") ("[" Expr "]")? Atom
Atom     ::= Path Expr*
```

A *judgment* `P ⊢[e] r t₁ … tₙ` is the type `derives (programOf P) e (atom ρ [v t₁, …, v tₙ])`: the
derivations of the fact `r t₁ … tₙ` by the program `P` from the database `e`. It is notation, and adds no
rule to the core. It is an error ([E0945](../errors/E0945.md)) if the program does not load
`std/semantics`; it needs neither `std/quote` nor a `programOf` of its own.

The program `P` is one of the following:

- a functor applied to arguments, or a module: its program is `programOf P`
  ([`std/quote`](quote.md#programs-as-values));
- a value of type `program`: the program as it is.

A functor written alone, `tc ⊢ path x y`, is an error ([E0946](../errors/E0946.md)): its arguments are
written, `tc G ⊢ path x y`, and in the type of a declaration a free uppercase variable `G` is bound as
any other ([Generalisation](#generalisation)).

The atom's relation `r` is resolved as the rules of `P`'s body name relations, so that a judgment speaks
of the program as `programOf` reads it: a relation that the body declares is `own i`, a relation of a
functor's parameter is `arg l`, and an object relation of the file is `ext s`. A parameter's relation is
named through the argument that the judgment writes for the parameter, which must be a variable:
`G.edge` in `tc G ⊢ G.edge x y`, for `tc (g : graph)`'s `g.edge`; with several parameters, each
argument names the relations of the parameter at its position. The functor's own name of the parameter,
`g`, is not in scope in the judgment. An argument that is not a variable names no relation. A relation
of the file that is written as such an argument, or as the value of a field of a record written as one,
is the parameter's relation `arg l` for the program's rules, not the file's `ext s`: naming it in the
atom is an error ([E0945](../errors/E0945.md)), so `tc { node = city, edge = road } ⊢ road x y` is
rejected and is stated through a variable argument, `tc G ⊢ G.edge x y`, or an instance. The comparison is
by the constant the name resolves to, as written, without evaluation; a relation of the file that is no
argument's value is `ext s`. A module value, such as an instance `fast`, names none of its functor's
parameters. Each argument
`tᵢ` is checked as code `⇑τᵢ` of the relation's column type `τᵢ`
([Object code](../meta/staging.md#object-code)), and is the value `v tᵢ`. So the variables of a statement
are typed nodes: `x : G.node` is object code of the parameter's type `G.node`. For a program given as a
value, `r` is one of the names its `relations` list, and the arguments' types are inferred. It is an error
([E0945](../errors/E0945.md)) if `r` is none of these, or if the atom has a different number of arguments
than `r` has columns.

The notation covers programs without negation and aggregates, the positive fragment of this page: a
rule with a negated atom or an aggregate in its body never fires in `derives`, so a judgment over a program
with such a rule would state facts about a different program than the one that runs. It is an error
([E0961](../errors/E0961.md)) if a rule of `P` has a negation or an aggregate in its body (when the rules
of `P` are known: a module body, a functor applied, or a program value that evaluates).
Such a program's facts are stated with `nderives` and `perfect` of [`std/strata`](strata.md).

The database `e` is written in brackets directly after the turnstile. Without it, a judgment in the type
of a declaration is at the declaration's anonymous database ([Generalisation](#generalisation)).
Elsewhere, in a definition's body, a lambda, a clause or a local type, its database is an unknown that
unification must determine, as an implicit argument's: `[p : tc g ⊢ path x x] p` checked against
`tc g ⊢[e] path x x -> tc g ⊢[e] path x x` is at `e`. It is an error ([E0947](../errors/E0947.md)) if
unification does not determine it. No name has a meaning for a judgment that it does not write: a
variable named `d` in scope is not its database.

Diagnostics and hovers show `derives (programOf (f ā)) e (atom ρ vs)` as the judgment `f ā ⊢[e] r t̄`
that it elaborates from, without `[e]` for a declaration's anonymous database, and a parameter's relation
through the argument: the goal of `toTc` below is shown as `tc G ⊢ path x y`. The anonymous database
is shown as `_` elsewhere, as in its binder `{_ : db}`.

### Generalisation

In the type of a declaration, and in the types of its parameters, the judgments without `[e]` are at one
*anonymous database*: the declaration's first implicit binder, `{_ : db}`, before those of its free
uppercase variables ([Implicit arguments](../meta/functions.md#implicit-arguments)), shared by all these
judgments, so that a statement such as `tc G ⊢ path x y -> tc G ⊢ path y z -> tc G ⊢ path x z` is about
one database. The binder has no name: no expression refers to it and no clause matches it by name.

Nothing else is generalised that the statement does not write. The program's arguments are written out,
and a free uppercase variable among them, `G` in `tc G ⊢ …`, is bound as any other, with the type of the
functor's parameter, which is known before the binders of the type are elaborated, so that `{x y :
G.node}` may come first. The same variable shares a graph between judgments, `tc G ⊢ …` and `tc2 G ⊢ …`.
A database that a statement refers to is named the same way, `tc G ⊢[D] path x y`: `D` is a free
uppercase variable, which a clause may match, `{D := E}`. The binders are those of `x : A.` and
`x : A = e.`; a clause of the declaration may match `G` by name, `{G := H}`.

The following program states that an edge is a path, for every graph and every database, and proves it by
the first rule of `path` of the transitive closure of [`std/graph`](graph.md).

```hugin,run
%use "std/graph".
%use "std/semantics".
oneStep : {x y : G.node} -> tc G ⊢ G.edge x y -> tc G ⊢ path x y.
oneStep E = path.1 E.
%opaque oneStep.
proved : string -> rel.
proved "oneStep".
```

```output
proved "oneStep".
```

The type of `oneStep` is `{_ : db} -> {G : graph} -> {x y : ⇑G.node} -> derives (programOf (tc G)) _
(atom (arg "edge") [v x, v y]) -> derives (programOf (tc G)) _ (atom (own 0) [v x, v y])`, where `_` is
the anonymous database.

> **Rationale.** Agda's generalisation of declared `variable`s and Lean's auto-bound implicits bind only
> names that the user writes; a name the statement does not write, such as a functor's parameter or a
> database `d`, would act at a distance. The one anonymous database is a scoping rule, one database per
> statement, as Abella's specification judgments share the ambient specification, and blesses no
> identifier. A theorem about `tc G` applies to each instance of `tc`, since the program of an instance
> is the program of the functor at the instance's arguments.

## Relations as propositions

An applied relation that a program owns, written where a meta type is expected, is that program's
judgment: `fast.path x y` is `fast ⊢ path x y`, and `(tc G).path x y` is `tc G ⊢ path x y`. Where a meta
type is expected means where `⇑` would be inserted for an object type
([Stage inference](../meta/staging.md#stage-inference)): checked against a universe, or as the domain,
codomain or binder type of a meta function type. The program owns the relation if it declares it (a
relation, a struct or a constructor of its body); it is found from the atom's head as written, without
evaluating anything:

| written | the program | the judgment |
|---|---|---|
| `fast.path x y`, `fast` an instance or a module | `fast` | `fast ⊢ path x y` |
| `weak.v.vertex x`, a member instance ([Instances](../modules.md#instances)) | `weak.v` | `weak.v ⊢ vertex x` |
| `(tc2 G).path x y`, a functor applied to its arguments | `tc2 G` | `tc2 G ⊢ path x y` |
| `path x y` after `%use trip (path).` | the instance `trip` | `trip ⊢ path x y` |

The judgment is the one that the turnstile without `[e]` denotes at the same place, at the same database:
in the type of a declaration the anonymous one ([Generalisation](#generalisation)), elsewhere an unknown
that unification must determine ([E0947](../errors/E0947.md)). Its arguments, its arity and the program's
fragment are checked as for the turnstile ([E0945](../errors/E0945.md), [E0961](../errors/E0961.md)), and
a free uppercase variable in the program, `G`, is bound as there. The coerced atoms of a declaration's type
share its anonymous database where the compiler finds them from the type's syntax: in the declared type,
an arrow's domain or codomain, a binder's type, a field type of a record type, and an argument of a global
constant whose parameter is a type or a family of types; an atom in another position, such as an argument
of a local function, has a database of its own.

*The η form.* An owned relation written unapplied where a family of meta types `⇑τ₁ -> … -> ⇑τₙ -> Type`
is expected is the function `[x₁] … [xₙ] P ⊢ r x₁ … xₙ`, as a relation passed where a formula function
is expected is eta-expanded ([Stage inference](../meta/staging.md#stage-inference)). A combinator over meta
relations then takes an object relation: `symmetric (undirected G).reach` below.

Not coerced are: a relation of a variable or of a functor's parameter, `G.edge x y`, which every program
over `G` reads (the judgment names the program, `tc G ⊢ G.edge x y`); a relation of the file and of the
body the statement is written in; a relation used unapplied where a type is expected, which is its fact
type ([Fact types](../object/types.md#fact-types)), so a nullary relation's judgment is written `fast ⊢
flag`; a relation of a functor written alone, `tc.path x y`, which names no program
([E0107](../errors/E0107.md)); and an atom with a named database, which keeps the turnstile, `P ⊢[e] r t̄`.
An applied relation that no program owns where a meta type is expected is an error
([E0960](../errors/E0960.md)). The coercion introduces no name: the head of the atom is resolved as
everywhere, and only an object relation that a program owns is coerced. Diagnostics and hovers show the
judgment, `tc G ⊢ path x y`.

```hugin,run
%use "std/graph" (graph).
%use "std/eq" (tt).
%use "std/semantics".

symmetric : {A : Type} -> (A -> A -> Type) -> Type.
symmetric {A := T} R = (x : T) -> (y : T) -> R x y -> R y x.

undirected (g : graph) = {
  link : g.node -> g.node -> rel.
  link X Y :- g.edge X Y.
  link Y X :- g.edge X Y.
}.
linkSym : symmetric (undirected G).link.
linkSym X Y (link.1 E) = link.2 E.
linkSym X Y (link.2 E) = link.1 E.

city : type. berlin, paris, rome : city.
trip = {
  hop : city -> city -> rel.
  hop berlin paris. hop paris rome.
  path : city -> city -> rel.
  path X Y :- hop X Y.
  path X Z :- hop X Y, path Y Z.
}.
%use trip (path).
viaParis : path berlin rome = decide 3 tt.
%opaque linkSym viaParis.
proved : string -> rel.
proved "linkSym, viaParis".
%output proved.
```

```output
proved "linkSym, viaParis".
```

The type of `linkSym` is `{_ : db} -> {G : graph} -> symmetric ([x] [y] undirected G ⊢ link x y)`, and
`viaParis` is `trip ⊢ path berlin rome`.

> **Rationale.** The coercion is inserted by the expected type, as stage inference inserts `⇑`, and as
> Lean's `CoeSort` and Rocq's coercions to `Sortclass` make a term a type where a sort is expected. It
> needs no declaration: a relation is a proposition of the one program that declares it, so the owner is
> read off the atom. A relation of a variable has no such program, and the same text would denote
> different judgments in `tc G` and `tc2 G`, so it keeps the turnstile.

## Rule names

The rules of a relation `r` of a program are named `r.1`, `r.2`, … in the order of the program's rules, a
rule by the relation of its first head (its `index`, [Programs](#programs)); a rule's label `@n` adds the
name `n`, where `n` does not denote anything else. A *rule name* is a derivation by its rule, both as a
pattern and as an expression, against a judgment whose program's rules evaluate. `given` is the
derivation of a fact of an input relation.

As a pattern against `P ⊢[e] a`, the rule name of a rule with the variables `X₁ … Xₖ`, applied to the
patterns `p₁ … pₘ`, stands for

```hugin,ignore
fire {xs := econs X₁ (… (econs Xₖ enil))} M (ppos refl p₁ (… (ppos refl pₘ pnil))) here
```

where `M` is the membership proof of the rule in the program's rules. The patterns `p₁ … pₘ` are the
premises, one for each atom of the rule's body, in body order; the body's comparisons are not written
(`pcmp _` stands for them). The rule's variables are bound as implicit patterns under their names in the
rule: in the clause, `Y` is in scope as the value of the rule's variable `Y`, unless a pattern variable of
the clause or an earlier rule name has that name. `{X := p}` matches the rule's variable `X` with the
pattern `p`. Index unification determines the variables of the head from the goal, and coverage considers
the program's rules ([Derivations](../meta/coverage.md#derivations)): a clause for each rule of the goal's
relation covers a derivation, and `given I`, `given _ I`, is refuted for a relation with rules.

As an expression of a judgment's type, a rule name builds the same derivation. The rule's variables are
determined by the goal's fact, then by the premises; `{X := e}` gives the variable `X`. The body's
comparisons are proved by evaluation, `fromSome (decideCmp o x y) tt`, so they must evaluate to true.
`given I` is `given t I`, where `t` is `tt` if the goal's relation is an input of the program, that is,
if `so (p.input r)` evaluates to `unit`.

It is an error ([E0948](../errors/E0948.md)) if a rule name names no rule of the program, names a rule
whose head relation is not the goal's, has a different number of premises than the rule has atoms in its
body, names a variable that the rule does not have, has a comparison that does not evaluate to true, or is
used where no judgment of a program with known rules is expected; and ([E0949](../errors/E0949.md)) if
`given` derives a fact of a relation that is not an input of the program.

In the editor, splitting a pattern variable of a judgment's type offers the rule names of the goal's
relation, with a variable for each premise named after the premise's relation, and `given` if the goal's
relation is an input: `toTc P = ?.` splits into `toTc (path.1 E) = ?.` and `toTc (path.2 E P) = ?.`.

The following program proves that the transitive closure `tc` and the variant `tc2` with the doubling rule
derive the same paths, for every graph and every input database. `given` derives the input edges, and
`path.1` and `path.2` are the rules of `path` in each program.

```hugin,run
%use "std/graph".
%use "std/eq" (iff).
%use "std/semantics".
tc2 (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- path X Y, path Y Z.
}.
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
%opaque sameFacts.
proved : string -> rel.
proved "sameFacts".
```

```output
proved "sameFacts".
```

In `tcTrans (path.2 E P) Q`, the rule `path X Z :- g.edge X Y, path Y Z.` binds `X` and `Z` to `x` and
`y`, and its variable `Y` is a node in scope: `E : tc G ⊢ G.edge x Y` and `P : tc G ⊢ path Y y`. The
recursive call is on the premise `P`, so it terminates ([Termination](../meta/termination.md)).

> **Rationale.** Rule names are pattern synonyms computed from the program value (Agda's pattern
> synonyms), named as Isabelle's `inductive` package names the introduction rules of a predicate
> (`tc.intros(1)`); matching on them is Abella's `case` on a specification judgment `{P |- A}`. No family,
> constructor or lemma is generated per relation, so the one judgment `derives` keeps one meaning.

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
%use "std/semantics".
%use "std/decide" (decide).
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
a variable only in a comparison or a constructor term, or that has a negation or an aggregate, derives
nothing in `holds`, so `holds` may be
`false` for a derived fact, but never `true` for a fact that is not derived.

The example opens the generic `decide` of `std/decide` next to the `decide` that `std/semantics` declares
itself. The name is then [overloaded](../modules.md#overloaded-opened-names) and chosen by the types:
applied to three arguments, only the generic one fits, since the semantics' `decide` takes two. The
semantics' own `decide n t` is `holdsSound n p a t` with the program and the fact taken from the expected
type, for judgments: a fact of a module whose facts are part of its program is proved by `decide n tt`
for enough rounds `n`. The following program proves by evaluation that a module derives a path through Paris, for
every database.

```hugin,run
%use "std/eq" (tt).
%use "std/semantics".
city : type. berlin, paris, rome : city.
trip = {
  hop : city -> city -> rel.
  hop berlin paris.
  hop paris rome.
  path : city -> city -> rel.
  path X Y :- hop X Y.
  path X Z :- hop X Y, path Y Z.
}.
viaParis : trip ⊢ path berlin rome = decide 3 tt.
%opaque viaParis.
proved : string -> rel.
proved "viaParis".
%output proved.
```

```output
proved "viaParis".
```

The first round derives the two facts of `hop`, the second `path berlin paris` and `path paris rome`, and
the third `path berlin rome`. The input relations of a program contribute no facts to `holds`, so a fact
that depends on the facts of a functor's parameter is not proved by evaluation.

## Adequacy

The judgment is about the program that the engine runs, by one statement for all programs and relations:

> For every module `m` of a program and every run of the program, the run derives the fact `m.r t̄` (and
> prints it if `m.r` is an output relation) exactly if `m ⊢[d] r t̄` has a derivation, where the database
> `d` holds `atom ρ vs` exactly if the run has the fact `s vs` of the relation `s` that `ρ` denotes for
> `m`: for `arg l`, the relation that the arguments of `m`'s functor application give the parameter's
> field `l`; for `ext s`, the relation `s`; for `own i`, the input relation `i` of `m`'s body.

The statement holds for the positive fragment of this page, which is the scope of the notation
([E0961](../errors/E0961.md)). It is trusted: the engine is not verified
against `derives`, but tested against it, as the reference semantics. A theorem about a functor applies to
each of its instances, since `programOf m` is the program of the application that made `m`
([`std/quote`](quote.md#programs-as-values)): `iff (tc G ⊢ path x y) (tc2 G ⊢ path x y)` at `G := { node
= city, edge = road }` is about the run of `fast = tc2 { node = city, edge = road }`.

The option `--certify` of `hugin run` checks the statement for a run, for the program the engine ran and
the run's input facts: the checker of [`std/certify`](certify.md) builds the derivation of every fact of
the run and shows that the facts are closed under the rules, so that the run's facts are exactly the
derived ones.

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
