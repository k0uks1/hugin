# Queries, input and output

A program reads *input facts* from facts files, and prints the facts of its *output relations* and the
*answers* to its queries. This chapter defines queries, input relations, the format of facts files, the
choice of the printed relations, derivation facts and the export of a run's proofs.

## Queries

```text
Query ::= "?-" Formula "."
```

A *query* asks for the valuations of its variables under which its formula holds in the database after
evaluation. Its formula is range-restricted like a rule body, and it is typed like a rule body. A query
may mention an [incomplete](negation.md#completeness) relation only positively.

An *answer* is a valuation of the query's *answer variables*: the variables that the query writes,
except wildcards and variables local to a negation or an aggregate. A query without answer variables has
the answer `yes` if its formula holds and `no` otherwise.

The output of a query is the query's text, with every run of whitespace replaced by one space, followed
by one line per answer, `X = v, Y = w.`, in the order of the answer variables' first occurrences. The
lines are sorted, and a query without answers prints `no.`.

The following program asks three queries: one with answers, one without, and one without answer
variables.

```hugin,run
parent : string -> string -> rel.
parent "ann" "bo".
parent "ann" "cy".
?- parent "ann" C.
?- parent "bo" C.
?- parent "ann"   "bo".
```

```output
?- parent "ann" C.
C = "bo".
C = "cy".
?- parent "bo" C.
no.
?- parent "ann" "bo".
yes.
```

## Input facts

A relation declared with the directive `%input r.` or `%open r.` is an *input relation*. Its facts may
come from facts files, given with the option `--facts FILE` (which may be repeated). An `%input` relation
is complete: the files state all of its facts. An `%open` relation is incomplete
([Completeness](negation.md#completeness)). An input relation may also have rules and facts in the
program.

A *facts file* consists of ground facts in the syntax of Hugin, each ending with a period, and comments.
The arguments are literals and constructor terms; a negative number is written in parentheses,
`(-3)`. Loading a fact adds its nested facts as well
([Facts and identity](facts.md#constructor-terms-in-heads)). It is an error
([E0801](../errors/E0801.md)) if a fact names a relation that is not an input relation, has the wrong
number of arguments, or has an argument of the wrong type.

The following program reads its edges from a facts file.

```hugin,run
edge : int -> int -> rel.
%input edge.
reach : int -> int -> rel.
reach X Y :- edge X Y.
reach X Z :- edge X Y, reach Y Z.
```

```facts
edge 1 2.  (* the first edge *)
edge 2 3.
```

```output
reach 1 2.
reach 1 3.
reach 2 3.
```

## Output relations

A relation declared with the directive `%output r.` is an *output relation*. The program prints the
facts of

1. its output relations, if it has any;
2. otherwise no relation, if it has queries;
3. otherwise every relation that is not an input relation; structs and constructors are not printed.

The facts are printed one per line, as `r v₁ … vₙ.`, sorted by their text, before the answers of the
queries, which follow in the order of the queries in the program. A value is printed as its literal or
identity; an argument that is itself a constructor term or a negative number is in parentheses. With the
option `--all-relations` the program prints the facts of every relation and constructor, including input
relations and demand relations.

## Derivation facts

```text
Derivations ::= "%derivations" (QualifiedName | RULE_NAME) "."
```

`%derivations r.` asks for a *derivation fact* for every instance of a named rule that derives a fact of
`r`; `%derivations @n.` does so for the rules named `@n`. The derivation relation of the rules named `@n`
is `@n` (`@n#1`, `@n#2`, … if several rules share the name). Its facts have the derived fact as their
first argument, followed by the *premises* of the instance in the order of the rule's body:

- A positive body atom gives the fact it matches.
- A negated atom `not r t̄` gives its *negative premise*, written `(not r v̄)`: the atom with each argument
  replaced by its value under the instance's valuation. A variable that only the negated atom has is
  local to the negation and keeps its name (`_` for a wildcard). The negative premise states that no fact
  matches the atom; it is not a fact.

Comparisons and aggregates give no premise. Derivation relations are output relations; they cannot be
read by rules.

> **Limitation.** A rule without a name has no derivation relation: `%derivations r.` shows no instances
> of the unnamed rules of `r`.

The following program records how each path was derived by the recursive rule.

```hugin,run
node : type. a, b, c : node.
edge : node -> node -> rel.
edge a b. edge b c.
path : node -> node -> rel.
@base path X Y :- edge X Y.
@step path X Z :- edge X Y, path Y Z.
%derivations @step.
```

```output
@step (path a c) (edge a b) (path b c).
```

The following program records the negative premises of the people without children. The wildcard is
local to the negation.

```hugin,run
person : type.
alice, bob : person.
parent : person -> person -> rel.
parent alice bob.
known : person -> rel.
known alice. known bob.
childless : person -> rel.
@none childless X :- known X, not parent X _.
%derivations @none.
```

```output
@none (childless bob) (known bob) (not parent bob _).
```

## Proof export

The option `--export-proofs FILE` of `hugin run` writes the *proof export* of the run to `FILE`: a proof
of every derived fact, in the JSON format of the verified Datalog checker of
[Tantow et al. 2025](../notation.md#references). Their checker, written and proven correct in Lean, then
validates the run without trusting the implementation. The option `--proof-format` chooses one proof
tree per fact (`trees`, the default) or one ordered proof graph that holds every fact once
(`ordered-graph`, the checker's option `-o`). The file has three members:

- `program`: the *exported rules*, one rule for each head of each rule in the exported fragment (below),
  and a rule without body for each fact of an input relation that no exported rule derives.
- `trees` or `graph`: the proofs of the facts of every relation that occurs in the exported rules. A
  node of a proof is a fact, and its children are the premises of one instance of an exported rule, in
  the order of the body. Of the instances of a fact, the export takes one of least proof depth.
- `hugin`: what the checker does not read: the version (1), the format, the assumption relations, the
  assumed facts and the rules left out, each with the reason.

The schema of the file is [`proof-export.schema.json`](proof-export.schema.json). A relation is named by
its qualified name, a value by its text as `hugin run` prints it (`"pen"`, `seat 1`), and a variable by its
name.

The *exported fragment* is function-free Datalog: rules whose atoms have only variables and constants as
arguments, without `as`, aggregates and disjunctions, whose head relation has no bound column. A negated
atom `not r t̄` is exported as an atom of the relation `not r`, and a comparison `l op r` as the atom
`op(l, r)`; a local variable of a negated atom is the constant of its name. These *assumption relations*
have no rules: their atoms are leaves of the proofs, which the checker accepts as database facts. An atom
of `not r` holds if no fact of the run matches it, and a comparison holds if it is true; both can be
checked against the export.

A rule outside the exported fragment is left out with a warning. A fact that no exported rule derives,
and that is not a fact of an input relation, is an *assumed fact*: a leaf of the proofs, listed under
`hugin`, with a warning.

The option `--certify` checks the same derivations in Hugin itself, against the semantics of
[`std/semantics`](../std/semantics.md) and [`std/strata`](../std/strata.md), with the negated atoms and
comparisons interpreted instead of assumed and with a model check that shows that the run has every
derived fact ([`std/certify`](../std/certify.md)).

The following program has a negated atom and a comparison. Its export has the rule
`childless(X) :- age(X, _#1), "not parent"(X, "_")`, in the format's notation, and the leaf
`"not parent"(carol, "_")` in the proof of `childless carol`.

```hugin,run
person : type.
alice, bob, carol : person.
parent : person -> person -> rel.
parent alice bob.
parent alice carol.
age : person -> int -> rel.
age alice 40. age bob 12. age carol 9.
childless : person -> rel.
childless X :- age X _, not parent X _.
younger : person -> person -> rel.
younger X Y :- childless X, childless Y, age X A, age Y B, A < B.
%output childless. %output younger.
```

```output
childless bob.
childless carol.
younger carol bob.
```

> **Rationale.** The checker's Datalog is positive and has no built-in relations. Reading a negated atom
> as an assumption is the reduct of a program by its model ([Gelfond and Lifschitz
> 1988](../notation.md#references)): the checker validates the positive structure of every proof, and the
> assumptions are what remains to be checked; when they hold, every fact of the export follows from the
> program. The checker's model check (option `-c`) does not see the negated atoms that hold but no proof
> uses, so it does not show that the export is complete for a rule with a negated atom. Constructor
> terms, arithmetic and aggregates have no counterpart in the format, so their rules are left out rather
> than encoded in a way the checker could not validate.

