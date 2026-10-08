# Queries, input and output

A program reads *input facts* from facts files, and prints the facts of its *output relations* and the
*answers* to its queries. This chapter defines queries, input relations, the format of facts files, the
choice of the printed relations and derivation facts.

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

`%derivations r.` asks for a *derivation fact* for every rule instance that derives a fact of `r`;
`%derivations @n.` does so for the rules named `@n`. The derivation relation of the rules named `@n` is
`@n` (`@n#1`, `@n#2`, … if several rules share the name). Its facts have the derived fact as their first
argument and the facts of the positive body atoms of the instance after it. Derivation relations are
output relations; they cannot be read by rules.

The following program records how each path was derived by the recursive rule.

```hugin,run
node : type. a : node. b : node. c : node.
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
