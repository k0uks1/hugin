# Facts and identity

Facts are the data of the object level. A *fact* is a ground atom `c v₁ … vₙ` of a relation, struct or
constructor `c` that holds in the database. Facts are first class: every fact has an *identity*, which
is a value, and every constructor term that a rule derives is a fact. This is the logic DL∃!
([Gilray et al. 2024](../notation.md#references)). This chapter defines values and identities, and how
constructor terms are read in heads and in bodies.

## Values

A *value* is a literal (an `int`, `float` or `string`) or the identity of a fact. The columns of facts
hold values. A value of an open type, a fact type or a union is an identity; a value of a base type or a
refinement is a literal.

## Identity

The *identity* of a fact `c v₁ … vₙ` is determined by `c` and the values `v₁ … vₙ`: two facts of the
same constant with the same arguments have the same identity, and are the same fact. An identity is
written like the fact it stands for: `cons 1 nil`, `edge 1 2`. Since the arguments of a fact exist before
the fact, identities are finite trees: no fact contains itself.

> **Note.** In DL∃! (Gilray et al. 2024), a head constructor term `c t̄` is a Skolem existential
> `∃Y. c(Y, t̄)` whose witness `Y` is determined by `t̄`. The implementation interns facts, so equal
> identities are equal machine words.

The following program derives the term `account 1` from two different orders of customer 1. Both
derivations give the same fact, so `buyer` has one fact and the count is 1.

```hugin,run
customer : type.
account : (id : int) -> customer.
order : (customer : int) -> (item : string) -> rel.
order 1 "pen".
order 1 "lamp".
buyer : customer -> rel.
buyer (account C) :- order C _.
buyers : int -> rel.
buyers N :- N = count { B | buyer B }.
%output buyers.
```

```output
buyers 1.
```

## Constructor terms in heads

A rule derives the fact of its head and every *nested fact* of it. Formally, let `subfacts(t)` be the
set of the subterms of `t` whose head is a relation, struct or constructor, `t` included. For a rule *R*
with head *H* and body *B*, and a database *db*, the immediate consequence of *R* is

```text
T_R(db) = db ∪ ⋃ { subfacts(H[v̄/x̄]) | db ⊨ B[v̄/x̄] }
```

where the union ranges over the valuations `v̄` of the rule's variables `x̄`. Input facts are read in the
same way: loading `program (add (num 1) (num 2))` adds the facts `num 1`, `num 2`, `add (num 1) (num 2)`
and the `program` fact.

The following program states one nested fact and queries the facts of the inner constructor.

```hugin,run
expr : type.
num : int -> expr.
add : expr -> expr -> expr.
program : expr -> rel.
program (add (num 1) (add (num 2) (num 3))).
?- num N.
```

```output
?- num N.
N = 1.
N = 2.
N = 3.
```

## Bodies never create facts

A body reads the database; it never adds to it. Every constructor term in a body has one of three
readings.

- A constructor term nested in an argument of an atom is a *pattern*. It matches a value with that
  structure and binds the variables in it. `booked (seat N)` holds for every fact `booked v` where `v`
  is `seat n`, and binds `N` to `n`.
- A constructor term on the value side of a *binding equation* `X = c t̄`, where `X` is not bound yet, is
  an *existence check*: the equation holds if `c t̄` is a fact, and binds `X` to its identity. It is read
  as `(c t̄ as X)`. Every constructor subterm of `c t̄` must be a fact as well.
- A constructor term in a comparison whose variables are all bound is compared *structurally*: `X = c t̄`
  holds if `X` has the same structure as `c t̄`, and `X <> c t̄` if it has not. A term that is not a fact
  is equal to no value in the database, and the comparison does not make it a fact.

Every value that a satisfying valuation binds therefore has only facts as constructor subterms. So
matching a nested pattern against a bound value and checking that its subterms exist give the same
results.

The following program shows the three readings. The facts `seat 2` and `seat 3` are never
derived, so `by_pattern_2` and `by_check_3` do not hold. The comparison in `not_nine` holds without
creating `seat 9`.

```hugin,run
place : type.
seat : (number : int) -> place.
booked : place -> rel.
booked (seat 1).
by_pattern : int -> rel.
by_pattern N :- booked (seat N).
by_pattern_2 : rel.
by_pattern_2 :- booked (seat 2).
by_check_3 : rel.
by_check_3 :- X = seat 3, booked X.
not_nine : place -> rel.
not_nine X :- booked X, X <> seat 9.
seats : int -> rel.
seats N :- seat N.
%output by_pattern. %output by_pattern_2. %output by_check_3. %output not_nine. %output seats.
```

```output
by_pattern 1.
not_nine (seat 1).
seats 1.
```

## Facts as values

The identity of a fact of a relation or struct is a value like the identity of a constructor term. A
column whose type is the fact type `r` holds facts of `r`; such a fact can be bound with `as`, passed in
a column, nested in a head, and compared.

```text
AsPattern ::= "(" Expr "as" VAR ")"
```

`(p as X)` matches `p` and binds `X` to the matched value. On an atom, `(r t̄ as X)` binds `X` to the
identity of the fact.

The following program records facts of `edge` in a relation and reads their columns back.

```hugin,run
edge : (src : int) -> (dst : int) -> rel.
edge 1 2.
edge 2 3.
first : edge -> rel.
first E :- (edge 1 _ as E).
targets : int -> rel.
targets D :- first (edge _ D).
%output first. %output targets.
```

```output
first (edge 1 2).
targets 2.
```

## Facts derived in other components

A rule may build a constructor term `c t̄` in its head whose constructor `c` belongs to an earlier
component than the rule's own relation. The fact `c t̄` is then also derived in `c`'s component: the
compiler adds the rule `c t̄ :- B` with the rule's body `B` to that component. So every component is
complete when it has been evaluated, also for facts that later rules build, and the result does not
depend on the order of the components.

The following program reads the facts of the constructor `ticket` in `issued`, and derives `ticket 1`
only in the head of `sold`. The fact is available to `issued` although `sold` would be evaluated after
`issued`.

```hugin,run
pass : type.
ticket : (number : int) -> pass.
sale : int -> rel.
sale 1.
issued : int -> rel.
issued N :- ticket N.
sold : pass -> rel.
sold (ticket N) :- sale N.
?- issued N.
```

```output
?- issued N.
N = 1.
```

> **Note.** As a consequence, a rule that builds a fact of `c` and negates or aggregates over a relation
> that depends on `c` closes a cycle through negation ([E0601](../errors/E0601.md)).

> **History.** Before the redesign recorded in `docs/REDESIGN.md`, a constructor built a value that was
> not a fact unless it was declared `%fact`. The directive `%fact` no longer exists.
