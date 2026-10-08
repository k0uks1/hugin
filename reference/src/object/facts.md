# Facts and identity

Facts are the data of the object level. A *fact* is a ground atom `c v₁ … vₙ` of a relation, struct or
constructor `c` that holds in the database. In Hugin facts are first class: every fact has an
*identity*, which is a value, and every constructor term that a rule derives is a fact. This is the
logic DL∃! of Gilray et al. 2024. This chapter defines values and identities, and how constructor terms
are read in heads and in bodies.

## Values

A *value* is a literal (an `int`, `float` or `string`) or the identity of a fact. The columns of facts
hold values. A value of an open type, a fact type or a union is an identity; a value of a base type or a
refinement is a literal.

## Identity

The *identity* of a fact `c v₁ … vₙ` is determined by `c` and the values `v₁ … vₙ`: two facts of the
same constant with the same arguments have the same identity, and are the same fact. An identity is
written like the fact it stands for: `cons 1 nil`, `edge 1 2`. Since the arguments of a fact exist before
the fact, identities are finite trees: no fact contains itself.

> **Note.** In terms of Gilray et al. 2024, a head constructor term `c t̄` is a Skolem existential
> `∃Y. c(Y, t̄)` whose witness `Y` is determined by `t̄`. The implementation interns facts, so equal
> identities are equal machine words.

The following program derives the term `w 1` from two different facts of `src`. It is one fact, so
`got` has one fact and the count is 1.

```hugin,run
wrap : type.
w : int -> wrap.
src : int -> int -> rel.
src 1 2.
src 1 3.
got : wrap -> rel.
got (w X) :- src X _.
facts_of_got : int -> rel.
facts_of_got N :- N = count { G | got G }.
%output facts_of_got.
```

```output
facts_of_got 1.
```

## Constructor terms in heads

A rule derives the fact of its head and every fact nested in it. Formally, let `subfacts(t)` be the set
of the subterms of `t` whose head is a relation, struct or constructor, `t` included. For a rule *R*
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
  structure and binds the variables in it. `holds (w N)` holds for every fact `holds v` where `v` is
  `w n`, and binds `N` to `n`.
- A constructor term on the value side of a *binding equation* `X = c t̄`, where `X` is not bound yet, is
  an *existence check*: the equation holds if `c t̄` is a fact, and binds `X` to its identity. It is read
  as `(c t̄ as X)`. Every constructor subterm of `c t̄` must be a fact as well.
- A constructor term in a comparison whose variables are all bound is compared *structurally*: `X = c t̄`
  holds if `X` has the same structure as `c t̄`, and `X <> c t̄` if it has not. A term that is not a fact is
  equal to no value in the database, and the comparison does not make it a fact.

Every value that a satisfying valuation binds therefore has only facts as constructor subterms. So
matching a nested pattern against a bound value and checking that its subterms exist give the same
results.

The following program shows the three readings. `w 2` and `w 3` are never derived, so `no_pattern` and
`no_check` do not hold; the comparison in `differs` holds without creating `w 9`.

```hugin,run
wrap : type.
w : int -> wrap.
holds : wrap -> rel.
holds (w 1).
by_pattern : int -> rel.
by_pattern N :- holds (w N).
no_pattern : rel.
no_pattern :- holds (w 2).
no_check : rel.
no_check :- X = w 3, holds X.
differs : wrap -> rel.
differs X :- holds X, X <> w 9.
created : int -> rel.
created N :- w N.
%output by_pattern. %output no_pattern. %output no_check. %output differs. %output created.
```

```output
by_pattern 1.
created 1.
differs (w 1).
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

The following program reads the facts of `mk` in `r`, and derives `mk 1` only in the head of `h`. The
fact is available to `r` although `h` is evaluated after `r` would be.

```hugin,run
w : type.
mk : int -> w.
src : int -> rel.
src 1.
r : int -> rel.
r N :- mk N.
h : w -> rel.
h (mk N) :- src N.
?- r N.
```

```output
?- r N.
N = 1.
```

> **Note.** As a consequence, a rule that builds a fact of `c` and negates or aggregates over a relation
> that depends on `c` closes a cycle through negation ([E0601](../errors/E0601.md)).

> **History.** Before the redesign recorded in `docs/REDESIGN.md`, a constructor built a value that was not a fact unless it
> was declared `%fact`. Every constructor is a fact constructor now, and `%fact` does not exist.
