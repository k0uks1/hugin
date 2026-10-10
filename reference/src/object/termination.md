# Termination

Every accepted program terminates: for every finite set of input facts, every component reaches its
fixed point after finitely many rounds. The compiler checks this statically. A recursive component that
may grow without bound needs a *termination argument*, either descent along derivations (A) or guarded
induction (B). A component for which the compiler finds neither is rejected. A program may declare a
measure with `%terminates` where the inferred measures do not suffice. This chapter defines when a
component needs an argument, the two arguments, the measure directive and the known limitation.

## Value invention

A recursive component can only be infinite if its rules create values that did not exist before. A rule
is *constructive* (it performs *value invention*) if one of the following holds.

1. A head builds a constructor term that is not matched in the body and can take infinitely many
   values. A term takes finitely many values if it is ground, or if each of its variables is bound by a
   *finite source*: a positive body atom of a relation outside the component. If the head's relation is a
   constructor, the head itself counts as a built term: `s (s N) :- s N.` builds `s (s N)`.
2. A head contains arithmetic (`p (N + 1) :- …`), or a head variable is computed by an equation with
   arithmetic (`p M :- …, M = N + 1`).
3. A head contains a variable bound with `as` to a fact of the body.

The bound column of a head is not counted: its values are kept finite by
[bound column](bound-columns.md) evaluation. A recursive component without constructive rules is finite,
since it only combines finitely many existing values. Every other recursive component needs a
termination argument.

The following program has two recursive components, and neither has a constructive rule. The
constructor term `red` in the head of `paint` is ground. The term `label Y` in the head of `tagged`
takes its argument from the relation `item`, which is outside the component.

```hugin,run
color : type. red : color. green : color.
tag : type. label : int -> tag.
item : int -> rel. item 1. item 2.
paint : int -> color -> rel.
paint X green :- item X.
paint X red :- paint X _.
tagged : int -> tag -> rel.
tagged 0 (label 0).
tagged X (label Y) :- tagged X _, item Y.
?- tagged 0 T.
```

```output
?- tagged 0 T.
T = label 0.
T = label 1.
T = label 2.
```

## Order of the arguments

The compiler tries the arguments in this order:

1. If a relation of the component has a measure declared with [`%terminates`](#declared-measures),
   guarded induction with the declared measures. If it fails, the program is rejected
   ([E0604](../errors/E0604.md)).
2. Otherwise descent along derivations (A).
3. Then guarded induction (B) with an inferred measure.
4. Otherwise the program is rejected ([E0603](../errors/E0603.md)).

The option `--explain-termination` prints, for every recursive component, which argument applies and the
reason for every recursive step.

## Decrease

Both arguments compare argument values in two well-founded orders.

- Values of types other than `int` and its refinements are ordered by the *proper subterm* relation: `t`
  is smaller than `c … t …`. Since identities are finite trees, this order is well founded independently
  of the input.
- Integers are ordered by `<`. A decrease counts only toward a bound: a strict decrease needs a lower
  bound on the smaller value, and a strict increase an upper bound on the larger.

The compiler derives decreases and bounds from the body. It computes an interval for every integer term
from the comparisons of the body, by propagation through `+`, `-`, unary `-`, multiplication by a literal
and division by a positive literal. A difference `a - b` is bounded by rewriting it with the linear
equations of the body. `A = N - 1` with `N > 1` gives `A < N` and `A >= 1`; `H = N / 2` with `N >= 1`
gives `H < N`. A value is also bounded if its variables are bound by finite sources.

## Descent along derivations (A)

For a rule `H :- …, B, …` of the component, where `B` is a body atom of a relation of the component (a
*premise*), the *size-change graph* `G(B, H)` relates the arguments of `B` to those of `H`. It has an arc
from argument `i` of `B` to argument `j` of `H` labelled

- `=` if the two are equal (syntactically, by an equation of the body, or by intervals);
- `>` (strict decrease) if `hⱼ` is a proper subterm of `bᵢ`, or `hⱼ` is an integer below `bᵢ` and bounded
  below;
- `≥` (weak decrease) if `hⱼ ≤ bᵢ`, or the strict decrease holds without the bound;
- `<` (strict increase) if `hⱼ` is an integer above `bᵢ` and bounded above, and `≤` (weak increase)
  likewise without the strict difference or the bound.

Graphs compose along paths of steps: `=` is neutral, two decreases give a decrease, strict if one is,
and two increases give an increase. A decrease followed by an increase gives no arc. The component
satisfies (A) if, in the closure of its graphs under composition, every graph `G : p → p` with
`G ; G = G` has a strict arc from an argument to itself, or the arc `=` from every argument to itself.

Then every chain of derivations through the component is finite, and so is the component
([Lee et al. 2001](../notation.md#references), Theorem 4, applied to derivation chains).

The closure can be large, but the check does not compute all of it, and there is no limit on its size.
A graph `G` is *weaker* than `G'` between the same relations if every arc of `G` is implied by an arc
of `G'` between the same arguments (`=` implies `≥` and `≤`; a strict arc implies the weak one of its
direction). Only the weakest graphs are composed further, and every graph `G : p → p` among them is
tested directly: some strict arc lies on a cycle of arcs of `G` of the same direction (`=` counts for
both), or every argument lies on a cycle of `=` arcs. This holds for `G` exactly when it holds for the
idempotent power of `G`, and it is preserved when a graph is replaced by a stronger one, so a component
satisfies (A) exactly when its weakest graphs pass this test (the local criterion of
[Ben-Amram and Lee 2007](../notation.md#references); [Fogarty and Vardi 2012](../notation.md#references),
Section 4.1).

The following program is accepted by (A). The expression in the derived fact is a proper subterm of the
one in the premise, and the counter `A` is smaller than `N` and bounded below by `N > 1`.

```hugin,run
expr : type.
num : int -> expr.
neg : expr -> expr.
start : expr -> rel.
start (neg (neg (num 3))).
inside : expr -> rel.
inside E :- start E.
inside E :- inside (neg E).
need : int -> rel.
need 5.
need A :- need N, N > 1, A = N - 1.
?- inside E.
?- need N.
```

```output
?- inside E.
E = neg (neg (num 3)).
E = neg (num 3).
E = num 3.
?- need N.
N = 1.
N = 2.
N = 3.
N = 4.
N = 5.
```

Without the comparison `N > 1`, nothing bounds `A` below, and the component is rejected.

```hugin,compile_fail,E0603
need : int -> rel.
need 5.
need A :- need N, A = N - 1.
```

Increases toward an upper bound are descents read upwards: `step M :- step N, N < 6, M = N + 1` is
accepted, since `M` is larger than `N` and bounded above by 6.

## Guarded induction (B)

A *measure* assigns to each relation of the component a tuple of argument positions. All tuples have
the same length, and each slot is an integer slot, ordered by `<`, or a structural slot, ordered by the
proper subterm relation. Tuples are compared lexicographically.

The component satisfies (B) with a measure if

1. the rules of relations without a measure are not constructive;
2. for every rule with a head `c h̄` of a measured relation `c`, every body atom `d s̄` of the component
   is of a measured relation, and the measure of `d s̄` is lexicographically smaller than that of `c h̄`,
   at some slot `i`;
3. the head's measure lies in a finite set, its *anchor*: slot `i` is bounded above, and every later slot
   is bounded above and below. A slot is bounded if its variables are bound by finite sources, by an
   interval, or by the call's slot plus a bounded difference. A structural slot must be bound by a
   relation outside the component.

Then every value of the measure has finitely many facts, and finitely many values of the measure occur,
by well-founded induction on the measure.

The compiler infers a measure: one argument per relation (for up to four relations, at most 256
combinations) and, for a component with a single relation, every lexicographic pair of arguments.

The following type checker is accepted by (B) with the inferred measure `e` on `typed`. Each recursive
call is on a proper subterm of the head's expression, and the head's expression is bound by `check`, a
finite source.

```hugin,run
expr : type.
lit : int -> expr.
pair : expr -> expr -> expr.
typ : type.
tint : typ.
tpair : typ -> typ -> typ.
check : expr -> rel.
check (pair (lit 1) (pair (lit 2) (lit 3))).
check A :- check (pair A _).
check B :- check (pair _ B).
typed : (e : expr) -> (t : typ) -> rel.
typed (lit N) tint :- check (lit N).
typed (pair A B) (tpair S T) :- check (pair A B), typed A S, typed B T.
?- typed (pair (lit 1) (pair (lit 2) (lit 3))) T.
```

```output
?- typed (pair (lit 1) (pair (lit 2) (lit 3))) T.
T = tpair tint (tpair tint tint).
```

## Declared measures

```text
Terminates ::= "%terminates" Measure Target "."
Measure    ::= VAR | NAME | "(" VAR ("," VAR)* ")" | "(" NAME ("," NAME)* ")"
Target     ::= "(" QualifiedName Term* ")" | QualifiedName
```

`%terminates X (r … X …)` names the argument of `r` at the position of `X` as its measure;
`%terminates l r` names the column labelled `l`. A tuple `(X, Y)` or `(l, m)` declares a lexicographic
measure. The directive is a hint: guarded induction is checked with the declared measure, and it is an
error ([E0604](../errors/E0604.md)) if the check fails. It is an error ([E0701](../errors/E0701.md)) if a
variable or label occurs twice in a measure, or a label is not a column of the relation.

The following program declares a lexicographic measure for a grid walk that moves right within a row
and then down to the next row.

```hugin,run
cell : int -> int -> rel.
%terminates (I, J) (cell I J).
cell 0 0.
cell I J :- cell I K, K >= 0, K < 2, J = K + 1.
cell I J :- cell H K, H < 2, K >= 0, K <= 2, I = H + 1, J = 0.
?- cell 2 J.
```

```output
?- cell 2 J.
J = 0.
J = 1.
J = 2.
```

## Diagnostics

The error [E0603](../errors/E0603.md) names a constructive rule of the component and the recursion. It
says why (A) fails: a cycle of steps without a strict decrease. It says why (B) fails: the first
candidate measure that decreases but has no anchor, or the absence of a decreasing argument. Its help
suggests a comparison when an integer decreases without a bound.

## Limitation

> **Limitation.** A component in which some relations need (A) and others need (B) is rejected. This
> happens when a [demand relation](../directives.md#demand) needs an answer of the relation it guards: in
> Ackermann's function with `%demand ack +m +n -r`, the input `R1` of the call `ack (M - 1) R1 R` is an
> answer of the call `ack M (N - 1) R1`, so `ack.check` and `ack` form one component. The demand rules
> descend (A), the answer rules are guarded by them (B), and the component is reported with
> [E0603](../errors/E0603.md) and a note naming the mixed component.

> **Rationale.** Plain Datalog terminates because it has no value invention. Once constructors and
> arithmetic exist, termination needs a check in any language. The check follows the size-change
> principle (Lee et al. 2001) in two directions, so that both demand relations, which descend, and the
> relations they guard, which are bounded by their guard, are accepted without annotations.
