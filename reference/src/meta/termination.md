# Termination of meta functions

Meta functions terminate on every argument. The compiler checks every function defined by clauses with
the size-change principle (Lee et al. 2001) over the order of meta constructor subterms. A function that
it cannot show to terminate is rejected, and the compiler never evaluates it.

## The criterion

A recursive call `g ā` in a clause of `f` with patterns `p̄` relates each argument `aⱼ` to the patterns:
`aⱼ` is *smaller* than `pᵢ` if it is a variable bound inside the constructor pattern `pᵢ`, such as `N` in
`suc N`; it is *equal* to `pᵢ` if it is the variable `pᵢ` itself. These relations form a *size-change
graph* from the arguments of `f` to those of `g`. The *call graph* of the program has these graphs as its
edges; calls through the local functions of a [`where`](where.md) block are calls of those functions.

The graphs are closed under composition, within each strongly connected component of the call graph. A
function is accepted if every graph `G : f → f` of the closure with `G ; G = G` has a strict decrease from
an argument to itself. This accepts structural recursion, lexicographic recursion such as Ackermann's
function, mutual recursion, and recursion with permuted arguments.

It is an error ([E0912](../errors/E0912.md)) if a function does not satisfy the criterion.

The following function is lexicographic: the first argument decreases, or it stays equal and the second
one decreases.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
ack : nat -> nat -> nat.
ack zero N = suc N.
ack (suc M) zero = ack M (suc zero).
ack (suc M) (suc N) = ack M (ack (suc M) N).
toInt : nat -> int.
toInt zero = 0.
toInt (suc N) = toInt N + 1.
value : int -> rel.
value (toInt (ack 2 3)).
```

```output
value 9.
```

The following function is rejected: its recursive call is on a larger argument.

```hugin,compile_fail,E0912
nat : Type.
zero : nat.
suc : nat -> nat.
grow : nat -> nat.
grow zero = zero.
grow (suc N) = grow (suc (suc N)).
```

> **Note.** Definitions `x = e.` cannot refer to themselves ([E0105](../errors/E0105.md)), and there is
> no general recursion. Together with strict positivity of inductive families and the exclusion of
> `Type : Type`, the check makes every meta computation terminate.
