# `match` and `rewrite`

`match` is the case expression of the meta level: it splits a value into the cases of its type, as the
[clauses](clauses.md) of a function do, but on the right-hand side. When the expected type mentions the
value, `match` abstracts it there, so that each branch sees the goal with the branch's pattern in its
place, and it can name the equation between the value and the pattern. `rewrite` changes the expected
type with an equation of [`std/eq`](../std/eq.md). Both are ordinary meta expressions, also outside
proofs. The heads of clauses stay pure patterns.

## Syntax

```text
Expr   ::= … | Match | Rewrite
Match  ::= "match" (VAR ":")? Expr "with" Branch+
Branch ::= "|" Pattern ("=>" Expr)?
Rewrite ::= "rewrite" Expr "in" Expr
```

`match`, `rewrite` and `in` are [keywords](../lexical-structure.md#keywords), and `=>` is a token. The
patterns of a branch are those of [clauses](clauses.md#patterns), except that a branch has one pattern
and that `::` needs no parentheses in it (`| X :: Xs => …`). A branch without `=> e` is an *absurd
branch*: its pattern contains `()`.

`|` ends a branch's pattern and expression, so a union type in a branch is written in parentheses.
The expression of the last branch extends as far as possible, as the body of a lambda does: to the end
of the enclosing expression, the clause's period or its `where`. A `match` in another branch than the
last, or in the middle of an expression, is written in parentheses. The expression after `in` extends
in the same way.

## `match`

`match e with | p₁ => e₁ | … | pₙ => eₙ` evaluates `e` and continues with the first branch whose
pattern matches its value; the pattern variables are bound to the parts of the value, as in a clause.
The branches must cover every value of the type of `e`; it is an error
([E0911](../errors/E0911.md)) if one is missing, and a branch that the branches before it cover is
reported as unreachable ([W0006](../errors/W0006.md)).

A `match` without an expected type is a plain case expression; its type is that of the branches. The
following program uses `match` in ordinary meta code.

```hugin,run
%use "std/list".
describe : nat -> string.
describe N = match N with
  | 0 => "zero"
  | 1 => "one"
  | _ + 2 => "many".
len : list A -> int.
len Xs = match Xs with
  | nil => 0
  | _ :: T => len T + 1.
answer : string -> int -> rel.
answer (describe 1) (len [1, 2, 3]).
answer (describe 7) ((match true with | true => 1 | false => 2) + 1).
```

```output
answer "many" 2.
answer "one" 3.
```

### Abstraction in the goal

When the expected type `G` of the `match` is known, the `match` *abstracts* `e` in it. `G` and `e` are
normalised as [conversion](index.md#meta-types) compares them: definitions are unfolded, and functions
by clauses are applied as far as evaluation takes them. Every subterm of the normal form of `G` that is
equal to the normal form of `e`, up to the names of bound variables, is replaced by a new variable `y`;
this gives the *motive* `[y] G'`. A numeral is not a subterm of another numeral, but `N + k` contains
`N + j` for `j < k` (it is the successor applied `k` times). The branch for `pᵢ` is checked against
`G'` with `pᵢ` for `y`. Only the goal is abstracted: the types of the variables in scope are not.

In the following program the goal of `maxIs M N` unfolds `maxN` to `either (eq (if (less M N) N M) M)
(eq (if (less M N) N M) N)`. The `match` abstracts `less M N`, so the branch `true` is checked against
`either (eq (if true N M) M) (eq (if true N M) N)`, in which `if true N M` evaluates to `N`.

```hugin,run
%use "std/eq".
%use "std/nat".
maxN : nat -> nat -> nat = [m] [n] if (less m n) n m.
maxIs : (m n : nat) -> either (eq (maxN m n) m) (eq (maxN m n) n).
maxIs M N = match less M N with
  | true => right refl
  | false => left refl.
answer : int -> rel.
answer 1.
```

```output
answer 1.
```

### The equation

`match H : e with …` binds `H : eq e pᵢ` in the branch for `pᵢ`, the equation of
[`std/eq`](../std/eq.md) between the scrutinee and the pattern. It is an error
([E0929](../errors/E0929.md)) if the program does not load `std/eq`. In the following program the
second branch refutes `less M N = false` with the hypothesis `H`.

```hugin,run
%use "std/eq".
%use "std/nat".
maxN : nat -> nat -> nat = [m] [n] if (less m n) n m.
below : (m n : nat) -> eq (less m n) true -> eq (maxN m n) n.
below M N H = match E : less M N with
  | true => refl
  | false => absurdBool (trans (sym E) H).
answer : int -> rel.
answer 1.
```

```output
answer 1.
```

### Ill-typed abstractions

Replacing `e` by `y` may leave a term whose type mentions `e` where its function now expects one that
mentions `y`. The abstracted goal is checked again, and it is an error ([E0927](../errors/E0927.md))
if it is ill-typed; the message shows the goal, the abstracted goal, and the argument that no longer
fits. The remedy is a [`where`](where.md)-local function whose type abstracts `e` together with what
depends on it.

```hugin,compile_fail,E0927
%use "std/eq".
%use "std/nat".
p : nat -> Type.
q : (n : nat) -> p n -> Type.
bad : (n : nat) -> (h : p (plus 0 n)) -> q (plus 0 n) h.
bad N H = match plus 0 N with
  | 0 => ?
  | K + 1 => ?.
```

### Elaboration, coverage and termination

A `match` is a function lifted from its context, as a [`where`](where.md)-local function is: with
`A` the type of `e`, it is `m : (y : A) -> {H : eq e y} -> G'` (without `H` when the equation is not
named), whose clauses `m pᵢ {H := H} = eᵢ` are the branches, applied as `m e {refl}`. So the branches
see the variables in scope, and [coverage](coverage.md), unreachable branches and the editor's case
split on a pattern variable are those of the function's clauses. An indexed family needs no branch for a
constructor whose indices cannot unify, and a branch whose pattern is impossible is written as an
absurd branch `| ()`.

For [termination](termination.md), the calls of the branches are calls of the function, and the
`match` is a call of it with the variables in scope (related to themselves) and `e`. So recursion on a
variable of the clause, or on a variable bound by a branch's pattern when `e` is a variable, decreases
as in a clause. In diagnostics the function of a `match` in `f` is `f.match`.

```hugin,run
%use "std/nat".
countdown : nat -> int.
countdown 0 = 0.
countdown (N + 1) = match less N 3 with
  | true => countdown N + 1
  | false => countdown N.
answer : int -> rel.
answer (countdown 6).
```

```output
answer 3.
```

## `rewrite`

`rewrite h in e`, where `h : eq a b` and the expected type `G` is known, abstracts the occurrences of `a`
in the normal form of `G` as `match` does, giving `P = [y] G'`. It checks `e` against `P b` and
elaborates to `subst P (sym h) e` of `std/eq`, of type `P a`, which is `G`. `rewrite sym h in e`
rewrites from right to left. It is an error ([E0928](../errors/E0928.md)) if `h` is not an equation,
if `a` does not occur in the goal, or if the expected type is not known, and an error
([E0927](../errors/E0927.md)) if the abstracted goal is ill-typed.

```hugin,run
%use "std/eq".
%use "std/nat".
zeroPlus : (n : nat) -> eq (plus 0 n) n.
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
twice : (n : nat) -> eq (plus 0 (plus 0 n)) n.
twice N = rewrite zeroPlus N in zeroPlus N.
answer : int -> rel.
answer 1.
```

```output
answer 1.
```

Here the goal `eq (plus 0 (plus 0 N)) N` contains `plus 0 N`, the left side of `zeroPlus N`; with
`N` in its place, the goal is `eq (plus 0 N) N`, which `zeroPlus N` proves.

> **Rationale.** Hugin follows Lean 4's right-hand-side `match` and Idris 2's `rewrite … in`, rather
> than Agda's `with` in clause heads, so that clauses keep the simple checking of
> [Clauses](clauses.md#checking-a-clause). As in Agda, abstraction is syntactic on normal forms, and
> only the goal is abstracted; unlike Agda's `w != e of type A` and Lean's `motive is not type
> correct`, an ill-typed abstraction names the argument that no longer fits.
