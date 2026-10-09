# `where`

A clause may end with a `where` block of local definitions. The definitions are in scope in the
clause's right-hand side and in the definitions after them, and they see the clause's pattern variables.
This chapter defines the syntax, the layout rule and the three kinds of local definitions.

## Syntax

```text
Clause    ::= NAME Pattern* "=" Expr "where" LocalItem+
LocalItem ::= NAME "=" Expr "."                      (a definition)
            | NAME ":" Type "=" Expr "."             (a definition with a type)
            | NAME ":" Type "." Clause+              (a local function)
            | NAME VAR* "=" Expr "."                 (a pattern binding or a clause)
```

`where` follows the right-hand side of the clause directly, without a period; the period of the last
local item ends the clause. The first local item may follow `where` on the same line. A definition
`f X₁ … Xₙ = e where …` whose patterns are all variables is a clause as well.

## Layout

The block consists of the items after `where` that start at a column greater than the column at which the
clause starts. It ends before the first item that starts at that column or to the left of it, at a `}` or
at the end of the file. For a clause at the top level of a file, the block ends at the next item in
column 0. A local function's clauses may have `where` blocks of their own, under the same rule relative
to their own column.

## Local definitions

The items of a `where` block are elaborated in order, at each leaf of the clause's case tree.

- A *definition* `x = e.` or `x : A = e.` binds `x` to the value of `e`.
- A *local function* `f : A.` followed by its clauses is a function by clauses like a top-level one. It
  is checked for [coverage](coverage.md) and [termination](termination.md), and it may use the pattern
  variables of the enclosing clause.
- A *pattern binding* `c x₁ … xₙ = e.`, where `c` is a meta constructor, binds the names `xᵢ` to the
  arguments of the value of `e`. The pattern must be irrefutable: it is an error
  ([E0911](../errors/E0911.md)) if the type of `e` has another constructor. It is an error
  ([E0915](../errors/E0915.md)) if the type of a field depends on another field.

The following program uses all three kinds. `fibPair` binds the components of the previous pair by a
pattern binding, `area` names two values, and `addTo` has a local function that refers to the pattern
variable `K` of its clause.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
pair : Type -> Type -> Type.
mkPair : A -> B -> pair A B.
fst : pair int int -> int.
fst (mkPair X _) = X.
fibPair : nat -> pair int int.
fibPair zero = mkPair 0 1.
fibPair (suc N) = mkPair b (a + b)
  where mkPair a b = fibPair N.
shape : Type.
rect : int -> int -> shape.
area : shape -> int.
area (rect W H) = w * h
  where w = W + 1.
        h = H + 1.
addTo : int -> nat -> int.
addTo K M = go M
  where go : nat -> int.
        go zero = K.
        go (suc N) = go N + 1.
answer : string -> int -> rel.
answer "fib" (fst (fibPair 20)).
answer "area" (area (rect 5 6)).
answer "add" (addTo 40 2).
```

```output
answer "add" 42.
answer "area" 42.
answer "fib" 6765.
```
