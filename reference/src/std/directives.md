# `std/directives`

The module `std/directives` defines what an author of [directives](../directives.md) needs beyond
[`std/reflect`](reflect.md): the parts of rules and modules, the calls of a relation, the binding analysis
of terms and formulas, fresh variable names and errors. It is the binding analysis that
[`%demand`](demand.md) uses. A program opens it with `%use "std/directives".`, next to
`std/reflect` and [`std/list`](list.md).

| declaration | meaning |
|---|---|
| `heads : rule -> list formula` | the heads of a rule |
| `body : rule -> list formula` | the body of a rule |
| `rules : module -> list rule` | the rules of a module, named or not, in order |
| `calls : sym -> formula -> list (list term)` | the arguments of the calls of a relation in a formula, also under `not`, in aggregates and in disjunctions |
| `tvars : term -> list string` | the variables of a term |
| `tsvars : list term -> list string` | the variables of a list of terms |
| `fvars : formula -> list string` | the variables of a formula |
| `fbound : formula -> list string` | the variables that a formula binds |
| `fneeds : formula -> list string` | the variables of a formula that it does not bind |
| `plain : term -> bool` | whether a term has no arithmetic |
| `plains : list term -> bool` | whether no term of a list has arithmetic |
| `fresh : string -> list string -> string` | a variable name from a hint that is not in a list |
| `reject : string -> list item` | the items of a directive that rejects its arguments |

Variables are named by strings, and the lists of variables are in order, with repetitions. The variable
of an aggregate is a de Bruijn index (`tbound`, [Reflection](../reflection.md#quotes)), so neither it nor
an occurrence of it is among the names. A formula *binds* the variables of an atom, the variables of the
sides of an equation that have no arithmetic, the result of an aggregate and the variables that the
conjuncts of a conjunction bind. A negation, a comparison other than `=` and a disjunction bind nothing.
This is the analysis by which a rule's body binds its variables from left to right
([Rules](../object/rules.md)).

## Rules and modules

`heads` gives the heads of a rule, and `body` its body. The following directive records the number of
the heads and of the conjuncts of a rule.

```hugin,run
%use "std/reflect". %use "std/list". %use "std/directives".
edge : int -> int -> rel.
path : int -> int -> rel.
shape : (heads : int) -> (conjuncts : int) -> rel.
measured : rule -> list item.
measured R = '( shape $(length (heads R)) $(length (body R)). ).
%measured '( path X Z :- edge X Y, path Y Z ).
%output shape.
```

```output
shape 1 2.
```

`body` alone gives the conditions of a rule. The following directive counts the negated conjuncts.

```hugin,run
%use "std/reflect". %use "std/list". %use "std/directives".
edge : int -> int -> rel.
negations : int -> rel.
negated : formula -> bool.
negated (fnot F) = true.
negated F = false.
counted : rule -> list item.
counted R = '( negations $(length (filter negated (body R))). ).
%counted '( edge X Y :- edge Y X, not edge X X, not edge Y Y ).
%output negations.
```

```output
negations 2.
```

`rules` gives the rules of a module. The following module-wide directive counts the rules of its file;
a fact is a rule with an empty body.

```hugin,run
%use "std/reflect". %use "std/list". %use "std/directives".
edge : int -> int -> rel.
path : int -> int -> rel.
rule_count : int -> rel.
counted : module -> module.
counted Is = append ('( rule_count $(length (rules Is)). ) : module) Is.
%counted.
edge 1 2.
path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.
%output rule_count.
```

```output
rule_count 3.
```

## Calls

`calls r f` gives the arguments of the calls of `r` in `f`, in order, also those under `not`, in
aggregates and in disjunctions. The following directive counts the calls of a relation.

```hugin,run
%use "std/reflect". %use "std/list". %use "std/directives".
path : int -> int -> rel.
call_count : int -> rel.
counted : sym -> formula -> list item.
counted R F = '( call_count $(length (calls R F)). ).
%counted path (path X Y, not path Y X, N = count { Z | path X Z }).
%output call_count.
```

```output
call_count 3.
```

## Binding analysis

`tvars` gives the variables of a term, and `tsvars` those of a list of terms.

```hugin,run
%use "std/reflect". %use "std/directives".
pt : type. pair : pt -> pt -> pt. leaf : int -> pt.
names : list string -> rel.
named : term -> list item.
named T = '( names $(tvars T). ).
%named (pair (leaf X) (leaf (Y + X))).
%output names.
```

```output
names (cons "X" (cons "Y" (cons "X" nil))).
```

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
names : list string -> rel.
named : formula -> list item.
named (fatom S Ts) = '( names $(tsvars Ts). ).
named F = [].
%named (edge X 3).
%named (edge (X + 1) Y).
%output names.
```

```output
names (cons "X" (cons "Y" nil)).
names (cons "X" nil).
```

`fvars` gives the variables of a formula.

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
names : list string -> rel.
named : formula -> list item.
named F = '( names $(fvars F). ).
%named (edge X Y, not edge Y Z).
%output names.
```

```output
names (cons "X" (cons "Y" (cons "Y" (cons "Z" nil)))).
```

`fbound` gives the variables that a formula binds: here `X` of the equation, whose right side has
arithmetic, and the variables of the atom.

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
names : list string -> rel.
named : formula -> list item.
named F = '( names $(fbound F). ).
%named (X = Y + 1, edge Y Z, X > Z).
%output names.
```

```output
names (cons "X" (cons "Y" (cons "Z" nil))).
```

`fneeds` gives the variables of a formula that it does not bind: those that the formulas before it must
bind.

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
names : list string -> rel.
named : formula -> list item.
named F = '( names $(fneeds F). ).
%named (X = Y + 1, not edge X Z).
%output names.
```

```output
names (cons "Y" (cons "Z" nil)).
```

`plain` tells whether a term has no arithmetic, and `plains` whether no term of a list has.

```hugin,run
%use "std/reflect". %use "std/directives".
pattern : bool -> rel.
checked : term -> list item.
checked T = '( pattern $(plain T). ).
%checked 3.
%checked (X * 2).
%output pattern.
```

```output
pattern false.
pattern true.
```

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
patterns : bool -> rel.
checked : formula -> list item.
checked (fatom S Ts) = '( patterns $(plains Ts). ).
checked F = [].
%checked (edge X 1).
%checked (edge X (1 - X)).
%output patterns.
```

```output
patterns false.
patterns true.
```

## Fresh names and errors

`fresh p xs` is a variable name made from the hint `p` that is not in `xs`: the first of `p#0`, `p#00`,
`p#000`, … that is not in the list. Source syntax cannot write `#` in a name, so a fresh variable cannot
capture a variable of the program. A directive that adds a variable to a rule takes its name from
`fresh` and the rule's variables.

```hugin,run
%use "std/reflect". %use "std/directives".
name : string -> rel.
name (fresh "x" []).
name (fresh "x" ["x#0", "y"]).
%output name.
```

```output
name "x#0".
name "x#00".
```

`reject m` is `[ierror m]`: the items of a directive that rejects its arguments. The error is reported
at the directive ([E1000](../errors/E1000.md)). The following directive states a fact of `edge` for an
atom of `edge` and rejects anything else.

```hugin,run
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
stated : formula -> list item.
stated '( edge $X $Y ) = '( edge $X $Y. ).
stated F = reject "`%stated` expects an atom of `edge`".
%stated (edge 1 2).
%output edge.
```

```output
edge 1 2.
```

```hugin,compile_fail,E1000
%use "std/reflect". %use "std/directives".
edge : int -> int -> rel.
stated : formula -> list item.
stated '( edge $X $Y ) = '( edge $X $Y. ).
stated F = reject "`%stated` expects an atom of `edge`".
%stated (1 < 2).
```
