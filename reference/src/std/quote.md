# `std/quote`

The module `std/quote` is the *code bridge*: it converts between object code `⇑A`
([Staging](../meta/staging.md)), which a program can build and splice but not take apart, and the
reflective syntax of [`std/reflect`](reflect.md) ([Reflection](../reflection.md)), which it can take
apart. A program writes `%use "std/quote".`

| declaration | meaning |
|---|---|
| `quote : {A : ⇑type} -> ⇑A -> quoted A.` | the data of object code of type `A` |
| `unquote : {A : ⇑type} -> quoted A -> ⇑A.` | the object code that closed data describes |
| `quoteF : ⇑prop -> formula.` | the data of a formula, such as the result of a formula function |
| `unquoteF : formula -> ⇑prop.` | the formula that closed data describes |
| `symOf : {R : ⇑type} -> ⇑R -> sym.` | the symbol of the code of an object constant |
| `quoteUnquote : {A : ⇑type} -> (c : ⇑A) -> eq (quote (unquote (quote c))) (quote c).` | the converse round trip on the data of code, by `refl` |
| `quoteUnquoteF` | the same for formulas |

The first five are trusted primitives ([Consistency](../meta/consistency.md#assumptions)); the two
lemmas are proved by `refl`.

## Quoting

`quote c` is computed on *canonical* code, structurally:

- an object constant applied to terms is `tapp` of its symbol and the data of the terms; a constant of a
  family is its instance (`cons[int]`), as [staging](../meta/staging.md) creates it;
- a literal is `tint`, `tfloat` or `tstr`, and a persisted meta value is its literal (`quote ⟨$k⟩` is
  `qterm (tint k)`);
- object arithmetic is `tarith` and `tneg`; arithmetic on two literals is computed where the code is
  built, so `quote ⟨1 + 2⟩` is `qterm (tint 3)`;
- `as`, an ascription, a projection and an update are `tas`, `tascribe`, `tproj` and `twith`;
- `quoteF` turns conjunctions, disjunctions, negations, comparisons and atoms into `fconj`, `fdisj`,
  `fnot`, `fcmp` and `fatom`, a conjunction or disjunction of more than two formulas nested to the left as
  `a, b, c` is read, and an aggregate into `fagg`, whose variable is a `tbound` index.

Positions are dropped. A variable that hygiene names, such as a variable of a
[formula function](../meta/staging.md#formula-functions) (`X#k`), is named by its first occurrence in
the code: the first such variable gets the number 0, the next one 1, and so on (`X#0`, `Y#1`), so the
data does not depend on how many formula functions were applied before.

`quote` is stuck on code that is not canonical: a variable of type `⇑A`, a splice of a meta application
that does not reduce, or a family whose type arguments are not known. It never decides anything about
code it cannot see.

## Unquoting

`unquote q` is the code that the closed data `q` describes, the inverse of `quote` on canonical code:
`unquote (quote (<circle 3>))` evaluates to `<circle 3>`. `unquote` types nothing: the code is typed where
it is staged, as reflected data is ([Reflecting data into the program](../reflection.md#reflecting-data-into-the-program)).
It is stuck on data that is not closed, such as a variable. A meta integer outside the object level's 64
bits becomes a persisted value, which staging reports ([E0930](../errors/E0930.md)).

The round trip `unquote (quote c)` is `c` for every `c`, also for a variable: on a stuck `quote c`,
`unquote` reduces to `c`, as `$⟨t⟩` is `t` ([Staging](../meta/staging.md)). The same holds for `unquoteF`
and `quoteF`. A formula with variables named by hygiene comes back with their names by first
occurrence, so `unquoteF (quoteF f)` evaluates to `f` with these variables renamed.

The converse, `quote (unquote q)` is `q`, holds for the data of code: `quoteUnquote c` proves it for
`q = quote c` by `refl`, by computation on canonical code and by the round trip above on a variable. It
does not hold for data in general, and is no conversion rule: data built by `qterm` may describe code
of another type, or arithmetic on two literals, whose code is computed:
`quote (unquote (qterm (tarith oadd (tint 1) (tint 2))))` is `qterm (tint 3)`.

## Code in quotes, and quoted terms as code

With the code bridge loaded, a hole `$c` of a quote whose value is object code `⇑A` stands for
`$(quote c)`, a term of type `A`; one whose value is a formula `⇑prop` stands for `$(quoteF c)`
([Quotes](../reflection.md#quotes)). A quoted term `q : quoted A` is accepted where object code `⇑B` is
expected if `A` is a subtype of `B`, and `unquote q` is inserted. In object code, a quoted term whose data
depends on a variable is `unquote q` as well; closed data is reflected where it is elaborated, as without
the code bridge ([Typed terms](../reflection.md#typed-terms)). `quote` is never inserted elsewhere: a
program says where it inspects code.

The following program checks the equations of `quote` and `unquote` by `refl`, takes the formula of a
formula function apart, puts object code into a quote, and uses a quoted term as object code.

```hugin,run
%use "std/reflect".
%use "std/eq" (eq, refl).
%use "std/quote".
city : type. berlin, paris : city.
road : city -> city -> rel.
shape : type.
circle : (r : int) -> shape.
q1 : eq (quote (<circle 3>)) (qterm (tapp '( circle ) [tint 3])) = refl.
q2 : eq (unquote (quote (<circle 3>))) (<circle 3>) = refl.
q3 : (c : ⇑shape) -> eq (unquote (quote c)) c = [c] refl.
linked : city -> prop.
linked X :- road X _.
q4 : eq (quoteF (linked berlin))
  (fconj (fcmp ceq (tapp '( berlin ) []) (tvar "X#0")) (fatom '( road ) [tvar "X#0", twild])) = refl.
q5 : eq (symOf road) '( road ) = refl.
toParis : ⇑city -> formula = [c] '( road $c paris ).
q6 : eq (toParis (<berlin>)) '( road berlin paris ) = refl.
asCode : quoted city -> ⇑city = [q] q.
start : ⇑city = asCode '( paris ).
road $start berlin.
%opaque q1 q2 q3 q4 q5 q6.
%output road.
```

```output
road paris berlin.
```

> **Note.** The bridge follows the "analysable deep embedding" of Kovács's two-level type theory (ICFP
> 2022, §6): the object level has no binders that conversion substitutes into, so equality of object code
> is syntactic and a structural `quote` is stable under the substitutions the meta level performs.
> Lean's `Lean.Expr` quotation and Agda's reflection (`quoteTerm`, `unquote`) are the same pair for a
> language whose terms are its own object of study; MetaOCaml's `'a code` and the `□ A` of layered modal
> type theory keep code opaque, as `⇑A` is here.
