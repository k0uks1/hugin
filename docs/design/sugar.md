# Small syntax sugar: meta naturals, functional and logic conveniences

Design note for [issue #127](https://github.com/k0uks1/hugin/issues/127). Status: approved by the
designer: N1–N5, F1, D1. The other items are not part of #127. N1–N5 land in one pull request, F1 and
D1 in another, each with its reference chapters, error codes, goldens and highlighting.

Contents: 1 Hugin today, 2 meta natural numbers, 3 sugar from functional languages, 4 sugar from Prolog
and Datalog, 5 rejected alternatives, 6 sources, 7 summary.

Measurements were made with scratch programs (not committed) on a build of 348fd8e. Each candidate gives
before and after, prior art, how it interacts with Hugin, its cost and a verdict: **recommend**,
**maybe** (it works, but the gain is small or depends on the designer's taste) or **reject**.

## 1. Hugin today

Several items of the issue exist already. The survey does not propose them again:

| issue item | status | where |
|---|---|---|
| literals `0`, `1`, … for `zero`/`suc` | **exist**, in expressions and patterns, for every *nat-like* family | `meta/families.md#numerals`, `Inductives.scala:164`, `Clauses.scala:120` |
| list literals and patterns `[a, b]`, `x :: xs` | exist, at both stages | `reflection.md#lists`, `std/reflect.md` |
| `xs ++ ys` | exists as the prelude function `append` | `prelude.md` |
| `if` on `bool` | exists as the prelude function `if c a b` (both branches evaluated) | `std/reflect.md` |
| Σ types, tuples | record types are the dependent sums; pairs are `{ fst : A, snd : B }` | `meta/records.md` |
| local functions by clauses | `where` blocks, with coverage and termination | `meta/where.md` |
| record update | exists at the **object** level, `(X with { l = t })`; not for meta records | `object/rules.md#records` |
| record wildcards | object named patterns `r { l = t, .. }` | `object/rules.md#records` |
| disjunction in bodies | exists, `φ ; ψ`, also inside aggregates | `object/rules.md#formulas`, `object/aggregates.md` |
| `\+` | `not` is a keyword; it applies to an atom only (E0202) | `object/negation.md` |
| anonymous variables, singleton warnings | `_`, and W0002 `singleton_variables` unless the name starts with `_` | `object/rules.md#variables` |
| `aggregate_all(count/sum/min/max)` | aggregates `X = count { t \| φ }` etc. | `object/aggregates.md` |
| subsumption (min/max) | bound columns `min τ`, `max τ` (Limit Datalog) | `object/bound-columns.md` |
| transitive closure | the functor `tc` of `std/graph` | `std/graph.md` |

Constraints every candidate must respect:

- **One expression grammar for both levels.** `->` is the arrow of types everywhere, `,` and `;` are
  conjunction and disjunction, `|` is the union of object types and the bar of aggregates, `.` ends an
  item or selects, `[` starts a list or a lambda `[x] e`, `{` a record, module, implicit binder or named
  pattern. A new token or a new meaning of an old one must not change a program that parses today.
- **Column 0** ends an argument, an operand, a lambda body and a body; an infix operator in column 0
  starts the next item. This is what lets the resilient parser report a missing period at the next item.
- **`%infix` takes names only**, never symbols. Users cannot redefine `+`.
- **Staging is inferred**, so a literal's meaning comes from the expected type and the position's stage.
- **Patterns are parsed as expressions** and converted afterwards (`Patterns.scala:52-75`), so a new
  pattern form usually needs no parser change, only a case in `plainPattern`.
- **`_` in a meta expression is an unknown** to be inferred (`pick _ Y refl`), not a placeholder.
- **`?` is a typed hole**, `'(` a reflection quote, `$` a splice or hole, `<t>` a staging quote.
- Every syntax change passes the recovery and fuzz suites (`src/test/scala/hugin/fuzz`), the goldens,
  the reference examples and the TextMate grammar in `editors/vscode`.

## 2. Meta natural numbers

### 2.1 What exists

A family is *nat-like* if it has exactly two constructors, one constant and one with a single argument of
the family itself. A literal `n` checked against it is `suc (… zero)`, in expressions
(`Bidirectional.scala:152`) and in patterns, where `PLit n` is expanded one constructor at a time while
the case tree is built (`Clauses.scala:120-125`), so coverage and size-change termination only ever see
constructor patterns. `index` of `std/reflect` (`izero`, `isuc`) is nat-like too. A literal is limited to
100000 (`Inductives.scala:168`, E0901 "nat literal too large"); the reference does not state the limit.

Gaps, measured:

1. Every program declares `nat : Type. zero : nat. suc : nat -> nat.` itself (15 reference examples do).
2. `toInt (N + 1) = toInt N + 1.` is E0915 "not a pattern".
3. Diagnostics print numerals in full: ``toInt (suc (suc (suc zero))) does not evaluate to a literal``.
4. A literal whose type is still an unknown is taken as `int` at once: with
   `f : {A : Type} -> A -> A -> A`, `f zero 3` elaborates, `f 3 zero` fails.

### 2.2 Recommended design

**N1. `nat` is a library type, opened by the prelude.** A module `std/nat` declares

```hugin,ignore
nat : Type.  zero : nat.  suc : nat -> nat.
plus : nat -> nat -> nat.        (* by clauses on the first argument *)
toInt : nat -> int.              (* by clauses: toInt 0 = 0. toInt (N + 1) = toInt N + 1. *)
```

and the prelude adds `%use "std/nat" (nat, zero, suc).` The rest is imported, as `size` and `iterate`
of #61's `std/list` would import `nat` instead of declaring it (`docs/design/stdlib.md`, section 5.3).
A program that declares its own `nat` shadows the prelude's, so every program keeps compiling; the
reference examples drop their three lines in the same pull request. `nat` stays a meta type: it has no
lifting and no object counterpart (`level zero` remains E0902). Converting to object code is `toInt`,
explicitly. *Prior art:* Agda binds `Nat` by `BUILTIN NATURAL` in `Agda.Builtin.Nat`
(`built-ins.lagda.rst:195-226`), and Idris 2 declares `data Nat = Z | S Nat` in `Prelude.Types`
(`Types.idr:18-22`); in both the library owns the type and the compiler only recognises its shape.

**N2. Keep the structural rule.** Hugin recognises *any* nat-like family, as Idris 2 does for its
`Natural` optimisation ("The data type must have 2 constructors … One must have exactly 1 argument",
`builtins.rst:30-40`); Agda instead requires the shape and a pragma (`built-ins.lagda.rst:208-212`).
Every nat-like family is isomorphic to ℕ, so the rule cannot misread a family, and it keeps `index`
literals working. No pragma is needed.

**N3. The literal rule, stated once.** A literal checked against

1. a nat-like family is its numeral;
2. a base type is a literal of that type, at the stage of the position;
3. an unknown type is *postponed* until the end of its item; if the type is then still unknown, the
   literal is an `int` at the stage of its position.

Clauses 1 and 2 are today's behaviour. Clause 3 replaces "taken as `int` at once" and is Lean's
discipline: `OfNat` resolution waits for the expected type, and `instOfNatNat` is only a
`@[default_instance]` applied when nothing else decides (`Prelude.lean:1396-1405`). Hugin's default
stays `int`, not `nat` as in Lean and Agda, because most literals are object integers and a default
must never change the stage. No ambiguity arises with object `int`: `nat` has no lifting, so a numeral
can never be object code, and an object position never expects `nat`. Postponement uses the per-item
unknowns of #66, which already solve "an item solves its own unknowns".

**N4. Successor patterns `P + k`.** In a pattern, `P + k` with an integer literal `k ≥ 1` against a
nat-like type is `suc` applied `k` times to `P`. In an expression, `e + k` checked against a nat-like
type, or whose left operand has a nat-like type, is the same term. One rule, both sides:

```hugin,ignore
(* before *)                               (* after *)
fib (suc (suc N)) = fib N + fib (suc N).   fib (N + 2) = fib N + fib (N + 1).
```

`+` with a literal right operand is the only form. `m + n` for two naturals stays the function `plus`,
and `N - 1` is not a pattern (it is not a constructor). In the elaborator `plainPattern` gets a case
`Infix("+", p, Lit(k))` that yields a new `Pat.PSucc(p, k)`, expanded in `simplify` exactly like `PLit`,
and `checkArith` gets the nat-like case. The parser does not change: `(N + 1)` already parses as an
argument. Coverage, unreachable clauses (W0006) and size-change termination see `suc (suc N)`, where `N`
is a strict subterm, so `fib` above is accepted for the same reason as today.

*Prior art.* Lean 4 accepts `n+1` patterns: `HAdd.hAdd` is `[match_pattern]` (`Prelude.lean:1905`),
the pattern collector admits `binop%` for that reason (`Elab/PatternVar.lean:257-273`), and literal
patterns become `Nat.zero`/`Nat.succ` constructor patterns lazily (`expandNatValuePattern`,
`Meta/Match/Match.lean:745-753`), the same strategy as Hugin's `PLit`. Haskell 98 had n+k patterns
and called them controversial ("an incongruous language design feature", Haskell 98 report preface,
`preface-13.verb:196-210`); Haskell 2010 removed them ("Removed language features: The (n+k) pattern
syntax", `preface.verb:112-115`); GHC keeps them behind `NPlusKPatterns` (`nk_patterns.rst`). The
reasons given in the Haskell′ process (proposal `RemoveNPlusK`, not read from source for this note) were
that `n+k` matched any `Integral` type through the class methods `>=` and `-`, so matching ran
overloaded user code instead of testing a constructor; that it was the only pattern built from a
function; and that its binding of `n` was surprising next to `+` in expressions. None of these holds in
Hugin: `+` cannot be redefined, the pattern is defined only for nat-like families, where it *is* a
constructor pattern, and the expression form means the same term. Agda has no such pattern; programs
write `suc n` and Agda prints numerals as literals.

**N5. Print numerals as literals.** The printer shows a closed numeral of a nat-like family as its
digits, and `suc^k e` with an open `e` as `e + k`, in diagnostics, `--print-after elaborate`, the REPL
and LSP hovers. Agda does this for its built-in naturals.

**N6. Representation: unary, no change now.** Meta naturals stay terms of `zero` and `suc`, as Agda
and Idris specify theirs. Agda represents closed naturals "as Haskell integers at compile-time" and
gives `_+_`, `_-_`, `_==_` both a definition by clauses and a primitive (`built-ins.lagda.rst:213-240`);
Idris 2 does the same at run time (`builtins.rst:30-55`). Hugin's meta code only runs at compile time,
on small numbers (fuel, sizes, indices), and the evaluator memoises. A packed representation
(`Val.NatLit n`, unfolded one `suc` at a time when a case tree splits on it) can follow if a benchmark
asks for it; it changes no rule. The limit of 100000 stays and is stated in `meta/families.md`.

*Cost.* N1: one library file, prelude, reference edits (`prelude.md`, `std/`, examples). N3: a
postponed-literal unknown in `Bidirectional`. N4: two elaborator cases, no parser change, reference
`meta/clauses.md` and `meta/functions.md`, goldens for coverage and SCT. N5: printer only. No new
token, no highlighting change, no new error code. **Recommend N1-N5.**

## 3. Sugar from functional languages

### F1. Record update for meta records: `(r with { l = e })` — recommend

```hugin,ignore
(* before *)  moved : point = { x = 5, y = p.y }.
(* after *)   moved : point = (p with { x = 5 }).
```

The object level already has `(X with { l = t })` for facts (`object/rules.md#records`) and `with` is
a keyword. The same syntax for meta records makes one notation for both levels. It means the record
value with the field `l` replaced and the other fields projected from `r`; the result is checked like
that record value, so updating a field on which a later field depends is accepted only if the later
field still has its type. Since modules are records, it also adjusts a module or signature argument:
`tc (g with { edge = road })`. Probe: `p with { x = 5 }` in a definition is E0001 today.
*Prior art:* OCaml `{ e with f = v }` (manual, "Records"), Haskell 2010 record update `e { f = v }`
(report, section 3.15.3), Agda `record r { f = e }`, "expanded before type checking"
(`record-types.lagda.rst:359-405`), Lean 4 `{ s with x := v }`, Gleam `Rec(..r, f: v)`
(`chapter3_data_types/lesson05_record_updates`), Roc `{ r & f: v }`. *Cost:* the parser already reads
the object form; the elaborator expands it to a record value. Reference `meta/records.md`.

### F2. Several binders in a lambda: `[x y] e` — maybe

`[x] [y] x + y` would be `[x y] x + y`. Agda `λ x y → e`, Lean `fun x y => e`, Haskell `\x y -> e`.
Today `[x y]` followed by an operand reads as a list applied to it, which never type-checks, so no valid
program changes; but the list/lambda decision already looks at the token after `]`, and this widens it
to a bracket holding several names. The gain is two characters per binder. Maybe.

### F3. Writing implicit arguments: `f {A = int}` — maybe

Implicit arguments cannot be written explicitly today (`meta/functions.md#implicit-arguments`). Agda
and Idris 2 write `f {A = int}`, Lean `f (A := int)`. In Hugin `{` followed by a *variable* and `=` is
free (record fields are names), so the form is unambiguous. It is an expressiveness gain rather than
sugar, useful when unification cannot determine an argument (E0903). Maybe, as a separate issue.

### Rejected

- **`if c then a else b`.** `if` is a prelude function, and Agda too writes `if_then_else_` as a library
  mixfix, not syntax. Keywords `then`/`else` would break programs that use the names, and would give one
  operation two spellings. If evaluating both branches is a cost, `if` can become lazy in its branches in
  the evaluator, without syntax.
- **Anonymous-function shorthand** (Scala 3 `_ + 1`, Gleam `f(_, 1)`, `lesson04_function_captures`).
  `_` in a meta expression is an inferred unknown; the meaning would depend on the context.
- **Operator sections** `(+ 1)`. `-` is prefix and binary, so `(- 1)` is the Haskell wart again; `%infix`
  operators are names. `[x] x + 1` is short.
- **Tuple syntax `(a, b)`.** `,` is conjunction and the measure syntax `(X, Y)`; records are the Σ type.
- **`case`/`match` expressions, pattern lambdas.** GHC `\case` (`lambda_case.rst:7-26`), Agda `λ where`
  (`lambda-abstraction.lagda.rst:137-160`), Lean `fun | 0 => … | n+1 => …`. A `where` function is
  Agda's `λ where` with a name, and gets coverage and termination for free. A case expression would need
  its own layout inside an expression, against the column-0 rule.
- **Multi-way if and guards** (GHC `MultiWayIf`, `multiway_if.rst:16`). The meta level has no
  comparisons; guards would only test `bool` functions, which `if` does.
- **`++` and other symbolic operators.** A new token, where `append` exists and `%infix` admits only
  names; `%infix right 4 append.` already gives `xs append ys`.
- **Pipelines `|>`** (Gleam, Roc, OCaml, Koka's dot calls). `|` and `.` are taken; application is
  juxtaposition.
- **`OverloadedLists`**: list syntax already resolves by stage to the one shared `list`.
- **do-notation**: there is no monad.

## 4. Sugar from Prolog and Datalog

### D1. Several names in one declaration: `ann, bob, cy : person.` — recommend

```hugin,ignore
(* before *)  red : color.  green : color.  blue : color.
(* after *)   red, green, blue : color.
```

Enumerations are the commonest object declarations in the reference and the examples. The item means
one declaration per name, with the same type and the same prefix directive. It is valid for
declarations without a definition only. Probe: E0001 "expected `.`, `,` or `:-`, found `:`" today. A
rule with several heads, `p, q :- r.`, also starts with names and commas; the parser decides at the
token after the list (`:` or `:-`), which is the decision it already makes for one name. *Prior art:*
Soufflé `.decl A, B(x:number, y:number)` (`pages/docs/rules.md:17`), Haskell 2010 signatures
`vars :: type` (report, section 4.4.1), Agda `postulate a b : A` and fields `x y : A`, Lean
`variable (a b : Nat)`. *Cost:* parser (declaration head), recovery goldens for a missing name after a
comma, reference `object/declarations.md`; the LSP reports each name at its own span. Recommend.

### D2. Negation of a conjunction: `not (φ)` — maybe

```hugin,ignore
(* before *)  reaches_safe X :- node X, not unsafe_reach X.
              unsafe_reach X :- edge X Y, bad Y.
(* after *)   reaches_safe X :- node X, not (edge X Y, bad Y).
```

`not` applies to an atom only (E0202). Allowing a parenthesised formula, compiled like a disjunction in
an aggregate (an auxiliary relation over the variables bound before it; the others are local), is the
general form behind three requests of the issue: if-then-else is `(C, T) ; (not (C), E)`, CodeQL's
`forall(x | φ | ψ)` is `not (φ, not ψ)`, and Prolog's `\+ (A, B)`. Stratification is unchanged: the
auxiliary relation is negated, so its relations must be complete and in earlier components. *Prior
art:* CodeQL `not` on any formula, `forall` "logically the same as `not exists(… | not …)`"
(`ql-language-reference/formulas.rst:244-262`), `if A then B else C` "the same as `(A and B) or ((not A)
and C)`" (`formulas.rst:398-402`); Logica `~` on a proposition (`docs/syntax.md:125`); Soufflé allows
`!` on atoms only (`pages/docs/rules.md:175`); Rel has `not`, `exists` and `forall` on formulas
(manual). *Cost:* elaborator (the aggregate's auxiliary-relation code, reused), range restriction,
reference `object/negation.md`; no new token. Maybe: it removes helper relations, but it hides a
stratum behind parentheses.

### D3. A bounded range of integers — maybe, as a library relation, not syntax

`between L H X` binds `X` to each integer from `L` to `H` when `L` and `H` are bound (SWI-Prolog
`between/3`, `man/builtin.plx:9022`; Soufflé `range(bgn, end)`, `pages/docs/aggregates.md:112-141`;
CodeQL `[3 .. 7]`, `expressions.rst:93-100`). In Hugin it can be a relation of a library module, written
with guarded induction and `%demand between +lo +hi -x`, so its termination argument is the existing
one. A syntax `X in [L .. H]` would overload the list brackets and `..` of named patterns and holes.
Maybe, in `std/` with #61.

### Rejected

- **`[H | T]` list notation** (ISO Prolog 6.3.5). `H :: T` exists at both stages; `|` already means
  union and the aggregate bar. A second spelling for one constructor.
- **`\+`.** `not` exists; `\` would be a new token.
- **`( C -> T ; E )`.** `->` is the arrow of the shared expression grammar; the probe gives E0901 "expected
  a type". Prolog's `->` also commits to the first solution of `C` (`man/builtin.plx:2429-2450`), which
  has no meaning bottom-up. The logical reading is D2.
- **`findall`/`aggregate_all(bag)`, collecting a list** (`man/builtin.plx:10259`, `library/aggregate.pl`;
  Logica `List=`). The list's order is not determined by the database, and a list is a fact with an
  identity, so the result would depend on evaluation order. Count, sum, min and max exist.
- **DCG rules** (`man/builtin.plx:3900`). Difference lists are top-down parsing; a Hugin program that
  wants grammar rules can write a directive over quotes, as `%demand` is written.
- **Soufflé choice domains** (`pages/docs/choice.md:19-40`). The choice of a tuple is nondeterministic;
  Hugin's database is unique.
- **Soufflé subsumption** `A <= B :- …` (`pages/docs/subsumption.md:16-21`). Bound columns cover the
  lattice case with the theory of Limit Datalog; general subsumption deletes facts, which is not
  monotone. Flix's lattice semantics (`flixbook/src/lattice-semantics.md`) is the same split.
- **CodeQL closures `p+`, `p*`** (`recursion.rst:73-110`). The functors `tc` of `std/graph` compose, a
  suffix operator would collide with `+`.
- **More anonymous variables.** `_` and `_name` with W0002 cover Prolog's conventions exactly. A lint
  for unused pattern variables of meta clauses (GHC `-Wunused-matches`) would be a separate issue.

## 5. Rejected alternatives for part 1

- **Default literals to `nat`** (Agda, Lean). Most literals are object integers; a default that picks a
  meta type would make `r 3` depend on whether `nat` is in scope.
- **Lift `nat` to object `int`.** A lifting maps `τ` to `⇑τ⁰` of the same type; a numeric conversion
  hidden in staging would make `level zero` legal and `toInt` invisible.
- **A pragma `%builtin natural nat`.** The structural rule is enough (N2), and the pragma would be a second
  way to get the same literals.
- **`nat` merged with `index`.** Rejected in #61 (`docs/design/stdlib.md`, section 10), for the
  reflection data's constructor names; literals already work for both.

## 6. Sources

Shallow clones (`--depth 1`, sparse) made on 2026-10-10 in the scratchpad:

- agda/agda 192e0d4: `doc/user-manual/language/built-ins.lagda.rst` (195-240, "Natural numbers"),
  `literal-overloading.lagda.rst` (31-55, `FROMNAT`), `record-types.lagda.rst` (359-405),
  `lambda-abstraction.lagda.rst` (137-160).
- idris-lang/Idris2 1c630e6: `docs/source/reference/builtins.rst` (10-55), `libs/prelude/Prelude/Types.idr`
  (18-22, 60-72).
- leanprover/lean4 b8182f6: `src/Init/Prelude.lean` (1396-1405 `OfNat`, 1905 `match_pattern`),
  `src/Lean/Elab/PatternVar.lean` (257-273), `src/Lean/Meta/Match/Match.lean` (745-753).
- haskell/haskell-report f6a7d73: `report/preface.verb` (100-115), `report/preface-13.verb` (194-210).
- ghc/ghc e7cacf5: `docs/users_guide/exts/` `nk_patterns.rst`, `lambda_case.rst`, `multiway_if.rst`,
  `record_wildcards.rst`, `overloaded_lists.rst`.
- SWI-Prolog/swipl-devel 884c31e: `man/builtin.plx` (2429-2450 if-then-else, 3900 DCG, 9022 `between/3`,
  10259 `findall/3`), `library/aggregate.pl` (173-191).
- souffle-lang/souffle-lang.github.io 95fe314: `pages/docs/rules.md`, `choice.md`, `subsumption.md`,
  `aggregates.md`.
- github/codeql b5b8165: `docs/codeql/ql-language-reference/formulas.rst`, `expressions.rst`, `recursion.rst`.
- flix/book fffb5ca: `src/fixpoints.md`, `src/lattice-semantics.md`. EvgSkv/logica 8356e23:
  `docs/syntax.md`. gleam-lang/language-tour 234cb02: `chapter1_functions/lesson04_function_captures`,
  `chapter3_data_types/lesson05_record_updates`. koka-lang/koka 9c55695: `doc/spec/tour.kk.md` (107-241,
  trailing lambdas and `with`).
- Not read from source, cited from their published manuals only: OCaml (records), Scala 3 (placeholder
  syntax), Roc (record update, pipelines), Rel, the Haskell′ proposal `RemoveNPlusK`.
- Hugin 348fd8e: `core/elab/Inductives.scala`, `Bidirectional.scala`, `Clauses.scala`, `Patterns.scala`,
  `TypeProblems.scala`; `docs/design/stdlib.md` (#61).

## 7. Summary

| # | candidate | prior art | verdict | reason |
|---|---|---|---|---|
| N1 | `nat` in `std/nat`, prelude opens `nat, zero, suc` | Agda `Agda.Builtin.Nat`, Idris 2 `Prelude.Types` | recommend | removes three lines from every program; shadowing keeps old programs valid |
| N2 | keep the structural nat-like rule | Idris 2 `Natural` shape rule | recommend | every nat-like family is ℕ; `index` keeps its literals |
| N3 | postpone literals at unknown types, default `int` | Lean `OfNat` + `default_instance` | recommend | `f 3 zero` works; the default never changes stage |
| N4 | `P + k` patterns and `e + k` expressions on nat-like types | Lean `n+1` (`match_pattern`); Haskell 2010 removed n+k | recommend | a constructor pattern, not overloaded: Haskell's objections do not apply; SCT/coverage unchanged |
| N5 | print numerals as digits | Agda | recommend | printer-only, readable diagnostics |
| N6 | packed nat representation | Agda, Idris 2 big integers | not now | compile-time numbers are small; no rule changes later |
| F1 | meta record update `(r with { l = e })` | OCaml, Haskell, Agda, Lean, Gleam, Roc | recommend | same syntax as the object level; adjusts module arguments |
| F2 | `[x y] e` | Agda, Lean, Haskell | maybe | small gain, widens the list/lambda decision |
| F3 | explicit implicit arguments `f {A = int}` | Agda, Idris 2, Lean | maybe | expressiveness, not sugar; separate issue |
| F4 | `if then else` syntax | Agda keeps it a library mixfix | reject | `if` exists; new keywords |
| F5 | `_ + 1`, captures, sections | Scala 3, Gleam, Haskell | reject | `_` is an unknown; `-` is ambiguous |
| F6 | tuples `(a, b)` | ML family | reject | `,` is conjunction; records are Σ |
| F7 | `case`/`\case`/pattern lambdas | GHC, Agda `λ where`, Lean | reject | `where` functions already; layout clash |
| F8 | multi-way if, guards | GHC `MultiWayIf` | reject | no meta comparisons |
| F9 | `++`, `\|>`, symbolic operators | Haskell, Gleam, Roc | reject | new tokens; `append` exists |
| F10 | `OverloadedLists`, do-notation | GHC | reject | lists resolve by stage; no monad |
| D1 | `a, b, c : t.` | Soufflé `.decl A, B`, Haskell, Agda, Lean | recommend | enumerations everywhere; decided at the same token as today |
| D2 | `not (φ)` on a conjunction | CodeQL `not`/`forall`/`if`, Logica `~` | maybe | subsumes if-then-else and `forall`; hides a stratum |
| D3 | `between L H X` as a library relation | SWI `between/3`, Soufflé `range`, CodeQL `[a .. b]` | maybe | needs no syntax; termination by guarded induction |
| D4 | `[H \| T]` | ISO Prolog | reject | `::` exists; `\|` taken |
| D5 | `\+` | ISO Prolog | reject | `not` exists |
| D6 | `( C -> T ; E )` | ISO Prolog, SWI | reject | `->` is the arrow; committed choice has no bottom-up meaning |
| D7 | `findall`, list aggregates | SWI, Logica `List=` | reject | order-dependent result |
| D8 | DCG rules | SWI | reject | top-down idiom; a directive can provide it |
| D9 | choice domains | Soufflé | reject | nondeterministic |
| D10 | general subsumption | Soufflé, Flix lattices | reject | bound columns cover the monotone case |
| D11 | closures `p+`, `p*` | CodeQL | reject | `std/graph` functors |
| D12 | more anonymous variables | Prolog | exists | `_`, `_name`, W0002 |
| D13 | disjunction in bodies | Soufflé, Prolog | exists | `;`, also inside aggregates |

## 8. Implementation of N1–N5

Re-measured on the base of the pull request (186694b) before implementing: every gap of 2.1 and every
probe of F1 and D1 holds as described, except that `(p with { x = 5 })` with a lowercase `p` is
E0001 "expected a variable" today (the parser reads the object form), not a type error.

- **N1.** `std/nat` declares `nat`, `zero`, `suc`, `plus` and `toInt`; the prelude adds
  `%use "std/nat" (nat, zero, suc).` `plus` recurses on its *second* argument (as Lean's `Nat.add`), so
  that `plus N k` reduces to `N + k` for an open `N`, the same term as N4's expression form; this keeps
  the door open for a primitive representation (#131). Both functions are plain clause definitions.
  `std/nat` declares no object constants, but `std/list` imports it, so it is elaborated with the
  prelude's chain (docs/PERFORMANCE.md).
- **N3.** A literal checked against an unknown meta type is an unknown, resolved at the end of its item,
  of a module member, or before a definition is stored (`core/elab/Literals.scala`), and earlier where
  the item needs a value of a type not yet known: before such a value is taken as object code (the
  Lift rule's fallback "a meta value of unknown type is object code") and before a value is reflected as
  syntax. An integer literal next to an operand of unknown type in arithmetic makes it `int` at once
  (`[x] x * 10`). Without these two, the polymorphic functions of #61's `std/list` (`foldr ([x] [s] x - s)
  0 [10, 4, 1]` in a rule) took their unknowns as object code. A type mismatch found before the end of
  the item may show the literal's type as an unknown (`vec ?0 1`).
- `std/list` (#61) declared its own `nat`; it now opens the one of `std/nat`. Since `std/list` is in the
  prelude's chain (`std/demand` imports it), `std/nat` stays in every chain rather than being lazy.
- **N4.** `Pat.PSucc` and the expression cases in `Bidirectional`/`Operators`; the construction of
  numerals and of `e + k` goes through `core/Naturals.scala` only.
- **N5.** The printer shows `zero` as `0` as well, and `suc^k e` as `e + k` also in suggested clauses
  (`f.g (_ + 1)`), which are valid patterns.
