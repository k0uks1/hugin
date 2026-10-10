# Meta naturals as numbers

Design note for [issue #131](https://github.com/k0uks1/hugin/issues/131): efficient representation and
evaluation of meta naturals, as Agda and Lean 4 do. Status: for the designer's approval. Nothing is
implemented. It builds on #127 (N1 `std/nat`, N2 the shape rule, N4 `P + k`, N5 digits) and coordinates
with #67 (canonical case tree, probes), #66 (glued values) and #61 B3 (the shared `bool`).

Contents: 1 recommendations, 2 conformance, 3 Hugin today, 4 prior art, 5 assessments, 6 alternatives
rejected, 7 effects, 8 batches, 9 benchmark plan, 10 sources.

## 1. Recommendations

1. **A closed numeral is a number.** Core terms and values get `Tm.Nat(fam, n)` and `Val.Nat(fam, n)`
   with `n : BigInt` and `fam` the nat-like family. A closed numeral is always in this form: `zero`
   evaluates to `Nat(fam, 0)` and `suc` applied to `Nat(fam, n)` to `Nat(fam, n + 1)`, as in Agda's
   `reduceNat`. `suc v` for a neutral `v` stays a constructor application.
2. **`zero` and `suc` are views.** Every place that inspects a constructor (case trees, unification,
   index unification, coverage, size change) sees `Nat(fam, n + 1)` as `suc (Nat(fam, n))` and
   `Nat(fam, 0)` as `zero`, one step at a time, as Agda's `constructorForm` and Lean's
   `toCtorIfLit`/`nat_lit_to_constructor` do. No rule of the language changes: the unary model stays the
   specification, and numbers are only its representation.
3. **Binding is by shape, the #127 N2 rule, with no pragma.** Every nat-like family gets numerals,
   including users' families and `index`. Shadowing (#127 N1) needs nothing: the representation is keyed
   by the family's global, not by a name.
4. **Arithmetic is recognised by its equations and checked as in Agda** (5.4). A function by clauses
   whose type and defining equations are those of one of the operations in the table of 5.4 (Agda's set
   plus `toInt`) computes natively when all its arguments are numerals. Otherwise its clauses run.
   Recognition is Agda's `verify` (the defining equations hold definitionally on fresh variables), done
   for every candidate function instead of for a pragma. Comparisons return any family with two
   constant constructors; the equations decide which one is "true". `std/nat` uses #61 B3's shared
   `bool`.
5. **Literal patterns are value splits, not unary chains** (5.3). A literal at the canonical split
   position gives a split by value (Agda's literal branches, Lean's `caseValues`), and coverage uses
   interval probes, so `f 50000 = …` costs one test. Size change compares numerals by value: `m < k` is a
   decrease, the unary subterm order on the representation.
6. **`toInt` is O(1).** A recognised `nat -> int` is native, and lifting its meta `int` into object code
   is O(1) already. A numeral beyond the 64-bit meta `int` leaves `toInt` stuck (as `Math.addExact`
   overflow does today), so no object code is generated from a wrapped value.
7. **The 100000 cap (E0901 "nat literal too large") goes.** Source numerals have the range of integer
   literals; computed numerals are unbounded. A limit on numerals produced by computation is only needed
   for exponentiation, which this design does not add (5.6).
8. **Digits come for free** (#127 N5): `Nat(fam, n)` prints as `n`, and `suc^k e` as `e + k`.
9. **Fix the quadratic walk independently** (3.2): `checkObjectFragments` re-evaluates every argument of
   a constructor chain. It costs 65 s for `n : nat = 50000.` today and should be fixed in batch 1 even
   though numerals remove the chain.

Open decisions for the designer: **O1** recognition of arithmetic by its equations (recommended) or an
Agda-style explicit binding that fails loudly (6); **O2** comparison results: any two-constructor type
(recommended) or only the shared `bool`; **O3** nat literals beyond the 64-bit literal range in the
source; **O4** whether to add Lean's `pow` (then with a size guard, 5.6).

## 2. Conformance

| decision | precedent | citation | match |
|---|---|---|---|
| numeral literal `BigInt` in core terms | Agda `LitNat !Integer`; Lean `Literal.natVal` (GMP) | `Syntax/Literal.hs` 23; `Expr.lean` 20 | match |
| literal carries its family | (one ℕ in Agda and Lean) | — | deviation, needed for the shape rule (several nat-like families) |
| closed numerals canonical as literals, `suc lit ↦ lit+1`, `zero ↦ 0` | Agda `reduceNat`; Lean kernel `reduce_nat` (succ) | `Reduce.hs` 644–660; `type_checker.cpp` 668–680 | match (Lean keeps `Nat.zero` as a constructor but treats it as 0, `is_nat_lit_ext` 603) |
| `zero`/`suc` as views on demand | Agda `constructorForm`; Lean `nat_lit_to_constructor`, `toCtorIfLit` | `Monad/Builtin.hs` 252–259; `inductive.h` 92–93, `inductive.cpp` 1347–1354; `WHNF.lean` 24–30 | match |
| case tree on a numeral: literal branch, then `suc` view | Agda compiled clauses | `CompiledClause/Match.hs` 133–137, 179–184 | match |
| conversion: literal vs `suc v` by one view step | Agda `compareAtom`; Lean `is_def_eq_offset` | `Conversion.hs` 599–604; `type_checker.cpp` 1025–1048 | match |
| index unification with views | Agda LHS unifier | `Rules/LHS/Unify/Types.hs` 54 | match |
| `?m + k = n` solved | Lean `isDefEqOffset` (offset terms `e + k`) | `Offset.lean` 118–160; `ExprDefEq.lean` 2421 | match in effect: `e + k` is `suc^k e` (#127 N4), solved by views; Agda leaves `?m + 1` stuck |
| binding by shape, no pragma | Idris 2 shape flags `ZERO`/`SUCC`; Agda pragma with shape check | `ProcessData.idr` 342–362; `built-ins.lagda.rst` 203–212 | Idris: match. Agda: deviation (no pragma, #127 N2) |
| arithmetic native on literals, clauses otherwise | Agda `Primitive{primClauses}`; Lean kernel/Meta on literals, definition otherwise | `Rules/Builtin.hs` 805–831, `Reduce.hs` 751–755; `type_checker.cpp` 610–622, 1051–1060 | match |
| definitions checked against the operation | Agda `verify` (equations by conversion) | `Rules/Builtin.hs` 475–499, 569–588 | match, applied to candidates instead of a pragma; Lean trusts `@[extern]` (`Prelude.lean` 1885–1898) |
| operation set: Agda's seven plus `toInt` | Agda `NATPLUS` … `NATLESS`; Lean adds `pow`, `gcd`, bitwise, shifts | `Primitive.hs` 885–897; `type_checker.cpp` 683–696, `WHNF.lean` 1011–1033 | Agda: match. Lean: subset |
| comparisons return a two-constructor type | Agda `BUILTIN TRUE/FALSE`; Lean `Bool` (`Nat.beq`, `Nat.ble`) | `Rules/Builtin.hs` 544–565; `Prelude.lean` 1945, 2018 | match in role; the constructors are found by the equations |
| literal patterns: value split plus default | Agda `litBranches`/`SplitLit`; Lean value transition, `caseValues` | `CompiledClause/Compile.hs` 145–161; `Match/Match.lean` 301–306, 675–681, 1048–1050 | match |
| literal mixed with `suc` patterns: one view step | Agda `unLitP`; Lean `expandNatValuePattern` | `Coverage/Match.hs` 389–397; `Match/Match.lean` 336–337, 745–753 | match |
| termination: literal against `suc p` by one view step | Agda `compareTerm'` | `Termination/TermCheck.hs` 1447–1470 | match; `m < k` between literals is a decrease (Agda: unknown), sound in the unary order |
| no numeral cap on literals | Agda none; Lean 128 MB guard (`LEAN_NAT_MAX_SIZE`) | `type_checker.cpp` 30–36, 296–320 | Agda: match. Lean's guard is for `pow`/`shiftLeft`; not needed without them |
| compiled representation | Agda, Lean, Idris 2: big integers | `Rules/Builtin.hs` 662–666; `Prelude.lean` 1351–1354; `Opts/Constructor.idr` 6–7, 124–125 | n/a: meta naturals do not exist at run time; `toInt` is the only exit |
| type checker accelerates, not only a compiler | Agda, Lean: yes; Idris 2: compiler only | `built-ins.lagda.rst` 220; `type_checker.cpp` 728; `builtins.rst` 13–28, no nat case in `Core/Normalise` | Agda, Lean: match. Idris 2: deviation (Hugin's meta level runs only in the elaborator) |

## 3. Hugin today

### 3.1 Code

- `Inductives.natLike` (`core/elab/Inductives.scala` 136–151) is the N2 rule: two constructors, one
  constant and one with a single explicit argument of the family, and no family arguments. `natLiteral`
  (164–170) builds `natTerm`, a fold of `n` `Tm.App(suc, …)`, after E0901 for `n > 100000` and the error
  for `n < 0`. The cap is not in the reference (`meta/families.md` 86–89 says nothing about a limit).
- Literal patterns: `Clauses.simplify` (`core/elab/Clauses.scala` 119–125) rewrites `PLit(n)` to
  `PCon(suc, [PLit(n-1)])`, one step per round, and re-normalises all pending equations in each round
  (`p.norm`, line 106).
- Values (`core/Value.scala`): `Val.Lit(l, st)` with `Literal.IntL(Long)` is the meta and object `int`;
  numerals are `Rigid(Glob(suc), …)` chains. `Val.Top` (#66) folds definitions with an eagerly computed
  `Unfold`. Meta `int` arithmetic is `Prims.arith` with `Math.addExact` etc.: overflow leaves the term
  stuck (`obj/Prims.scala` 8–28). `persist` turns a meta literal into an object literal in O(1)
  (`core/Evaluation.scala` 180–181).
- Evaluation: `Matching.reduceFunction` memoises closed applications by hash-consed normal forms
  (`MemoKeys`); `runTree` (`core/Matching.scala` 57–70) splits by `forceData` and the constructor id;
  `SplitAtom` already splits on meta literals by value (quoted patterns).
- Unification (`core/Unification.scala` 187–275): smalltt's `Rigid`/`Flex`/`Full` states over `Top`;
  `(Lit, Lit)` by equality; constructor applications by `unifySp`, recursively per `suc`.
- Primitives: `x : A = %builtin p.` declares a `GlobalKind.Primitive(op, ctors)` whose `bool`
  constructors come from its type (`core/elab/Declarations.scala` 171–175, `core/Primitives.scala`), as
  for `same`. It replaces a definition; there are no clauses behind it.
- Size change (`core/elab/SizeChange.scala` 321–325) compares call arguments with the leaf's pattern
  terms by the constructor-subterm order; literal patterns are already `suc` chains there.
- Printing shows numerals unary (diagnostics, `--print-after`, hovers).

### 3.2 Measurements

On 186694b, staged launcher, one run each, wall time including JVM start and prelude (baseline program
3.99 s). The machine was shared with other sessions' test runs, so times are ±20 %. Scratch programs
(not committed) declare `nat`, `plus` and `times` by clauses on the first argument, `toInt`, `lt`
returning `bool`, `eq : nat -> nat -> Type` with `refl : eq N N`, and `vec`.

| program | result |
|---|---|
| `n : nat = 10000.` / `20000.` / `50000.` / `100000.` | 4.8 s / 12.2 s / **65.7 s** / **260.8 s** (quadratic) |
| `n : nat = 100001.` | E0901 "at most 100000 (nats are unary)" |
| `out (toInt 20000).` / `out (toInt 50000).` | 4.8 s / 6.1 s |
| `out (toInt (plus 25000 25000)).` | 7.8 s |
| `out (toInt (times 200 250)).` / `times 1000 1000` | 5.9 s / **StackOverflowError** after 33 s |
| `out (if (lt 49999 50000) 1 0).` | 7.7 s |
| `w : nat -> eq 20000 (plus 10000 10000). w _ = refl.` | 9.3 s |
| same with 50000 | **StackOverflowError** (`reduceFunction` recursion) |
| `e : eq 50000 (plus 25000 25000) = refl.` | E0901 (`plus` does not reduce in a definition's type: #91); with `100000 100000`: **StackOverflowError** in `unifySp` |
| `out (vlen (rep 10000)).` / `rep 50000` | 5.8 s / 12.0 s |
| `f : nat -> int. f k = 1. f _ = 0. out (f k).`, k = 200 / 400 / 600 | 7.4 s / 22.4 s / 73.8 s (cubic) |
| same, k = 1000 / 10000 / 50000 | **OutOfMemoryError** after 203 s / 307 s / 130 s |

Findings. (a) The literal definition is quadratic not because of the numeral but because
`ObjectTyping.checkArguments` (`core/elab/ObjectTyping.scala` 91–101) recurses into each argument of
`suc (suc …)` and evaluates it (`ev(c, a)`) at every level (stack samples: `checkArguments` →
`Contexts.ev` → `evalArgChain`). A `nat` domain cannot contain object code, so the walk can stop there.
(b) A literal pattern costs a split per unit and a re-normalisation of every equation per split: cubic
time, then out of memory. (c) Values deeper than about 50000 overflow the 64 MB stack in conversion,
read-back and nested function calls. (d) Arithmetic through clauses is usable up to about 10⁵ thanks to
the memo, but not beyond.

## 4. Prior art

Clones (`--depth 1`, sparse, in the scratchpad): agda/agda 192e0d4, leanprover/lean4 b8182f6,
idris-lang/Idris2 1c630e6.

### 4.1 Agda

`BUILTIN NATURAL` binds a data type of the right shape ("modulo the order of the constructors",
`built-ins.lagda.rst` 203–212); the effects are literals, "closed natural numbers are represented as
Haskell integers at compile-time", backend compilation, and enabling the arithmetic built-ins (214–223).
`bindBuiltinNat` also adds a Haskell pragma `= type Integer` (`Rules/Builtin.hs` 662–666).

- **Reduction.** `reduceNat` turns `zero` into `LitNat 0` and `suc` of a literal into the next literal,
  after reducing the argument (`Reduce.hs` 644–660; "reduceNat can traverse the entire term").
  `constructorForm'` is the inverse view, one step: `0 ↦ zero`, `n ↦ suc (n-1)` (`Monad/Builtin.hs`
  252–259).
- **Case trees.** For a literal argument the matcher pushes the literal branch and the constructor
  branch of its constructor form (`CompiledClause/Match.hs` 133–137, 179–184). Compiled clauses have
  `litBranches` next to `conBranches` (`CompiledClause/Compile.hs` 145–161).
- **Conversion** applies `constructorForm` to both sides unless both are literals (`Conversion.hs`
  599–604); the LHS unifier does the same (`Rules/LHS/Unify/Types.hs` 54). So `suc ?m = 5` solves
  `?m := 4`; `?m + 1 = 5` with a user `_+_` stays a postponed constraint.
- **Coverage.** `isLitP` reads `suc^k zero` patterns as literals and `unLitP` expands a literal one
  constructor at a time when a split needs it (`Coverage/Match.hs` 365–397).
- **Arithmetic.** The primitives are `primNatPlus`, `Minus` (monus), `Times`, `DivSucAux`, `ModSucAux`,
  `Equality`, `Less` on `Integer` (`Primitive.hs` 885–897); `mkPrimFun2` only fires when both arguments
  are literals (750–771). `BUILTIN NATPLUS f` type-checks `f` against the primitive's type, runs the
  verification, and replaces `f`'s definition by `Primitive{primClauses = cls}` (`Rules/Builtin.hs`
  805–831); reduction tries the primitive and falls back to the clauses (`Reduce.hs` 751–755). The
  verification checks the defining equations by conversion on fresh variables, allowing either
  recursion argument for `+` (`Rules/Builtin.hs` 475–487, `verify'` 569–588); the manual: "checked to
  make sure that they really define the corresponding built-in function" (276–282).
- **Termination.** `suc t` against a `suc p` pattern cancels; a literal argument is compared with a
  literal pattern by equality (`le`) and otherwise expanded once by `constructorForm`
  (`Termination/TermCheck.hs` 1447–1470).

### 4.2 Lean 4

`Nat` is an ordinary inductive "special-cased by both the kernel and the compiler … at runtime, `Nat`
values that are sufficiently small are unboxed" (`Prelude.lean` 1349–1371). `Nat.add` is defined by
structural recursion on the second argument and marked `@[extern "lean_nat_add"]`: "the definition
provided here is the logical model" (1885–1898). Nothing checks that the model and GMP agree.

- **Kernel.** `reduce_nat` handles `Nat.succ` of a literal and the binary `add`, `sub`, `mul`, `pow`,
  `gcd`, `mod`, `div`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` when both arguments
  whnf to literals (`type_checker.cpp` 668–696, 610–622); the constants are found by name (1251). `whnf`
  tries `reduce_nat` before unfolding (728). `is_def_eq_offset` compares `succ`/literal pairs by
  predecessor (1025–1048); recursors convert a literal major premise to a constructor
  (`inductive.h` 92–93, `inductive.cpp` 1347–1354). Numerals are limited to 128 MB, checked on
  literals and on `add`/`sub`/`mul`/`pow` results (30–36, 296–320).
- **Meta.** `reduceNat?` has the same list (`WHNF.lean` 1011–1033); `toCtorIfLit` is the view (24–30).
  `isDefEqOffset` solves `s + k₁ =?= v` by `s =?= v - k₁` (`Offset.lean` 118–160), tried before delta
  (`ExprDefEq.lean` 2420–2421).
- **Matchers.** A column of only values and variables is a *value transition*, compiled by `caseValues`
  into decidable equality tests (`Match/Match.lean` 301–306, 675–681, 1048–1050). Values mixed with
  constructor patterns are expanded one step (`expandNatValuePattern`, 336–337, 745–753).
- **Literals** are elaborated through `OfNat` with `instOfNatNat` the default (`Prelude.lean` 1396–1405).

### 4.3 Idris 2

Any type with a `ZERO`-like and a `SUCC`-like constructor is flagged by shape (`TTImp/ProcessData.idr`
342–362); `%builtin Natural` only checks that the flags were set (`TTImp/ProcessBuiltin.idr` 164–226).
The compiler replaces the constructors by `0` and `1 +` on `Integer` and cases by zero tests
(`Compiler/Opts/Constructor.idr` 6–7, 100–125), and hard-wires `natToInteger`, `plus`, `mult`, `minus`,
`equalNat`, `compareNat` of `Prelude.Types` (`natHack`, 81–95). The documentation speaks only of the
runtime ("At runtime, Idris2 will automatically represent this the same as the `Integer` type",
`docs/source/reference/builtins.rst` 13–28), and `Core/Normalise` has no case for these flags: **the
type checker stays unary**.

## 5. Assessments

### 5.1 Binding (question 1)

Three mechanisms: a pragma naming the type (Agda), the shape rule (Idris 2, Hugin's N2), or a library
type the compiler knows by name (Lean). Lean's mechanism does not survive shadowing (#127 N1: a user's
`nat` must keep working) and contradicts N2, which already gives literals to every nat-like family. A
pragma would be a second way to the same literals, which #127 rejected (`docs/design/sugar.md`,
section 5). **The shape rule binds the representation**, keyed by the family's global id. Since every
nat-like family is isomorphic to ℕ, the rule cannot misread a family (Idris 2's argument).

### 5.2 Representation, evaluation, conversion, unification (question 2)

`Val.Nat(fam, n)` and `Tm.Nat(fam, n)`, with the invariant that a closed numeral of `fam` is never a
constructor chain: `globalValue(zero)` is `Nat(fam, 0)`, and `rigid(Glob(suc), [EApp(Nat(fam, n))])` is
`Nat(fam, n + 1)`. Read-back, zonking and the memo keys are O(1) per numeral (`MemoKeys` treats it as
stable data, like `Lit`). One helper, `natView(v): Zero | Suc(pred) | No`, serves every consumer. The
cost of the invariant is one check in `rigid` on constructor heads (a set of `suc` ids).

- **Conversion with glued values.** `Val.Top` needs no change: a definition `n : nat = 50000` is a `Top`
  whose `Unfold` is `Nat(fam, 50000)`, compared in `Flex` by id and arguments, then unfolded as today.
  New cases in `unifyForced`: `(Nat a, Nat b)` by `a == b` (all states); `(Nat n, Rigid(suc, [v]))` and
  symmetric: fail if `n = 0`, else `unify(Nat(n-1), v)`; `(Nat 0, zero)` cannot occur by the invariant.
  `Flex` against `Nat` solves with the literal (O(1) `psubst`).
- **Unification.** `suc ?m = 5` gives `?m := 4` by one view step; `suc^k ?m = n` costs `k` steps,
  bounded by the program text. `?m + 1 = 5`: with #127 N4, `e + k` against a nat-like type *is*
  `suc^k e`, so this is the previous case, which is Lean's `isDefEqOffset` result without a separate
  offset form. A call `plus ?m 1` reduces if `plus` recurses on its second argument (as Lean's `Nat.add`
  and the recommended `std/nat`), and is otherwise stuck and postponed, as in Agda.
- **Deep chains** remain possible for open terms (`suc^100000 x` written by a meta program). They do not
  arise from literals or arithmetic on literals, which covers the measured overflows of 3.2 (c).

### 5.3 Case trees, coverage, termination (question 3)

- **Evaluation.** `runTree` at a `Split` on a `Nat` value uses the view: the `suc` branch gets
  `Nat(n-1)`, the `zero` branch `n = 0`; O(1) per step (Agda `Match.hs` 179–184).
- **Literal patterns.** In #67's canonical order (the first remaining clause, its leftmost decided
  position) a literal at the chosen position gives a value split: `SplitAtom(x, branches, default)`,
  which exists already, with keys `Tm.Nat(fam, k)` for every literal of the remaining clauses at that
  position (Lean's `caseValues`, Agda's literal branches). In a branch `k`, a clause with `P + j` there
  (`j ≤ k`) continues with `P := k - j`; a variable continues; other literals drop. The default keeps
  variables and `P + j` patterns. A constructor at the chosen position gives a constructor split, and
  each literal `k > 0` of a later clause becomes `suc (k-1)` there, a single step (Agda `unLitP`, Lean
  `expandNatValuePattern`). The tree's depth is bounded by the number of constructor patterns written,
  not by the literals' values. `f 50000 = 1. f _ = 0.` is one test.
- **Coverage (#67).** At a nat position the probes are *value classes*: the singletons `{k}` for the
  literals named and the intervals between the breakpoints `{k, k+1, j}` of the literals `k` and offsets
  `P + j`, the last one unbounded. There are O(clauses) classes, each with a witness for messages
  (`f 3`, `f (N + 6)`, printed with N4/N5). With one class per value the probes of #67 4.1 would be
  `suc^k zero`: the same verdicts at O(k) cost. This replaces the sentence "Literals are `sucᵏ zero`" of
  `coverage.md` 4.1 and has to be agreed with #67 batch 2.
- **Size change.** Pattern terms keep `suc` for `P + j`, so structural descent is unchanged. New cases
  in the subterm test: a literal argument `m` against a literal pattern `k` is `<` if `m < k` and `≤` if
  equal; a literal argument against `suc p` is compared with `p` after one view step (Agda
  `TermCheck.hs` 1466–1470). Both are the unary subterm order read off the representation, so
  termination verdicts can only become more precise (Agda answers "unknown" for `m < k`).

### 5.4 Primitive arithmetic (question 4)

**Set.** Agda's set: it is the set whose definitions are structurally recursive and so can be checked
by equations, which Hugin can elaborate (no well-founded recursion). Lean's extra operations (`pow`,
`gcd`, bitwise, shifts) and its direct `div`/`mod` are not structural; `div`/`mod` come from Agda's
helpers, as in `Agda.Builtin.Nat`. `toInt` is added for staging (5.5). Each operation is one row:

| op | type | defining equations (either listed variant) | native |
|---|---|---|---|
| add | `N → N → N` | `n + 0 = n`, `n + suc m = suc (n + m)`; or on the first argument | `+` |
| monus | `N → N → N` | `0 ∸ 0 = 0`, `0 ∸ suc m = 0`, `suc n ∸ 0 = suc n`, `suc n ∸ suc m = n ∸ m` | `max(0, n - m)` |
| mul | `N → N → N` | `0 * m = 0`, `suc n * m = m + n * m` (`+` a recognised add), or variants | `*` |
| divSucAux, modSucAux | `N → N → N → N → N` | Agda's (`Rules/Builtin.hs` 520–543) | Agda's (`Primitive.hs` 890–895) |
| eq | `N → N → B` | `0 == 0 = t`, `suc n == 0 = f`, `0 == suc m = f`, `suc n == suc m = n == m` | `==` |
| lt | `N → N → B` | `n < 0 = f`, `0 < suc m = t`, `suc n < suc m = n < m` | `<` |
| toInt | `N → int` | `toInt 0 = 0`, `toInt (suc n) = toInt n + 1` (meta `int`) | exact to `Long`, else stuck |

`N` is a nat-like family, `B` a family with exactly two constant constructors; `t ≠ f` are found by the
first equation.

**Binding and checking.** After a clause group is elaborated (at the end of its component under #91),
each function whose type matches a row is verified: its equations are checked by `conv` on fresh
variables, as Agda's `verify'`. On success its global records the operation
(`GlobalKind.Function(arity, tree, native = Some(op))`), and `reduceFunction` computes natively when all
explicit arguments are `Nat` values, else runs the tree (Agda's `primClauses` fallback). This is sound
for the same reason as Agda's check: the equations determine the function on all numerals by induction,
so the native result is the clauses' result. It is cheaper than Agda's pragma in syntax and costs a few
`conv` calls per candidate (functions of exactly these types). It is predictable in one direction: a
correct but differently written function (an accumulator `plus`) silently stays unaccelerated.
`--print-after elaborate` and hovers say "native: add" so a user can see it. Lean's trust in
`@[extern]` is not an option: a meta-level mistake would change typing.

**Booleans (#61 B3).** `std/nat` returns the shared `bool` of `std/reflect`, as `same` does. Recognition
by shape also accepts a user's own two-constructor result type; the equations fix which constructor
means "true". The `%builtin` primitives (`same`, …) stay as they are: they have no clauses to fall back
to, and the nat operations do.

### 5.5 Staging (question 5)

Meta naturals have no lifting (`level zero` stays E0902, `meta/staging.md` 61–66). The only way into
object code is `toInt`, which becomes O(1) natively, followed by the existing O(1) `persist` of a meta
literal. Meta `int` is 64-bit with exact arithmetic, so `toInt` of a numeral above `Long.MaxValue` is
stuck and the existing E0909 ("cannot compute a primitive value at compile time") reports it, as it
does today for `big 9223372036854775807` with `big X = X + 1` (measured). Object code can never carry a wrong
(wrapped) value. A meta `BigInt` `int` would be a separate decision (the object `int` is 64-bit).

### 5.6 The cap and printing (questions 6, 7)

E0901 "nat literal too large" exists only because of the unary chains, and goes. Source numerals keep
the range of integer literals (the lexer already produces a `BigInt` for larger tokens and reports
`IntegerOutOfRange`, `syntax/ExprSyntax.scala` 136–147). Accepting larger nat literals is a small
change, offered as an open decision (O3). Computed numerals are unbounded. Lean's 128 MB guard
protects `pow` and `shiftLeft`, which can explode in one step; `add`/`mul` on numerals from the source
grow at most polynomially in the elaboration time already spent. Printing: `Nat(fam, n)` prints as `n`
and an open `suc^k e` as `e + k` (#127 N5), in diagnostics, `--print-after`, REPL and hovers.

### 5.7 Interactions

`same` on numerals becomes decidable (a `Nat` is an atom for `atomKey`): `same 3 3` reduces where it was
stuck. That is the same value, and an improvement. Reflection does not reify meta naturals. The
`std/nat` of #127 N1 (being implemented on `feat/sugar-127-nat`) should define `plus` on the second
argument (Lean's model), so `plus N 1` reduces to `suc N` on open `N`, and `minus`, `times`, `eq`, `lt`,
`div`/`mod` through Agda's helpers, and `toInt`, in the forms of the table. N1 can land first: its
functions are accelerated once batch 3 lands, with no change to the library.

## 6. Alternatives rejected

- **Agda's pragma (`%builtin natural nat`, `%builtin natplus plus`).** A second way to get literals
  (#127 N2), new item syntax where `%builtin` is an expression form, and it binds by name, which
  shadowing complicates. It would make a failed binding an error instead of a silent miss; this is
  the trade-off of open decision O1.
- **Lean's hard-wired names in `std/nat`.** Not robust to shadowing and to users' nat-like families;
  `index` would stay unary; trusts the model.
- **A primitive without clauses (`plus : nat -> nat -> nat = %builtin add.`).** Open terms would be
  stuck: `vec A (plus (suc n) m)` would no longer be `vec A (suc (plus n m))`, so `append` stops
  checking. Agda and Lean keep the definition for this reason.
- **An offset value `Val.NatAdd(v, k)` for `suc^k v`** (Lean's `e + k`). Only pays for long `suc` chains
  over neutrals, which literals no longer create; it would add a case to every consumer. Possible later
  without rule changes.
- **Reusing `Val.Lit(IntL)` for numerals.** It does not carry the family, has `Long` range, and would
  make meta `int` and `nat` values indistinguishable to `same`, printing and size change.
- **Compiler-only acceleration (Idris 2).** Hugin's meta programs run only during elaboration.
- **Keeping N6 "not now".** Overridden by the issue; 3.2 shows realistic sizes fail.

## 7. Effects

| program (3.2) | today | after (expected) |
|---|---|---|
| `n : nat = 50000.` / `100000.` | 65.7 s / 260.8 s | baseline (O(1) literal, and the walk is fixed) |
| `n : nat = 100001.` / `10^12` | E0901 / E0901 | accepted |
| `toInt 50000`, `plus 25000 25000`, `times 1000 1000` | 6.1 s, 7.8 s, stack overflow | baseline: native |
| `eq 50000 (plus 25000 25000)` in a clause | stack overflow | baseline |
| `f 50000 = 1. f _ = 0.` | out of memory | baseline: one value test |
| `vlen (rep 50000)` | 12.0 s | unchanged order (a 50000-element `vec` is 50000 values), smaller constants |
| diagnostics with numerals | unary | digits |
| programs without numerals | — | unchanged; one id check in `rigid` per constructor application |

No accepted program is rejected; programs that overflowed now pass; no output changes except printing
(goldens with unary numerals are updated, as N5 already requires). `same` on numerals reduces (5.7).

## 8. Batches

Each batch is one pull request and updates the reference with the code.

0. **The walk** (3.2 a): `checkArguments` stops at domains without object code (nat-like families,
   meta base types). Reference: none (performance). Golden: `bench/` entry only.
1. **Representation and views** (5.2, 5.6). Code: `Tm.Nat`/`Val.Nat` with `BigInt`; `natLiteral` builds
   `Tm.Nat`; the invariant in `rigid`/`globalValue`; `natView`; read-back, zonk, renaming, `MemoKeys`,
   `atomKey`; `unifyForced` and index unification cases; `runTree` view; printing digits and `e + k`;
   E0901 `NatTooLarge` removed (and `TypeProblems` 152). Reference: `meta/families.md` "Nat literals"
   (numerals are values, views, no cap; the representation is not observable), `meta/clauses.md`
   "Evaluation" (a numeral matches `zero`/`suc`), `meta/staging.md` (no change of rule; mention `toInt`),
   `docs/errors/E0901.md` (unchanged: it does not list the cap). Goldens: `run/nat_numerals` (large
   literals, conversion, `suc ?m = 5`, `e + k`),
   `neg/nat_numerals` (`suc ?m = 0`, negative literal), print-after golden with digits.
2. **Patterns** (5.3), after #67 batch 2. Code: literal value splits in `Clauses` (no `PLit` expansion),
   value-class probes in coverage, literal cases in `SizeChange`. Reference: `meta/clauses.md` "Patterns"
   (literal patterns and the canonical value split), `meta/coverage.md` ("Cases and probes": value
   classes for literals), `meta/termination.md` "The criterion" (numerals compared by value).
   Goldens: `run/nat_patterns` (`f 50000`, mixed `f 0`/`f (N + 2)`/`f 7`), `neg/nat_coverage` (missing
   `f (N + 6)`), SCT golden with `f 5 = f 3`.
3. **Arithmetic** (5.4, 5.5). Code: recognition after a component's clauses, `native` on
   `GlobalKind.Function`, native reduction with fallback, `toInt`, print-after/hover "native: op".
   Reference: `meta/functions.md` new section "Arithmetic on numerals" (the table of 5.4, recognition,
   fallback, `toInt` overflow), `std/nat` page and `prelude.md` (with #127 N1). Goldens:
   `run/nat_arith` (each operation, variants by either argument, a non-recognised accumulator `plus`,
   a user `bool`), `run/nat_toint` (object code from `toInt 10^12` and the stuck case beyond 2⁶³).
4. **Benchmarks** (9). `bench/meta/nat_large.hgn` in `BenchSet` and `bench/cold.sh`; numbers in
   `docs/PERFORMANCE.md`.

Batch 1 alone removes the cap, the overflows of conversion and the cost of literals; batch 2 removes the
pattern cost; batch 3 the arithmetic cost. Batches 0 and 1 do not depend on #67.

## 9. Benchmark plan (question 8)

`bench/meta/nat_large.hgn`, one program in the #60 harness (`BenchSet`, `cold.sh`, five runs, median),
with sections that can be timed separately by `--only`: (a) `n : nat = 1000000.`; (b) `toInt (plus
500000 500000)`, `toInt (times 1000 1000)`, `lt`, `eq`; (c) `w : nat -> eq 1000000 (plus 500000
500000). w _ = refl.`; (d) `f 50000 = 1. f _ = 0.` and a ten-literal `switch`; (e) `vlen (rep 50000)`;
(f) `fin 1000000` index arithmetic in a type. **Before**: today's sizes that finish (the 3.2 rows), and
the failing ones recorded as failures. **After** each batch: the same file at full size, plus
`meta_scaled` and the whole bench set to confirm no regression from the check in `rigid`. Acceptance: (a)–(d)
within 10 % of the baseline program; no regression above noise elsewhere.

## 10. Sources

- agda/agda 192e0d4: `src/full/Agda/Syntax/Literal.hs`; `TypeChecking/{Primitive.hs, Reduce.hs,
  Conversion.hs, Monad/Builtin.hs, Coverage/Match.hs, CompiledClause/{Compile,Match}.hs,
  Rules/Builtin.hs, Rules/LHS/Unify/Types.hs}`; `Termination/TermCheck.hs`;
  `doc/user-manual/language/built-ins.lagda.rst`.
- leanprover/lean4 b8182f6: `src/kernel/{type_checker.cpp, inductive.h, inductive.cpp}`;
  `src/Lean/Meta/{WHNF.lean, Offset.lean, ExprDefEq.lean, Match/Match.lean}`; `src/Lean/Expr.lean`;
  `src/Init/Prelude.lean`.
- idris-lang/Idris2 1c630e6: `src/TTImp/{ProcessData,ProcessBuiltin}.idr`;
  `src/Compiler/{CompileExpr.idr, Opts/Constructor.idr, Common.idr}`; `src/Core/Normalise/`;
  `docs/source/reference/builtins.rst`.
- Hugin 186694b; `docs/design/sugar.md` (#127, branch `design/sugar-127`), `coverage.md` (#67),
  `elab-order.md` (#91), `elaborator-glued.md` (#66), `stdlib.md` (#61).
