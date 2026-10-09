# Stage polymorphism: sharing data and definitions across stages

Research note for [issue #52](https://github.com/k0uks1/hugin/issues/52). Proposed syntax is written
against the explicit reflection quotes `'{ … }` of [issue #76](https://github.com/k0uks1/hugin/issues/76);
where that matters it is said.

> **Status.** Shared data declarations (§5) are implemented by
> [issue #80](https://github.com/k0uks1/hugin/issues/80); the reference defines them (meta/families,
> "Shared data"; meta/staging, "Lifting") and `docs/NOTES.md`, "Shared data (#80)", records the decisions
> of the implementation. The examples in `docs/design/examples/` are rewritten in the new form and run
> as goldens; §2 and the code in this note describe the duplication before #80 (`seq`, `snil`, `scons`,
> `sappend` no longer exist). Shared aliases (`DataAlias` of §5.1) and labels on the prelude's `cons` are
> not implemented.

Contents

1. Recommendations
2. The duplication today
3. Literature
4. The questions of the issue
5. Proposal: shared data declarations
6. Functions: costs and benefits
7. A related defect found on the way
8. Open questions, with recommended answers
9. References

---

## 1. Recommendations

**Data.** Add *shared data declarations*: `list A : data.` with constructors declared as today. One
declaration yields a meta inductive family, an object family of constructors (facts, as every object
constructor), and two derived total meta functions: `list.lift`, the fold into object code `⇑(list B)`,
and `list.reify`, the fold into the reflective type `term`. Stage inference inserts `lift` where a meta
value of a shared type is used as object code. This generalises the existing persistence of `int`,
`float` and `string`, which becomes the base case of one rule. The extension is conservative: everything
it generates can be written by hand today (the example files do so), so it adds no rule to the core
calculus and does not change the semantics of the object level. In the prelude it replaces `seq` by
`list` and makes `option` available at both stages.

**Functions.** Do not add stage-polymorphic functions, neither as a language feature nor as a library
directive. The only reading available for Hugin is "a meta function and its graph relation". That
relation is useless without a mode and the demand transformation, so stage inference for functions would
reintroduce modes. The facts it creates depend on the stage chosen, so the choice would be observable.
The meta termination proof does not carry over: Ackermann's function is accepted at the meta level and
its graph relation is rejected with E0603 (§6.2). In the three worked examples the natural meta and
object definitions differ in structure, and the only case where the translation is mechanical (`len`) is
two rules long. Once data is shared, the remaining duplication is between programs that are written
differently for good reasons.

**Related defect.** In a file with a module-wide directive (such as `%demand`), a rule that uses a meta
value as object code, even a persisted `int`, is rejected with E0917 (§7). It should be fixed
independently of this note; the derived `reify` gives the fix a uniform form for shared types.

## 2. The duplication today

The prelude declares two list types:

```hugin,ignore
list A : type.  nil : list A.  cons : A -> list A -> list A.     (* object: facts *)
seq : Type -> Type.  snil : seq A.  scons : A -> seq A -> seq A.  (* meta: `[]`, `::` *)
```

The list syntax `[a, b]` and `x :: xs` is bound to `seq` and is not available for object lists. `option`
is an object type only, so a meta function that may fail declares its own (`maybe` in
`examples/typechecker.hgn`). `bool` is meta only, by decision (#74: truth at the object level is the
presence of a fact).

Measured duplication of *functions* in the prelude is zero. The meta helpers (`sappend`, `band`,
`member`, `sdiff`, `openT`, the `%demand` code) have no object counterparts and need none; the object
relation `len` has no meta counterpart. All duplication in the prelude is in types.

The three example files show the duplication in programs.

- `examples/lists.hgn` converts a meta `seq int` into an object `list int` twice, once into `⇑(list B)`
  for staging and once into `term` for reflection, and writes the length as a meta function next to the
  prelude's relation. Persisting an `int` has to be wrapped in a function (`persist`) to be passed to the
  generic `lift`.
- `examples/typechecker.hgn` declares the syntax of the simply typed lambda calculus twice: 3 types and 7
  constructors at the object level, the same again at the meta level, and 5 clauses of conversion
  functions between them. The checker exists as three rules (`typed`, with `%demand`) and as a meta
  function `infer` with its helpers.
- `examples/graphs.hgn` computes reachability with the prelude's two-rule functor `tc` and, for a graph
  known at compile time, with a meta function that iterates a step a bounded number of times.

The data duplication is mechanical: each converting clause maps a constructor to the constructor of the
same name at the other stage. The function duplication is not, as §6 shows.

## 3. Literature

For each work: what it does, and what transfers to Hugin.

**Kovács 2022**, *Staged Compilation with Two-Level Type Theory*, ICFP 2022 (PACMPL 6, ICFP;
doi:10.1145/3547641; arXiv:2209.09729). Hugin's meta level follows it: `⇑A`, inferred quotes and
splices, staging by evaluation. Two points bear on #52. Section 2.3 shows that `⇑` preserves negative
type formers but only maps inductive types in one direction: there is a map `Bool₁ → ⇑Bool₀`, called
*serialization* or *lifting* in the staging literature, and only constant functions back. Finite
function types can be serialised; `ℕ₁ → ℕ₁` cannot. Section 8 (future work) names stage polymorphism as
a way to remove the code duplication that arises when the object and meta languages are similar, and
sketches a setup with a third stage that is polymorphic over the other two. The paper does not develop
it. *Transfers:* lifting of inductive types is the standard construction and is definable inside 2LTT;
the "third stage" idea is the formal reading of a shared declaration (§5.9). Section 6 of the paper notes
that intensional analysis of `⇑A` is incompatible with the standard presheaf model, which is why Hugin
keeps `⇑` opaque and reflects through separate inductive types; the proposal keeps that separation.

**Kovács 2024**, *Closure-Free Functional Programming in a Two-Level Type Theory*, ICFP 2024 (PACMPL 8,
ICFP, 659–692; doi:10.1145/3674648). A 2LTT with a simply typed first-order object language and a
dependently typed meta language, used for monads and stream fusion. Its object level is first order, as
Hugin's. I found no follow-up paper that develops stage polymorphism; the full text of this paper was not
accessible from this environment, and this note claims nothing about it beyond its abstract.

**Allais 2024**, *Scoped and Typed Staging by Evaluation*, PEPM 2024 (arXiv:2310.13413). Builds on
Kovács's observation that the two layers need not share features (static layer a functional language,
dynamic layer circuit descriptions). *Transfers:* support for keeping the levels different, which is
Hugin's situation.

**Annenkov, Capriotti, Kraus, Sattler 2023**, *Two-Level Type Theory and Applications*, Mathematical
Structures in Computer Science 33(8), 688–743 (doi:10.1017/S0960129523000130; arXiv:1705.03307). The
general theory: an inner and an outer type theory, with the outer one as internalised metatheory, and
the distinction between outer types and *fibrant* types (those that behave as inner types). *Transfers:* the vocabulary and the model;
the question "which outer types have inner counterparts" is the question of §5.2, here answered
syntactically because Hugin's inner level is a first-order Datalog.

**Cross-stage persistence in MetaOCaml.** Taha and Sheard, *MetaML and multi-stage programming with
explicit annotations*, TCS 248 (2000), introduce persistence of present-stage values in future-stage code.
BER MetaOCaml (Kiselyov, FLOPS 2014, LNCS 8475, 86–102; Kiselyov, *MetaOCaml: Theory and Implementation*,
arXiv:2309.08207) persists values of base types as literals and global identifiers by name; other values
persist by reference, which is meaningful only when the code runs in the generating process. *Transfers:*
only the serialising form fits Hugin. An object value is a literal or the identity of a fact; a meta value
"by reference" has no meaning there. Hugin's persistence of base types is serialisation, and shared data
extends the set of serialisable types.

**Typed Template Haskell, `Lift`.** Xie, Pickering, Löh, Wu, Yallop, Wang, *Staging with Class: a
specification for typed Template Haskell*, POPL 2022 (PACMPL 6, POPL). The class
`Lift t` has `lift :: Quote m => t -> m Exp` and `liftTyped :: Quote m => t -> Code m t`; GHC's
extension `DeriveLift` derives instances for algebraic data types. A local variable used one level
deeper than its binding is lifted by inserting `lift` (the paper's account of level correctness).
*Transfers:* the two functions match the proposal's `reify` (untyped syntax) and `lift` (typed code), and
automatic insertion at a stage mismatch matches stage inference. Hugin has no type classes; instances
are synthesised structurally from the type (§5.4), which is what a derived instance does for a closed
set of types.

**Scala 3 `ToExpr` and `FromExpr`.** Stucki, Biboudis, Odersky, *A Practical Unification of
Multi-stage Programming and Macros*, GPCE 2018; the
[macro reference](https://docs.scala-lang.org/scala3/reference/metaprogramming/macros.html).
`ToExpr[T]` has `apply(x: T)(using Quotes): Expr[T]`, used by `Expr(x)`; `FromExpr[T]` has
`unapply(x: Expr[T])(using Quotes): Option[T]`, used by `x.value` and in quoted patterns
(`${Expr(n)}`), and matches only constants. Instances are given by hand; the reference shows no
derivation. Local variables cannot persist across levels; global definitions can. *Transfers:* the
partial reverse map `FromExpr` corresponds to a `lower : term -> option (T A)` (§5.5); its use in quoted
patterns is the "typed hole" of Q3 (§4.3).

**Lean 4 `ToExpr`.** Core class `Lean.ToExpr` (`toExpr : α → Expr`, `toTypeExpr : Expr`) with a deriving
handler in `Lean.Elab.Deriving.ToExpr` for inductive and mutually inductive types, universe polymorphic
through `Lean.ToLevel`; Mathlib has its own handler (`Mathlib.Tactic.DeriveToExpr`). *Transfers:* a
deriving handler that runs at the declaration and produces an ordinary definition is the right
implementation strategy. The derived function is checked like hand-written code, and nothing in the core
changes.

**Datafun.** Arntzenius, Krishnaswami, *Datafun: a Functional Datalog*, ICFP 2016
(doi:10.1145/2951913.2951948); *Seminaïve Evaluation for a Higher-Order Functional Language*, POPL 2020.
A functional language with finite sets, semilattice types and monotonicity typing; relations are values
and fixed points are terms. There are no constructors with identity. *Transfers:* little. Datafun unifies
functions and relations by putting relations inside a runtime functional language. Hugin's functional
level runs at compile time and its object level has no functions. Datafun is evidence that the
unification needs one runtime language, which Hugin does not have.

**Flix.** Madsen, Lhoták, *Fixpoints for the Masses: Programming with First-Class Datalog Constraints*,
OOPSLA 2020 (PACMPL 4, OOPSLA). Datalog programs are values of a functional language; rules may call
functions, and both share the algebraic data types of the language because both run at the same time.
*Transfers:* sharing data costs nothing when both sides are one stage. In Hugin the sides are two stages,
and a shared declaration is the corresponding mechanism. Flix does not turn functions into relations.

**Formulog.** Bembenek, Greenberg, Chong, *Formulog: Datalog for SMT-Based Static Analysis*, OOPSLA 2020
(PACMPL 4, OOPSLA, article 141; arXiv:2009.08361). Datalog with an ML-like functional sublanguage whose
functions over algebraic data types are called from rule bodies. Terms are values, not facts; functions
are evaluated, not translated to relations. *Transfers:* "functions as evaluated builtins of rules"
is a different design from graph relations. In Hugin it conflicts with the invariant that every value a
valuation binds has only facts as constructor subterms, unless the function's result is a literal
(§6.6).

**Functional IncA.** Pacak, Erdweg, *Functional Programming with Datalog*, ECOOP 2022, LIPIcs 222, 7:1–7:28
(doi:10.4230/LIPIcs.ECOOP.2022.7). This is the functions-as-relations translation in a setting close to
Hugin's. Each first-order function becomes its graph relation, guarded by an *input relation* computed
by the demand transformation (their Principles 3 and 4, §3); the translation is whole-program. Algebraic
data types become *constructor relations*, plus selector and *instance relations* that enumerate every
constructed value (§4.1), which is Hugin's facts-with-identity. Correctness of the translation is stated
as a conjecture (Conjecture 1, §3), not proved. *Transfers:* the most direct evidence for §6. The
translation needs demand; the set of constructed values depends on demand and is observable through
instance relations; and the termination of the result is argued separately from that of the source.

**Descriptions and levitation.** Chapman, Dagand, McBride, Morris, *The Gentle Art of Levitation*,
ICFP 2010, 3–14 (doi:10.1145/1863543.1863547): inductive types given by first-class descriptions, with
generic programs by interpretation of the description. Dagand, McBride, *Transporting Functions across
Ornaments*, ICFP 2012: relating `list` to `nat` and deriving functions such as length along the
relation. *Transfers:* the description view gives the precise class of shareable types (polynomial
functors with parameters, §5.2) and the specification of `lift` and `reify` as generic folds. A
first-class universe of descriptions in Hugin's meta level would be a large addition with no use at the
object level, which cannot interpret descriptions (it has no functions). Derivation at the declaration
gives the same functions without that universe.

**Datalog with first-class facts.** Gilray, Sahebolamri, Sun, Kunapaneni, Kumar, Micinski, *Datalog with
First-Class Facts*, arXiv:2411.14330. The object level of Hugin (DL∃!). Demand is ordinary rules. The
redesign removed modes because demand changed the set of facts (`docs/REDESIGN.md`, §1.1); §6.3 of this
note applies the same argument to functions.

**Size-change termination.** Lee, Jones, Ben-Amram, *The Size-Change Principle for Program Termination*,
POPL 2001. Used at both levels of Hugin, over call graphs at the meta level and over derivation chains at
the object level.

## 4. The questions of the issue

### 4.1 Q1: stage polymorphism of functions

A meta function is a total function given by clauses and evaluated by the compiler. The object level has
no functions; the only object reading of a function `f : A → B` is its graph `f° : A → B → rel`. The
translation of clauses into rules is the one of functional IncA: one rule per clause, a body atom for
each recursive call, and a guard that restricts the inputs to values that exist.

The guard is the problem. A rule `f° (c X̄) R :- …` only fires on arguments that are facts. Arguments of
recursive calls that the clause builds (`f (suc N)`, `ack M (ack (suc M) N)`) are facts only if
something creates them, which is what `%demand f +x̄ -r` does: it builds the demanded arguments as facts
of `f.check`. So the graph relation needs a mode (arguments in, result out) and demand. Hugin removed
modes as a semantic notion on purpose (#40, D2). A stage-polymorphic function brings them back, either
hidden in the translation or as a required annotation.

Semantics preservation holds in a restricted form. For a meta function `f` and inputs `v̄` that are
demanded, `f° (lift v̄) r` holds exactly when `r = lift (f v̄)`. The proof is by induction on the meta
termination order, provided the demand closure contains the arguments of every recursive call. Totality
transfers. Termination does not (Q4). Skolem identity is preserved, but the facts that exist afterwards
differ from those of compile-time evaluation (§6.3).

The stage cannot be inferred without changing answers. A use of `f` with compile-time arguments can be
evaluated by the compiler, and a use with object arguments needs the relation. If the elaborator chose,
the set of facts would depend on its choice. This is the situation the redesign removed: `%mode` changed
answers of programs that observed constructors (`docs/REDESIGN.md`, §1.1).

Answer: stage polymorphism of functions has a meaning for Hugin, the graph relation with demand, but it
is not worth its weight (§6).

### 4.2 Q2: shared data structures

Yes, and the formal story is simple because Hugin's object level is first order. A shareable type is
a family of polynomial functors in its parameters (§5.2). For such a type, the meta inductive `T₁`
and the object family `T₀` have the same constructors, `⇑(T₀ B̄)` with the object constructors is a
`T₁`-algebra, and `lift` is the fold out of the initial algebra `T₁` into it. Of the three options of the
issue:

- a stage-indexed universe `U s` with stage variables is the right reading, restricted to declarations
  and with the stage fixed at every use (§5.9); full stage variables are not needed;
- a "liftable" class closed under the inductive formers is the right *judgement* (§5.4), without user
  instances;
- descriptions give the specification of the class and of the derived functions, but a first-class
  universe of descriptions is not needed (§3).

Interaction with Skolem identity: none beyond what hand-written terms have. A lifted value is a closed
object term. In a head it derives the fact and all its subfacts; in a body it is a pattern or an existence
check. Bound columns: constructors have no bound columns, so a shared type cannot have one; it can be the
type of a key column. Object typing: the object side is an ordinary family of constructors. Reflection:
`reify` is specified by `reflect (T.reify v) = T.lift v` (§5.5), so the derived reflective quoting
coincides with the reflective embedding of the lifted code.

### 4.3 Q3: pattern matching across stages

Meta code never sees facts: facts exist when the object program runs, after the meta level has finished.
So "meta matching on object values" is not possible. Within that limit, shared data gives two things.

1. One constructor vocabulary. A meta clause `length (cons X Xs) = …` and an object rule
   `len (cons X L) N :- …` use the same names and the same pattern syntax. Inside a reflection quote
   `'{ … }` (#76) names are object syntax, so `'{ cons $X $Xs }` matches the reflected object term.
2. Typed holes. A hole of a shared type in an expression quote, `'{ held $xs }` with `xs : list int`,
   can insert `list.reify` as stage inference inserts `lift`. This is total and fits #76. In a quoted
   *pattern*, a hole of a shared type would have to run a partial `lower` on the subterm (Scala's
   `${Expr(n)}`). Hugin's clause patterns elaborate to finite constructor patterns, and a recursive shared
   type has no finite pattern for "any lifted list", so this needs views or guards in patterns, which
   Hugin does not have. Not now (§8, question 5).

### 4.4 Q4: totality and termination

For data, `lift` and `reify` are folds, structurally recursive, and accepted by the meta check. The
object side gains no rules. Shared data has a property that relates the two orders: for closed values of
shared types, `w` is a proper subterm of `v` exactly when the fact `lift w` is a proper subterm of
`lift v`. So the structural order used by the meta check and the proper-subterm order on identities used
by (A) and (B) coincide on shared data.

For functions, one size-change argument does not justify both sides. The meta check relates the
arguments of a call to the patterns of the clause. The object check relates premises to heads along
derivations, including the demand rules, whose arguments may be answers of other calls. The meta
function `ack` of the reference (Termination of meta functions) is accepted; its graph relation under
`%demand ack +m +n -r` is rejected with E0603, because the demand of the inner call needs an answer of
`ack` and so puts the demand relation and the answers in one component (§6.2). A translation would
therefore produce object errors in generated code for functions the meta level accepts.

### 4.5 Q5: costs

For shared data:

- *Elaboration.* A name declared by a shared declaration denotes two constants, one per stage. The
  elaborator already elaborates every term at the stage of its expected type, so the constant is chosen
  by that stage. Where no type is expected (a definition `x = nil.`), the position is a meta position, as
  every definition is. No stage variables, no constraint solving.
- *Errors.* A misuse is a type error at the use: `bad (lift [3])` with `bad : string -> rel` reports
  E0901 at the argument. The same conversion written into `term` reports E0402 inside the converting
  function, with only a note naming `bad` (compare `examples/lists.hgn`'s two functions; checked on the
  current build). Typed `lift` keeps errors where they belong.
- *Incrementality.* One declaration generates a fixed set of items (two families, two functions). The
  footprint is local to the declaration, as for any declaration.
- *Modes.* None.

For functions the costs are those of §6: modes, demand, observable fact sets, a second termination proof,
and errors in generated rules.

## 5. Proposal: shared data declarations

### 5.1 Syntax

```text
DataDecl   ::= NAME VAR* ":" "data" "."
DataAlias  ::= NAME VAR* ":" "data" "=" ShType "."
```

A *shared type* is declared with the sort `data`. Its constructors are declared as today, by their
result type:

```hugin,ignore
list A : data.
nil : list A.
cons : (head : A) -> (tail : list A) -> list A.
```

`data` is not a universe. It says that the declaration exists at both stages. Constructors of a shared
type are classified by their result, as all declarations are (reference: Declarations).

> **Rationale.** An explicit marker is needed because a shared type is closed: its meta side is an
> inductive family, which coverage checks against the complete set of constructors. An object open type
> can gain members through subtyping edges, so it cannot become shared implicitly.

### 5.2 Shareable types

Let `T` be declared `T a₁ … aₙ : data` (or a group of such declarations that refer to each other). The
*shareable types* over the parameters `ā` are

```text
σ ::= aᵢ                    a parameter
    | int | float | string  a base type
    | U σ₁ … σₘ             a shared type of the group or declared before, with shareable arguments
```

It is an error if a constructor `c : (x₁ : σ₁) -> … -> (xₖ : σₖ) -> R` of `T`

- has an argument type that is not shareable, in particular a function type, a universe, `⇑A`, `sym`, a
  relation, a meta type or an object type that is not shared;
- has a result `R` other than `T a₁ … aₙ` with exactly the parameters (no indices);
- uses `T` in an argument at other arguments than `ā` (no polymorphic recursion, which the object level
  rejects with E0205);
- depends on an earlier argument (the arrows are not dependent; labels are allowed and are column labels
  at the object level).

It is an error if a subtyping edge `c <: T` names a shared type.

A shared alias `name : data = string.` is a type definition at both stages.

These conditions are the intersection of what the two stages accept: the meta side needs strict
positivity (it holds, since no argument is a function type), and the object side needs first-order
argument types and uniform parameters. In terms of descriptions, the shareable types are the fixed
points of finite sums of finite products of parameters, base types, recursive positions and other shared
types.

### 5.3 Elaboration

A shared declaration elaborates to items of the existing core. For the group `T ā` with constructors
`cᵢ : σ̄ᵢ -> T ā`:

```text
T   : Type → … → Type                      (meta inductive family, stage 1)
cᵢ  : {ā : Type} → σ̄ᵢ¹ → T ā               (meta constructors)
T   : type → … → type                      (object family of types, stage 0)
cᵢ  : {ā : type} → σ̄ᵢ⁰ → T ā               (object constructors: fact constructors)

T.lift  : {ā : Type} {b̄ : type} → (a₁ → ⇑b₁) → … → (aₙ → ⇑bₙ) → T ā → ⇑(T b̄)
T.lift f̄ (cᵢ x₁ … xₖ) = cᵢ (L[σᵢ₁] x₁) … (L[σᵢₖ] xₖ)

T.reify : {ā : Type} → (a₁ → term) → … → (aₙ → term) → T ā → term
T.reify ḡ (cᵢ x₁ … xₖ) = '{ cᵢ $(R[σᵢ₁] x₁) … $(R[σᵢₖ] xₖ) }
```

where `L[σ]` and `R[σ]` are the liftings of §5.4 with the parameters `aⱼ` mapped to `fⱼ` (resp. `gⱼ`).
The names `T.lift` and `T.reify` are derived names in the way `r.check` is a derived constant; they are
ordinary meta functions, checked for coverage and termination like hand-written ones. In the clause of
`T.reify`, the quote of #76 contains object syntax, so `cᵢ` is the object constructor; before #76 the clause
was written without the quote (`cons $(F X) $(reify F Xs)`); since #76 it is
`'{ cons $(F X) $(reify F Xs) }` (see `docs/design/examples/lists.hgn`).

The two families have the same name and the same constructor names. They are distinct constants. A use
is resolved by the stage of its position (§5.6).

### 5.4 The lifting judgement

`Δ ⊢ τ ⇝ e` says that meta values of type `τ` can be turned into object code by the meta function `e`.
`Δ` maps parameters to liftings.

```text
                                  (a ↦ f) ∈ Δ
  ──────────────────── Base      ──────────── Param      ─────────────────── Code
  Δ ⊢ b ⇝ persist_b               Δ ⊢ a ⇝ f               Δ ⊢ ⇑A ⇝ [x] x
  (b ∈ int, float, string)

  T shared    Δ ⊢ τ₁ ⇝ e₁   …   Δ ⊢ τₙ ⇝ eₙ
  ──────────────────────────────────────────── Shared
  Δ ⊢ T τ₁ … τₙ ⇝ T.lift e₁ … eₙ
```

The object type of the result is read off the same derivation: `b⁰ = b`, `(⇑A)⁰ = A`,
`(T τ̄)⁰ = T τ̄⁰`. The judgement is syntax-directed: at most one rule applies to each type, so a lifting,
if it exists, is unique. The judgement `Δ ⊢ τ ⇝ʳ e` for `reify` has the same rules with `tint`/`tfloat`/
`tstr` for the base types and `T.reify` for shared types, and no rule `Code` (opaque code cannot be
reified, §5.5).

The rule `Code` makes partially static data liftable: a meta `list (⇑int)` (a compile-time list of
object terms, such as the variables of a rule) lifts to the object list of those terms.

### 5.5 Stage inference

The staging chapter has one conversion from meta values to object code for values of base types
(persistence). The proposal replaces it with one rule:

```text
  Γ ⊢ e ⇒ τ  (stage 1)        · ⊢ τ ⇝ ℓ        τ⁰ ≤ A
  ────────────────────────────────────────────────────── Lift
  Γ ⊢ e ⇐ A  (stage 0)   elaborates to   $(ℓ e)
```

Persistence is the instance `τ = int` (`float`, `string`). It is an error (E0902, as today) if `τ` has no
lifting; the message names the first type in `τ` that is not shared.

The reflective counterpart applies inside a quote `'{ … }` (#76): a hole `$e` in a term position with
`e : τ`, where `τ` is not a reflective type and `· ⊢ τ ⇝ʳ r`, elaborates to `$(r e)`.

The specification that ties the two together, for closed `v : τ`:

```text
reflect (R[τ] v)  ≡  L[τ] v          (as object code)
```

that is, the term built by `reify` describes exactly the code built by `lift`. Both are folds over the
same constructors, and the equation holds by induction on `v`. This is the sense in which derived lifting
"coincides with the reflective embedding" of Q2. One function cannot be defined from the other inside the
language: `⇑A` cannot be inspected (Kovács 2022, §2.3 and §6), and a `term` becomes object code only at a
reflection site (`$e.` or an object position). So both are derived.

A reverse map `T.lower : (term → option a) → term → option (T a)` is definable with quoted patterns (a
hand-written instance for `onat` was checked on the current build), but it is partial and no prelude
code needs it. It is not derived (§8, question 5).

### 5.6 Name resolution

Each occurrence of a name declared by a shared declaration is elaborated at the stage of its expected
type, as every term is (reference: The meta level, Stages):

- in a rule, a query or an object type, and inside `'{ … }`, it is the object constant;
- in a clause, a meta type, a definition and a directive argument outside quotes, it is the meta
  constant;
- in a position whose expected type is `⇑A`, an object constant is used directly; `lift` is inserted only
  for a meta *value*.

The explicit quotes of #76 matter here. Before #76, object syntax in a position of a reflective type
was reified by expected type, so `cons X Xs` in such a position could be read as a meta constructor applied
to meta values or as quoted object syntax. With `'{ … }` (implemented) the content of a quote is always object syntax
and everything outside is not, so the stage of a shared name is never ambiguous.

`[a, b]` and `x :: xs` denote `cons`/`nil` of `list` at the stage of the position. In a rule head,
`held [X, Y]` is the object term `cons X (cons Y nil)`; in a clause, the meta list.

### 5.7 Soundness

The argument has four parts.

1. *Conservativity.* Everything §5.3 generates is a declaration or a definition of the current core: a
   meta inductive family, an object family with constructors, and two meta functions by clauses.
   `examples/lists.hgn` and `examples/typechecker.hgn` write them by hand and compile today. The rule Lift
   inserts an application of such a function. So every program with shared declarations is a program of
   today's core, and its meaning is the meaning of that program: the 2LTT semantics of the meta part,
   and the DL∃! semantics of the staged object program. No model needs extending.
2. *Totality.* `T.lift` and `T.reify` are structurally recursive folds with one clause per constructor:
   coverage and size-change termination hold by construction. The rule Lift is deterministic (§5.4).
3. *Identity.* Object identity is determined by the constant and its arguments (reference: Facts and
   identity). `lift` maps distinct constructors to distinct constants and is injective on each argument,
   so `lift v` and `lift w` are the same fact exactly when `v = w`. The subfacts that a head `H[lift v]`
   derives are `{ lift w | w a subterm of v of a shared type }`, the same set that the hand-written term
   derives. Subfact closure and the three readings of constructor terms in bodies are unchanged.
4. *Object well-formedness.* The restrictions of §5.2 ensure that the object family is a legal object
   declaration: first-order columns (no E0908), uniform parameters (no E0205), no bound columns (no E0605),
   no unions that overlap (the shared type is one open type with its own constructors, no edges).

The only new failure mode is in elaboration (no lifting for a type), and it is a type error at the use.

### 5.8 Interactions

- *Skolem identity.* As in §5.7, item 3. Lifting a large meta value into a body is an existence check of
  the whole tree; lifting it into a head asserts the tree. That is the reading of the same term written
  by hand.
- *Families and instances.* The object side is a family; its instances are memoised by type arguments
  (`list[int]`) as today. The meta side has no instances.
- *Modules and functors.* A shared declaration in a module body: the meta family is a component of the
  module value and the object family is generative like other object declarations. The derived functions
  are components named `T.lift`, `T.reify`. Recommendation: allow shared declarations at the top level of
  a file only in a first version, because the generativity of the meta side of a shared type inside a
  functor body would need its own design (§8, question 6).
- *Interfaces* (`docs/LIBRARIES.md`). An interface that exports a shared type exports both sides and its
  constructors; hiding constructors of a shared type is not allowed, since `lift` would expose them.
- *Reflective types.* `term`, `formula` and the others contain `sym` and are not shareable. They stay
  meta types, and their sequences become `list term` (§5.10).
- *`%demand`, `%derivations`.* Unaffected: they work on object syntax.

### 5.9 Formal reading: a stage-indexed declaration

Kovács (2022, §8) sketches a third stage that is polymorphic over the object and meta stages. A shared
declaration is the restriction of that idea to inductive declarations. Write `U s` for the universe of
stage `s ∈ {0, 1}` (`U 0 = type`, `U 1 = Type`). A shared declaration is a declaration

```text
T : (s : stage) → U s → … → U s → U s
cᵢ : (s : stage) → {ā : U s} → σ̄ᵢ[s] → T s ā
```

in a stage-polymorphic layer, together with the theorem `lift : T 1 ā → ⇑(T 0 b̄)` (given liftings of the
parameters), which is the fold. Hugin never abstracts over `s`: every use instantiates it, at the stage
of its position. This makes the stage-polymorphic layer a matter of elaboration with no stage variables
in the core, in the way universe levels are inferred and global (reference: Universes). Full stage
variables (a definition generic in `s` and used at both) are needed only for functions, and §6 argues
against those.

### 5.10 The prelude after the change

```hugin,ignore
list A : data.
nil : list A.
cons : (head : A) -> (tail : list A) -> list A.

option A : data.
none : option A.
some : A -> option A.

len : (l : list A) -> (n : int) -> rel.         (* unchanged: the length of the lists that are facts *)
len nil 0.
len (cons X L) M :- cons X L, len L N, M = N + 1.

append : list A -> list A -> list A.             (* was `sappend` on `seq` *)
append [] Ys = Ys.
append (X :: Xs) Ys = X :: append Xs Ys.

term : Type.  …  tapp : sym -> list term -> term.  …   (* `seq` becomes `list` throughout *)
module : Type = list item.
```

Removed: `seq`, `snil`, `scons`, `sappend`. `pair` stays an object struct; meta code uses record types.
`bool` stays a meta type. The change to the prelude is a renaming of `seq` to `list` in the reflective
types and the `%demand` code, which `[]` and `::` already hide in most places.

The typechecker example in the proposed form (with the quote syntax of #76):

```hugin,ignore
expr : data.  ref : string -> expr.  lam : string -> typ -> expr -> expr.  app : expr -> expr -> expr.
typ  : data.  base : string -> typ.  arrow : typ -> typ -> typ.
ctx  : data.  empty : ctx.  bind : ctx -> string -> typ -> ctx.

(* lookup, typed, program and result: the rules of examples/typechecker.hgn, unchanged *)

twice : nat -> expr.                    (* a meta function over the meta side of `expr` *)
twice zero = lam "x" (base "o") (ref "x").
twice (suc N) = lam "f" (arrow (base "o") (base "o")) (app (ref "f") (app (twice N) (ref "f"))).

program (twice 0).                      (* `expr.lift` is inserted *)
program (twice 1).
```

The meta copies of the three types (7 constructors), the five conversion clauses, and the local `maybe`
disappear. The meta checker `infer`, if the program wants one, stays as it is. The lists example
becomes:

```hugin,ignore
primes : list int = [2, 3, 5, 7].
held : list int -> rel.
held primes.                                        (* `list.lift persist` is inserted *)
suffixes : list int -> list rule.
suffixes [] = [].
suffixes (X :: Xs) = '{ held $(X :: Xs) } :: suffixes Xs.   (* `list.reify tint` is inserted *)
$suffixes [11, 13].
```

### 5.11 Alternatives considered

- *Implicit sharing of every first-order object type.* No new syntax, but object open types can gain
  members through edges, and making them closed implicitly changes their meaning. Rejected for the
  explicit marker of §5.1.
- *A liftable class with user instances.* Hugin has no type classes, and user instances would make
  stage inference depend on instance search. The closed judgement of §5.4 suffices.
- *First-class descriptions (levitation).* Generic `lift` by interpretation of a description. Adds a
  universe of descriptions to the meta level and needs the object level to interpret them, which it
  cannot. Rejected; descriptions inform the specification only.
- *Lifting only into `term`.* One derived function instead of two, since a `term` in an object position
  is reflected. Errors then appear in the converting function after reflection, not at the use (§4.5),
  and the result is untyped. Rejected as the primary map; kept as `reify` for directives.

## 6. Functions: costs and benefits

### 6.1 What a stage-polymorphic function would be

A definition by clauses, usable as a meta function on meta arguments and as a relation on object
arguments, with the relation generated as the guarded graph of the clauses and made demand-driven. For
`append` this is

```hugin,ignore
append : (xs : list int) -> (ys : list int) -> (zs : list int) -> rel.
%demand append +xs +ys -zs.
append nil Ys Ys.
append (cons X Xs) Ys (cons X Zs) :- append Xs Ys Zs.
```

which the current build accepts (demand by descent, the answers by guarded induction).

### 6.2 Example 1: `len` and `append` over lists

For `len` the translation is mechanical: the prelude's two rules are what it would generate, and they need
no demand because the recursion is on subterms of an existing fact. The benefit of not writing them is
two lines, once, in the prelude.

For `append`, which builds a list, the graph relation needs demand. Evaluated at compile time,
`held (append [1, 2] [3])` derives the facts `cons 1 (cons 2 (cons 3 nil))`, `cons 2 (cons 3 nil)`,
`cons 3 nil` and `nil`. Evaluated by the relation above, the query
`?- append (cons 1 (cons 2 nil)) (cons 3 nil) Z` leaves (checked with `--all-relations`) five `cons`
facts, among them the inputs `cons 1 (cons 2 nil)` and `cons 2 nil`, three `append` facts and three
`append.check` facts. A program that counts lists sees the difference.

For a function whose recursion is not structural on the input facts, the translation fails. The
reference's `ack` is accepted at the meta level. Its graph relation

```hugin,ignore
nat : type. z : nat. s : nat -> nat.
ack : (m : nat) -> (n : nat) -> (r : nat) -> rel.
%demand ack +m +n -r.
ack z N (s N).
ack (s M) z R :- ack M (s z) R.
ack (s M) (s N) R :- ack (s M) N R1, ack M R1 R.
```

is rejected with E0603: the demand of the inner call needs an answer of `ack`, which puts the demand
relation (descent) and the answers (guarded induction) in one component.

### 6.3 Example 2: a type checker

In `examples/typechecker.hgn` the object checker is three rules of `typed` and two of `lookup`, with
failure expressed by the absence of a fact and demand by `%demand`. The meta checker returns
`maybe mtyp`, compares types with `teq`, and threads failure through `arrowOf`, `applyT` and
`checkArg`. The graph relation of `infer` would be a relation `infer° : ctx -> expr -> maybe typ -> rel`
whose answers include `nothing` facts and whose rules build `just` facts: a different program from the
hand-written `typed`, and a worse one, since the relational checker needs no `maybe` at all. In the other
direction, the meta reading of `typed` would need a search over the rules, which a total meta function
cannot do without a bound.

What the example does share is the data: the AST, the types and the contexts. With §5 the program
builds test terms at compile time and states them as facts without any conversion code.

### 6.4 Example 3: a graph library

The object definition of reachability is the least fixed point of two rules (`tc` in the prelude). A meta
function must be structurally recursive, so `examples/graphs.hgn` iterates a step as many times as the
graph has edges and implements set operations on lists. The two definitions agree on the result (both
print 3) and have nothing in common structurally. A stage-polymorphic `reach` would have to be written in
the meta style (structural recursion with fuel), and its graph relation would then be a fuel-indexed
relation that recomputes what the two rules compute directly.

### 6.5 A library instead of a feature

A directive `%graph f` that generates the graph relation of a meta function cannot be written today:
directives receive object constants as `sym` and object syntax as reflective data, and there is no
reflective representation of meta clauses. Adding one (a `clause` type, reflection of meta definitions)
would be a large addition to the reflective embedding for this single purpose, and it would still need
the demand transformation and leave the termination of the result to the object check. The opposite
direction, generating a meta function from rules, needs a meta Datalog evaluator with fuel. Neither is
worth writing.

### 6.6 A variant: object evaluation of literal-valued functions

Formulog calls functions from rule bodies instead of translating them. In Hugin a function evaluated
inside a rule must not bind a variable to a constructor term that is not a fact: that breaks the
invariant that every value of a satisfying valuation has only facts as constructor subterms, which the
redesign established to remove probes and absent terms (`docs/REDESIGN.md`, §1.1 and §3.3). The variant
is sound only for functions whose result is a literal, such as `len : list A -> int`, applied to facts.
It would need the meta evaluator at run time, and the termination check would treat such a call like
arithmetic in a head, with no size information. The benefit is the `len` case of §6.2. Not recommended.

### 6.7 Recommendation

No stage-polymorphic functions. Shared data removes the mechanical part of the duplication (types,
constructors, conversion functions). What remains are meta functions and relations that are written
differently because the two stages compute differently: total structural recursion at compile time,
least fixed points over facts at run time. Translating one into the other brings back modes, makes the
set of facts depend on a stage choice, and moves termination errors into generated code.

## 7. A related defect found on the way

In a file with a module-wide directive, the rules and queries of the file are reified as data before the
directive runs (reference: Directives, Module-wide directives). Reification fails on a meta value in an
object position. The following file is rejected with E0917 at `k` ("expected object syntax of a term"),
and is accepted without the `%demand` line:

```hugin,ignore
k : int = 3.
held : int -> rel.
held k.
r : (x : int) -> rel.
%demand r +x.
r 1.
```

The same happens to `program (liftE idf)` in `examples/typechecker.hgn`, which therefore writes
`program $(reifyE idf)`. The reference does not mention the restriction, and `reference/DISCREPANCIES.md`
does not list it. #76 removes reification by expected type from user code, but the compiler still reifies
a file's items for module-wide directives, so the defect remains after #76.

Recommended fix, independent of this proposal: before reifying an item for a module-wide directive,
evaluate its closed meta subterms in object positions and reify their values: a base-type value as a
literal (`tint 3`), and, with §5, a value of a shared type with its `reify`. A meta subterm of type `⇑A`
that is not of a shared type cannot be reified (it is opaque) and remains an error, with a message that
says so. This deserves its own issue.

## 8. Open questions, with recommended answers

1. *Keyword.* `T ā : data.`, a directive form (`%shared`), or `T ā : type & Type`? Recommendation:
   `data`. A directive cannot generate meta declarations (directives produce object items), and a
   compound sort reads as a type former. `data` is one word and makes the closedness visible.
2. *Names of the derived functions.* `list.lift`/`list.reify`, or one overloaded `lift`? Recommendation:
   `T.lift` and `T.reify`, derived names like `r.check`. Hugin has no overloading, and stage inference
   inserts them in almost all uses; the names matter only when a lifting is passed as an argument.
3. *Implicit insertion.* Insert `lift` silently, or require `$` or an explicit call? Recommendation:
   implicit, by the rule Lift. It is the existing persistence rule generalised, deterministic, and typed
   at the use; `--print-after elaborate` shows the inserted call.
4. *Unify `seq` and `list` in the prelude.* Recommendation: yes, in the same change. It is the main
   duplication of the prelude, frees the list syntax for object code, and the renaming is mechanical.
   Do it after #76, since both touch the reflection code of the prelude.
5. *Derive `lower` and typed holes in quoted patterns.* Recommendation: no, until a directive needs to read
   constructor data out of rules. It is partial, needs `option` at both stages (which §5.10 provides), and
   typed holes in patterns need views or guards in clause patterns. A program that needs it writes it
   with quoted patterns today.
6. *Shared declarations in module bodies and functors.* Recommendation: top level only in the first
   version. The meta side of a type declared in a functor body would be generative too, which has no
   precedent in the meta level.
7. *Shared records* (`pair A B : data = { fst : A, snd : B }`). Recommendation: not now. Object structs are
   nominal fact types with labels, meta records are structural Σ types; a shared struct needs a decision
   on which equality the meta side has. Positional constructors with labels cover the cases seen so far.
8. *Stage-polymorphic functions later.* Recommendation: close the question with this note. Reopen only
   with a program whose meta and object definitions are the same clauses and that is too large to write
   twice; none of the examples examined here is one.
9. *The E0917 defect of §7.* Recommendation: file it as its own issue and fix it before or with #76; the
   fix for base types does not depend on this proposal.

## 9. References

- G. Allais. *Scoped and Typed Staging by Evaluation.* PEPM 2024. arXiv:2310.13413.
- D. Annenkov, P. Capriotti, N. Kraus, C. Sattler. *Two-Level Type Theory and Applications.*
  Mathematical Structures in Computer Science 33(8), 688–743, 2023. doi:10.1017/S0960129523000130;
  arXiv:1705.03307.
- M. Arntzenius, N. R. Krishnaswami. *Datafun: a Functional Datalog.* ICFP 2016.
  doi:10.1145/2951913.2951948.
- M. Arntzenius, N. R. Krishnaswami. *Seminaïve Evaluation for a Higher-Order Functional Language.*
  POPL 2020.
- A. Bembenek, M. Greenberg, S. Chong. *Formulog: Datalog for SMT-Based Static Analysis.* OOPSLA 2020,
  PACMPL 4 (OOPSLA), article 141. arXiv:2009.08361.
- J. Chapman, P.-É. Dagand, C. McBride, P. Morris. *The Gentle Art of Levitation.* ICFP 2010, 3–14.
  doi:10.1145/1863543.1863547.
- P.-É. Dagand, C. McBride. *Transporting Functions across Ornaments.* ICFP 2012.
- T. Gilray, A. Sahebolamri, Y. Sun, S. Kunapaneni, S. Kumar, K. Micinski. *Datalog with First-Class
  Facts.* arXiv:2411.14330.
- O. Kiselyov. *The Design and Implementation of BER MetaOCaml.* FLOPS 2014, LNCS 8475, 86–102.
- O. Kiselyov. *MetaOCaml: Theory and Implementation.* arXiv:2309.08207, 2023.
- A. Kovács. *Staged Compilation with Two-Level Type Theory.* ICFP 2022, PACMPL 6 (ICFP).
  doi:10.1145/3547641; arXiv:2209.09729.
- A. Kovács. *Closure-Free Functional Programming in a Two-Level Type Theory.* ICFP 2024, PACMPL 8
  (ICFP), 659–692. doi:10.1145/3674648.
- Lean 4: class `Lean.ToExpr` and the deriving handler `Lean.Elab.Deriving.ToExpr`
  (<https://lean-lang.org/doc/api/Lean/Elab/Deriving/ToExpr.html>); Mathlib `Mathlib.Tactic.DeriveToExpr`.
- C. S. Lee, N. D. Jones, A. M. Ben-Amram. *The Size-Change Principle for Program Termination.* POPL 2001.
- M. Madsen, O. Lhoták. *Fixpoints for the Masses: Programming with First-Class Datalog Constraints.*
  OOPSLA 2020, PACMPL 4 (OOPSLA).
- A. Pacak, S. Erdweg. *Functional Programming with Datalog.* ECOOP 2022, LIPIcs 222, 7:1–7:28.
  doi:10.4230/LIPIcs.ECOOP.2022.7.
- N. Stucki, A. Biboudis, M. Odersky. *A Practical Unification of Multi-stage Programming and Macros.*
  GPCE 2018. Scala 3 reference, Macros: <https://docs.scala-lang.org/scala3/reference/metaprogramming/macros.html>.
- W. Taha, T. Sheard. *MetaML and Multi-Stage Programming with Explicit Annotations.* Theoretical
  Computer Science 248, 2000.
- N. Xie, M. Pickering, A. Löh, N. Wu, J. Yallop, M. Wang. *Staging with Class: a Specification for Typed
  Template Haskell.* POPL 2022, PACMPL 6 (POPL). Template Haskell's `Lift` class and GHC's `DeriveLift`.
