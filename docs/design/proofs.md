# Proving properties of Datalog programs in the meta language

Design note for [issue #186](https://github.com/k0uks1/hugin/issues/186): the meta level should state and
prove properties of object-level Datalog programs, such as "this derived relation is transitive" and
"this rewrite derives the same facts". Status: research, for the designer's approval; nothing is
implemented. Written against `ccr-48027e29-daam41` at 28dbcb1. No program in this note was compiled: the
task allowed no builds, and the only launcher on the machine predates the redesign. Statements about
today's behaviour are read from the reference, `docs/NOTES.md` and the sources, and are cited.

Contents: 1 recommendations, 2 Hugin today, 3 gap analysis, 4 logical consistency today, 5 prior art,
6 a meta-level semantics of Datalog programs, 7 worked examples, 8 batches, 9 decisions for the
designer, 10 sources.

## 1. Recommendations

1. **First make the logic honest (batch P1).** Today False takes three lines: any meta declaration that
   is not a family or a constructor is a *postulate* (reference `meta/index.md`, "Meta items"), and
   `boom : (A : Type) -> A.` is one. Postulates should need an explicit marker (`= %postulate`, by
   analogy with `= %builtin`), and a `--safe` mode should reject them. A command should list the
   assumptions a definition depends on (Lean's `#print axioms`, Rocq's `Print Assumptions`). Apart from
   postulates, this note found no way to derive False (section 4). One combination should still be
   closed before proofs matter: forced large indices together with recursion on forced arguments, which
   Agda forbids under `--safe` (Agda issue #6654).
2. **A small proof library and proof ergonomics (P2).** This means a closed `std/eq`, with `refl`, `sym`,
   `trans`, `cong`, `subst` and J written as ordinary clauses, plus `empty`, `unit` and `dec`. Also:
   explicit implicit arguments `f {n = e}` and implicit patterns; *opaque theorems*, which are never
   unfolded or eagerly evaluated and are exempt from the unused-definition lint (W0003); and decidable
   equality of atoms with evidence (`same` gives only a `bool`). All of this is useful without the
   Datalog goal: equations about `std/nat` and `std/list`, and proofs about directive code.
3. **The deep semantics as the specification (P5, P6).** This is a library `std/semantics` written in
   Hugin over the reflective types that already exist (`module`, `rule`, `formula`, `term`). It has a
   universal value type that follows DL∃!'s identity of facts, and derivability as an inductive family
   (the proof-theoretic least model, closed under subfacts). Stratified negation is handled stratum by
   stratum, as in Benzaken, Contejean and Dumbrava (ITP 2017). Aggregates and bound columns come last.
   The library needs no compiler change beyond P2, and it makes generic theorems about module-wide
   directives (`module -> module`) stateable.
4. **Shallow semantic families for concrete programs (P7).** The compiler derives one meta inductive
   family per relation, with one constructor per rule, parameterised by a *model* of the relations it
   reads. Functors become the unit of proof: "for every graph `g`, `(tc g).path` is transitive" is a
   theorem about `tc.path.sem m` for every model `m`. Such families can be written by hand today:
   example 7.1 proves transitivity, and 7.2 the equivalence of two closure programs, in today's syntax.
   The derived families are tied to the deep semantics by an adequacy lemma. That lemma starts out
   trusted (and listed among the assumptions) and is generated as a proof later.
5. **The engine stays trusted, with a certificate mode (P8).** Verifying the Scala engine is out of
   reach, and a meta-level engine would be far too slow. Hugin already emits derivation facts
   (`%derivations`). P8a exports them as Datalog proof trees in the JSON format of Tantow, Gerlach,
   Mennicke and Krötzsch (ITP 2025), whose Lean checker is verified. P8b adds a post-run validation
   phase that runs a meta-level checker, proven sound against `std/semantics`, on the reified output:
   proof trees give soundness, and a one-round model check gives completeness.
6. **Not now:** a `Prop` universe or definitional proof irrelevance, tactics or meta-level elaborator
   reflection, a separate kernel, and univalence. Erasure comes for free: meta code never reaches the
   object program. Proof automation should be proof by reflection (`decide`), which suits Hugin's fast,
   memoised evaluator, together with the language server's existing goals and case splits.

## 2. Hugin today

The meta level is "a total, dependently typed functional language: a two-level type theory" (reference
`meta/index.md`). As a proof language it has the following.

- **Universes.** There is a cumulative, predicative hierarchy `Type₀ : Type₁ : …`. Levels are inferred,
  are global to a program, and are not polymorphic. `Type : Type` is E0904 (reference
  `meta/universes.md`; `core/Levels.scala`). `type` is the universe of object types; it is first order,
  and `⇑type : Type₀` (NOTES "Decisions (B1)").
- **Π, implicit Π, records.** Records are dependent Σ types with eta, and functions have eta
  (`core/Unification.scala`, header comment). Lambdas are written `[x] e`. Implicit arguments are
  solved by pattern unification. They "cannot be written explicitly" and are not written in patterns;
  the names of a function's own implicit binders are in scope in its clauses (reference
  `meta/functions.md`, `meta/clauses.md`).
- **Inductive families.** Every argument is an index, and there are no parameters. Positivity is
  strict, including nesting through families that are positive in that argument. Implicit binders of
  a constructor that occur in its result type "do not count" for predicativity (reference
  `meta/families.md`; `core/elab/Inductives.scala`, `forcedBinders`). A family may have no
  constructors, which makes it an empty type. Its constructors are the declarations of the same file
  that return it, so a family is closed to other files.
- **Dependent pattern matching.** Clauses compile to case trees (Cockx and Abel 2018). Index
  unification is the full Cockx–Abel unifier *with* K: deletion, solution, injectivity, conflict and
  cycle, on constructors and literals only. Stuck equations are postponed, then reported as E0915.
  Absurd patterns `()` are allowed (`core/elab/SplitProblem.scala`, `IndexUnifier`; NOTES "Decisions
  (B2)").
- **Totality.** Coverage is checked over probes, with emptiness decided one level deep (reference
  `meta/coverage.md`). Termination uses the size-change principle over constructor subterms. Calls
  through definitions and record fields are followed; a function passed as a value is a call with
  unknown arguments (reference `meta/termination.md`; `core/elab/SizeChange.scala`). A cycle's bodies
  do not unfold until its termination check is done (reference `meta/index.md`, "Order of
  elaboration").
- **Equality.** There is no built-in identity type, but one can be declared as an ordinary family. The
  tests do so monomorphically (`eqn : nat -> nat -> Type. refl : eqn N N.`, for example in
  `tests/run/nat_offsets.hgn`), and coverage uses one to decide a split (reference `meta/coverage.md`,
  "Undecided splits"). The prelude's `same : A -> A -> bool` compares atoms (literals and symbols) and
  is stuck on everything else (`core/Primitives.scala`). It returns no evidence.
- **Numbers.** `nat` has numerals, offsets and native arithmetic that is checked against its clauses
  when `std/nat` is elaborated, as Agda does with its built-ins (reference `std/nat.md`, "Native
  arithmetic"). The meta `int` is 64-bit; its overflow is stuck, and the meta level has no comparison
  operators (reference `meta/functions.md`, "Literals and primitive operations").
- **Staging.** `⇑A` is opaque: it is spliced, never inspected (reference `meta/staging.md`). Module
  bodies are generative: there is one instance per evaluation site, and `Tm.Fresh` advances a hygiene
  counter. NOTES calls both "effects" of evaluation (NOTES "Glued evaluation").
- **Reflection.** Object syntax is available as data: `term`, `formula`, `rule`, `item` and `module`,
  with `'( … )` quotes, quoted patterns and `$m.` to reflect data back into the program (reference
  `reflection.md`). `quoted A` is a phantom-typed term whose constructor `qterm` is unchecked
  (NOTES "Typed object code (#56)"). A module-wide directive is a meta function `module -> module`
  over the file's rules (reference `directives.md`, "Module-wide directives"). There is no reflection
  of *meta* terms.
- **Holes.** `?` is an error (E0924), and the language server shows its goal and offers case splits
  (reference `meta/functions.md`, "Typed holes"). There are no unsolved-meta or incomplete-match escape
  hatches; `%partial` was removed in redesign A3 (NOTES "Termination").

So the meta level is intended to be MLTT with K, inductive families, cumulative predicative universes,
Σ and Π with eta, primitive base types and an opaque code type, plus postulates.

## 3. Gap analysis

Sources: Agda a3f41e8 (manual `doc/user-manual/language/*.lagda.rst`, `src/full/Agda/...`), Lean 4
0bb12a8 (`src/...`) and Rocq 29f5238 (`doc/sphinx/...`, `theories/Corelib/...`).

| feature | Agda | Lean 4 | Rocq | Hugin today | needed for #186? |
|---|---|---|---|---|---|
| identity type and eliminator | `_≡_` in `src/data/lib/prim/Agda/Builtin/Equality.agda`; J by matching | `inductive Eq : α → α → Prop` (`src/Init/Prelude.lean`:73); `Eq.rec` | `Inductive eq` (`theories/Corelib/Init/Logic.v`:379); `eq_rect` | user-declared family; J by clauses | yes: P2 `std/eq` |
| K / UIP | on by default; `--without-K` (`without-k.lagda.rst`); unifier `TypeChecking/Rules/LHS/Unify.hs` | definitional proof irrelevance gives UIP | UIP not provable in general; an axiom (`Eqdep`) | K by the deletion rule (`SplitProblem.scala`) | keep K (D9) |
| Prop universe | `--prop` (`prop.lagda.rst`), matching only by `()` into `Set` | impredicative `Prop`; large elimination only for subsingletons (`src/kernel/inductive.cpp`, `elim_only_at_universe_zero`, :510) | `Prop`, `SProp` (`language/core/sorts.rst`; empty/singleton elimination, `language/core/inductive.rst`:1306) | none | no (D6) |
| proof irrelevance, erasure | `irrelevance.lagda.rst`; `@0` (`runtime-irrelevance.lagda.rst`) | `Prop` erased by the compiler; `lcProof` (`Prelude.lean`:242) | extraction erases `Prop` (`addendum/extraction.rst`) | the whole meta level is erased by staging | free; opaque theorems for compile time (P2) |
| induction principles | by matching; `TermCheck.hs` (`src/full/Agda/Termination/`) | generated recursors; structural or well-founded (`src/Lean/Elab/PreDefinition/{Structural,WF}`) | `Fixpoint`, generated `_rect`/`_ind` | by matching, size-change | enough; no infinitary (applied-subterm) recursion |
| inductive families as evidence | yes | yes | yes | yes (example 7.1) | already there |
| params vs indices | declared parameters; `--large-indices` off by default since 2.6.4 | declared, plus `inductive.autoPromoteIndices` (`src/Lean/Elab/MutualInductive.lean`:52, `fixedIndicesToParams`) | declared parameters | no parameters; forced implicit binders exempt from predicativity | P1 (D2) |
| `with` / rewrite | `with-abstraction.lagda.rst` (with, rewrite, inspect) | `rw` (`src/Lean/Elab/Tactic/Rewrite.lean`), `match h :` | `rewrite` (`proofs/writing-proofs/equality.rst`) | `where`-local functions only; `subst` after P2 | P3, optional |
| explicit implicits, implicit patterns | `{x = e}`, `{n}` | `(x := e)`, `@f` | `(x:=e)`, `@f` | no | P2 |
| tactics / elaborator reflection | `TC` monad, macros (`reflection.lagda.rst`) | tactic framework (`src/Lean/Elab/Tactic/*`: `simp`, `omega`, `grind`, `decide`) | Ltac, Ltac2 | reflection of object syntax only | no; proof by reflection (P4) |
| assumption tracking | `--safe` (`safe-agda.lagda.rst`) | `#print axioms` (`src/Lean/Elab/Print.lean`); `sorryAx` (`Prelude.lean`:794) | `Print Assumptions` | none: postulates are silent | P1 |
| partial definitions | `TERMINATING` pragma, not `--safe` | `partial def` is opaque, needs `Inhabited` (`src/Lean/Elab/PreDefinition/MkInhabitant.lean`) | none in the core | none (`%partial` removed) | already there |
| trusted arithmetic | built-in `Nat`, checked against its definition | kernel GMP acceleration (`src/kernel/type_checker.cpp`, `reduce_nat`, :668) | `Uint63`, `Float64` primitives | native `std/nat`, checked against its clauses | already there |
| small kernel | no (the type checker is the kernel) | yes | yes | no (the elaborator is the kernel) | no (D7) |
| two-level | `--two-level`, `SSet` (`two-level.lagda.rst`) | — | — | staging 2LTT, `⇑A` opaque | section 6 |

What is missing for proofs, in order of need:

1. **Postulate hygiene** (P1). Agda's `--safe` refuses `postulate` ("can be used to assume any axiom",
   `safe-agda.lagda.rst`). In Hugin a typo can create a postulate: a declaration whose type does not end
   in a family of the same file is one.
2. **Equality and its library** (P2). The machinery for J is there; a closed library and a convention
   are not. Without universe polymorphism there is one `eq` per program, whose type argument lives at
   the maximal level used. Cumulativity and the forced-binder exemption keep `eq` itself in `Type₀`.
3. **Naming implicit arguments** (P2). Proofs often need an index (`{m}`, `{x}`), and today a clause can
   only use the names of its function's own implicit binders.
4. **Opaque theorems** (P2). NOTES "Glued evaluation" says the unfolded value of a definition is
   computed eagerly. A theorem should be checked and then never unfolded (Agda's `opaque`,
   `opaque-definitions.lagda.rst`; Lean's `theorem`). W0003 would also report every theorem that
   nothing refers to.
5. **Decidable equality with evidence** (P2). The semantics needs `(a b : sym) -> dec (eq a b)` and the
   same for literals. That requires a conflict rule for distinct symbols in index unification (literals
   have one already) and a primitive whose `no` branch is a checkable absurd function.
6. **A theory of integers** (P5). The meta `int` has no comparisons and a stuck overflow, so it cannot
   model the object level's 64-bit arithmetic in proofs. A `zint` defined over `nat`, with native
   acceleration like `std/nat`, is consistent by construction (D8).
7. **`with`/rewrite** (P3) is convenience. `subst` and a `where`-local helper (Agda's "inspect" idiom)
   already express it.
8. **Automation.** For closed, finite programs a checker `check : … -> bool` with a soundness lemma
   proves goals by `refl` (Rocq's ssreflect `reflect`, Lean's `decide`, `src/Lean/Elab/Tactic/Decide.lean`).
   This needs no tactic language (P4).

## 4. Logical consistency today

**Can False be proved now? Yes, by a postulate.** By reference `meta/index.md` ("Meta items") and
`meta/families.md` ("Syntax"), `boom` below is a postulate, since its type ends in a variable, not in a
family of the file. `empty` is a family without constructors, and `absurd : empty` type-checks. E0909
only fires if *object* code depends on a stuck value, and a proof never reaches object code.

```hugin
empty : Type.
boom : (A : Type) -> A.
absurd : empty = boom empty.
```

(`boom : empty.` would not do: it would declare a *constructor* of `empty`.) Lean has `sorryAx` and
Agda has `postulate`; the difference is that both mark and track them (`#print axioms`, `--safe`).

Apart from postulates, here is each hole the issue names.

| hole | today | verdict |
|---|---|---|
| type-in-type | E0904; universes checked as difference constraints (`core/Levels.scala`) | closed |
| `type : type` | the object universe classifies itself, but holds only first-order object types, with no Π and no meta types (NOTES "Decisions (B1)") | harmless: a set-theoretic model interprets `⇑A` as sets of object terms |
| `%partial`, `TERMINATING`, unsolved metas, incomplete matches | none: `%partial` removed, `?` is E0924, E0911 and E0912 are errors, and an item with an error fails the compilation | closed |
| unchecked escapes | `qterm` (unchecked phantom type of `quoted A`); `same`, `labels`, `derive`, `derived`, `qatom` reduce only on canonical arguments and are stuck otherwise (`core/Primitives.scala`) | not logical escapes, since they assert no equation. `quoted A` is not evidence that the term has type `A` |
| native arithmetic | `std/nat` is checked against its clauses when the library is elaborated; the meta `int` is Scala arithmetic | trusted code, as in Agda and Lean |
| coverage | probes; emptiness one level deep; an absurd pattern needs a conflict; undecided splits are errors | sound (it only rejects more) |
| index unification | constructors and literals only (`SplitProblem.scala`, lines 99–178). The rule that solves `c α = c Y` as `α := Y` for a stuck `c` belongs to elaboration's unifier (`meta/functions.md`), where it picks *a* solution; it does not belong to index unification | sound. K holds; UIP is consistent with MLTT |
| positivity | strict, nested through positive families (E0913) | closed |
| termination | size-change over constructor subterms; no applied-subterm rule; unknown calls through values | sound by Lee et al. 2001, modulo the next row |
| forced large indices and forced-argument recursion | forced implicit binders do not count for predicativity (`Inductives.scala`, `forcedBinders`). At a leaf, a variable that index unification solved inside a constructor term counts as a subterm (`SizeChange.scala`: "the clause's patterns, as terms of the leaf") | **to close (D2).** Agda calls this combination "known to be inconsistent" (`--large-indices`, `doc/user-manual/tools/command-line-options.rst`) |
| generativity | functor bodies create fresh constants per evaluation site; closed applications are memoised "since meta functions are total and have no effects" (`meta/clauses.md`) | not a source of False, but evaluation is not referentially transparent across items (D10) |
| 2LTT staging | `⇑A` has no eliminator into the meta level; quotes are syntax, not semantics | closed: the object level cannot feed facts into the meta logic |

**The forced-index row in detail.** Agda's counterexample (`test/Fail/Issue6654a.agda`) declares
`data Bad : ((P : Set) → P → P) → Set` with `b : (f : …) → Bad f`, and recurses with
`no-bad (b x) = no-bad (x _ bad)`. Two things make it go through. The forced argument `f` lives in
`Set₁` but is not counted, and Agda's termination checker counts `x _ bad`, an *applied* subterm, as
smaller than `b x`. In Hugin the exemption applies only to *implicit* forced binders:
`b : {f : (P : Type) -> P -> P} -> Bad f.` puts `Bad` in `Type₀`. The function `no-bad` can reach `f`
through its own implicit binder. But the size-change relation holds only for a *variable* below a
constructor (reference `meta/termination.md`), so `no-bad (F _ bad)` is an unknown call, E0912. The
note found no derivation of False. Still, Hugin has exactly the two features that Agda now refuses to
combine under `--safe`, and the argument for its safety rests on a missing termination rule (applied
subterms), which proofs over infinitely branching trees will one day want. D2 closes it as Lean does:
promote fixed indices to parameters and exempt only parameters.

**Trusted base.** Hugin has no kernel: the whole elaborator, the evaluator and native arithmetic are
trusted, as in Agda. That is acceptable while the goal is to catch mistakes rather than to certify for
third parties. A core re-checker is the long-term answer (D7).

## 5. Prior art

**Verified Datalog engines.**

- Benzaken, Contejean and Dumbrava, *Certifying Standard and Stratified Datalog Inference Engines in
  SSReflect*, ITP 2017 (LNCS 10499, 171–188), released as DatalogCert. The development formalises the
  model-theoretic and fixpoint semantics of Datalog and of its stratified extension, and implements
  them by bottom-up and stratified evaluation, with proofs of soundness, termination, completeness and
  model minimality. They chose bottom-up evaluation because loop-freedom of top-down or optimised
  strategies is harder to establish. The stratified engine reuses the standard one per stratum. This
  is the closest model for Hugin's deep semantics (6.2). Their engine *is* the proof object; Hugin's
  engine is not, so Hugin takes their semantics, not their architecture.
- Bonifati, Dumbrava and Gallego Arias, *Certified Graph View Maintenance with Regular Datalog*, TPLP
  18(3–4), 2018 (ICLP). Regular Datalog is a fragment with transitive closure as a primitive; an
  incremental engine is proven sound in Coq and extracted to OCaml.
- Bégay, Crégut and Monin, *Developing and Certifying Datalog Optimizations in Coq/MathComp*, CPP 2021.
  A static analysis and two program transformations are certified on top of the Coq/MathComp
  formalisation, with a new trace semantics. Their transformations are what Hugin's module-wide
  directives are; a "rewrite preserves the facts" theorem (7.3) is the same kind of result.
- Schlichtkrull, Hansen and Nielson, AFP entry *Stratified Datalog* (2025; SAC 2024 paper
  *Isabelle-verified correctness of Datalog programs for program analysis*). It proves that every
  stratified program has a least solution, and proves five bit-vector analyses correct. These are
  proofs *about specific Datalog programs* against the least-solution semantics, which is exactly
  #186's goal, in Isabelle.
- Tantow, Gerlach, Mennicke and Krötzsch, *Verifying Datalog Reasoning with Lean*, ITP 2025 (LIPIcs
  352, 36). This is a Lean checker for Datalog proof trees and proof DAGs in a tool-independent JSON
  format. The model-theoretic and proof-theoretic semantics are proven equivalent
  (`modelAndProofTreeSemanticsEquivalent`), and a model checker (`checkPGR`) validates that a result is
  closed under the rules. Evaluated on traces of Nemo. This is the certificate route of 6.6.
- Shahin, *A Shallow Embedding of Datalog in Lean*, arXiv 2605.02113 (2026). Datalog relations map to
  native Lean inductive predicates, and backward-chaining queries become theorems proved by tactics.
  This is the shallow route of 6.3.

No Agda formalisation of Datalog semantics was found.

**Refinement-style verification.** Liquid Haskell's refinement reflection (Vazou et al., POPL 2018)
turns terminating functions into logic equations, with proofs as unit-returning functions and SMT
discharge. F* separates total, ghost and erased computation and has Meta-F* tactics. The lessons for
Hugin: proofs as ordinary total functions are enough for programs of this size; arithmetic wants a
decision procedure (here proof by reflection over `nat`/`zint`, P4); and erasure must be guaranteed,
which staging already does.

**Two-level type theory.** Annenkov, Capriotti, Kraus and Sattler, *Two-level type theory and
applications* (MSCS 2023; arXiv 1705.03307): the outer level has a strict equality and reasons about
inner types through it. Agda implements this as `--two-level` with `SSet`, where UIP holds for the outer
equality even under `--without-K` (`two-level.lagda.rst`). Kovács, *Staged compilation with two-level
type theory* (ICFP 2022), on which Hugin's stage inference is built (NOTES "Architecture"), keeps
`⇑A` opaque so that staging is sound for every model of the object theory. Hence the meta level cannot
learn anything about object *semantics* from `⇑A`. Semantics has to enter as an explicit model inside the
meta level: a deep embedding over reflected syntax, or derived shallow families, connected to the
object program by an adequacy statement. This is the main design consequence of the 2LTT literature for
#186. An outer equality on `⇑A` (Agda's `≡ˢ`) would give only *syntactic* equality of object code, which
is not the property users want.

**Provenance and monotonicity.** Soufflé's provenance evaluation (Zhao, Subotić and Scholz, TOPLAS 2020)
produces proof trees for derived facts; Hugin's `%derivations` does the same per rule (reference
`object/io.md`, "Derivation facts"). Datafun (Arntzenius and Krishnaswami, ICFP 2016) types
monotonicity; in Hugin, monotonicity of a negation-free program is a theorem of the deep semantics
(6.2), not a type discipline.

## 6. A meta-level semantics of Datalog programs

### 6.1 What has to be modelled

The object level is Datalog∃! with stratified negation, aggregates, 64-bit partial arithmetic,
floats, strings and bound columns (reference `object/index.md`). Its meaning is the iterated least
fixpoint, per component, of

```
IC_R(db) = db ∪ ⋃ { subfact(Head(R)[v/x]) | db ⊨ Body(R)[v/x] }
```

(REDESIGN §3.3). The identity of a fact is determined by its constant and its arguments (reference
`object/facts.md`), and bodies never create facts.

### 6.2 The deep semantics (`std/semantics`, P5–P6)

The deep semantics is a library over the reflective types, so that the reflected or reified program
*is* the object of proof.

```hugin
%use "std/reflect". %use "std/eq".
value : Type.                          (* a value of the object level: DL∃!'s identities *)
vint : zint -> value.                  (* zint: the integers by clauses over nat (D8) *)
vstr : string -> value.
vfact : sym -> list value -> value.    (* the fact c v̄; identity = constant and arguments *)
gatom : Type = { rel : sym, args : list value }.
db : Type = gatom -> Type.             (* a set of facts, as a predicate *)
subst : Type = list { name : string, val : value }.
```

- **Terms and formulas.** `evalT : subst -> term -> option value` evaluates terms. Arithmetic is checked
  for 64 bits through `zint`, so an undefined operation gives `none`, matching "a formula that contains
  an undefined operation does not hold" (reference `object/arithmetic.md`). The satisfaction family
  `sat (pos neg : db) s φ` reads positive atoms from `pos` and `not` from `neg`, the complete lower
  strata. `fdisj` is a sum. An existence check `X = c t̄` is membership of `vfact c …` in `pos`.
- **Derivability.** For a positive component, derivability is an inductive family:

  ```hugin
  derivable : list rule -> db -> db -> gatom -> Type.     (* rules, lower strata, input *)
  input : {rs : list rule} -> {lo d : db} -> {a : gatom} ->
          d a -> derivable rs lo d a.
  fire  : {rs : list rule} -> {lo d : db} -> {a : gatom} -> {r : rule} -> {s : subst} ->
          member r rs -> all (premise rs lo d s) (body r) -> headFact s r a -> derivable rs lo d a.
  sub   : {rs : list rule} -> {lo d : db} -> {a b : gatom} ->
          derivable rs lo d b -> subfactOf a b -> derivable rs lo d a.
  ```

  `premise` is the satisfaction of one body formula with `derivable rs lo d` as `pos` and `lo` as
  `neg`. The family occurs nested inside `all`, which is strictly positive in its predicate, the same
  pattern as `tapp : sym -> list term -> term`. That `premise` passes `derivable rs lo d` unsaturated
  to `all` is a positivity case to confirm in P5. If the checker rejects it, `premise`/`all` become a
  family mutual with `derivable`. This is the proof-theoretic least model (Tantow et al.'s proof
  trees). The model-theoretic one ("the least `db` closed under the rules") follows as a theorem, as
  in their `modelAndProofTreeSemanticsEquivalent`.
- **Strata.** `model : list (list rule) -> db -> db` is defined by clauses over the strata. It is
  Type-valued recursion, which Hugin allows (`sel : bool -> Type` in reference `meta/clauses.md`):
  `model [] d = d` and `model (c :: cs) d = derivable c (model cs d) (model cs d)` (lowest stratum
  last), as in Benzaken et al.'s stratified engine. The stratification is the compiler's; the library
  states, but need not recompute, the side condition that `not` reads only lower strata.
- **Aggregates (P6).** `count`, `sum`, `min` and `max` need finite sets: the semantics takes a list of
  valuations, a proof that it has no duplicates, and a proof that it is complete for the body over the
  lower strata. That is heavy but standard. Bound columns (Limit Datalog with ±∞) come last and may
  stay out of scope.
- **Floats** stay uninterpreted: a value that can only be compared for equality.

Theorems this enables: monotonicity of negation-free rule sets in the input; correctness of
module-wide directives (`(p : module) -> iff (derivable (rules p) …) (derivable (rules (dir p)) …)`);
"at most N facts" for programs with finite carriers. The last one needs a finite enumeration of the
model and is the most expensive.

### 6.3 Shallow semantic families (P7)

For a concrete program, the deep semantics is clumsy: rules are data, and substitution is explicit.
The shallow embedding gives each relation `r : τ̄ -> rel` a meta family `r.sem`, with one constructor
per rule of `r`, whose arguments are the rule's variables and body atoms:

- **Carriers.** An object type of a functor parameter, such as `g.node`, becomes a carrier field
  `node : Type` of a *model record*. The model of the signature `graph = { node : type, edge : node ->
  node -> rel }` is `{ node : Type, edge : node -> node -> Type }`: object types become `Type` and
  relations become predicates. A concrete program uses `value` (with a typing predicate) as the carrier.
- **Heads and bodies.** A head term `c X` becomes the index `vfact c [X]`. A body atom becomes a
  constructor argument, and `not p t̄` becomes `p.sem … t̄ -> empty`. Strict positivity holds because
  stratification puts `p` in an earlier family. Comparisons and arithmetic go through `zint`.
- **Functors.** `tc : graph -> …` gives `tc.path.sem : (m : model graph) -> m.node -> m.node -> Type`.
  A theorem quantifies over models, never over instances, so proofs never evaluate a functor
  application and generativity does not arise (D10).
- **Derivation.** The derivation is like `T.lift`/`T.reify` for shared data (`core/elab/DerivedFunctions.scala`):
  generated declarations that "can be written by hand", checked like hand-written ones. Example 7.1
  writes them by hand.

### 6.4 Connecting reflection, semantics and the engine

The chain from a theorem to the facts that a run prints has four links.

1. **Theorem → shallow or deep semantics.** This link is checked by the meta level.
2. **Shallow → deep (adequacy).** For a relation `r` with reified rules `R`, `r.sem m ā` is inhabited
   iff `derivable R … (r ā)` is. For P7 the compiler can generate the proof: each constructor is one
   rule instance, so the proof is a structural translation both ways. It starts as a trusted lemma that
   `--print-assumptions` lists (D3).
3. **Deep semantics → staged program.** A program written as data (`rules : module = '( … ). $rules.`)
   is the shortest path: theorems about `rules` are about what is reflected. For hand-written rules,
   the module a module-wide directive receives is the same reification (reference `directives.md`). The
   trusted steps are re-elaboration of reflected data, hygiene renaming, formula-function inlining and
   the Scala transforms (`obj/transform/{Disjunctions,Records}.scala`). The semantics models the source
   forms (`fdisj`, records as facts), so these transforms stay inside the trusted base.
4. **Staged program → output.** This link is the engine: semi-naive evaluation in
   `runtime/{Engine,Evaluation}.scala`.

### 6.5 Trusted, verified or certified engine

| option | what it gives | cost | verdict |
|---|---|---|---|
| trusted | theorems hold of the reference semantics; the engine is tested against it | none | default |
| verified (Benzaken et al.) | the engine is the proof | the engine would have to be meta code or proven Scala: a rewrite, and orders of magnitude slower | rejected |
| meta-level reference engine | a naive `IC` fixpoint in Hugin, proven against `derivable`, evaluated at compile time for closed programs | P5 plus about 400 lines of Hugin; feasible only for small programs | optional: differential testing of the engine |
| certificate per run (Tantow et al.) | soundness from proof trees (`%derivations` plus negative premises); completeness from a one-round model check | P8 | recommended as an opt-in mode |

### 6.6 Certificates (P8)

`%derivations` already gives, for each rule instance, the derived fact and its positive premises
(reference `object/io.md`). A certificate needs, in addition, the instances' negative premises and
aggregate witnesses, plus the input facts. With those, P8a exports the derivation facts as Tantow et
al.'s JSON proof DAG for the pure fragment, so that their verified Lean checker validates a run. That
is useful immediately for debugging and auditing, and needs no proofs in Hugin. P8b adds a post-run
phase (`--certify`): the driver reifies the input, the output and the derivations as meta data, and the
evaluator runs `check : module -> facts -> derivs -> bool`, proven in Hugin against `derivable`:
`check … = true -> ∀ a ∈ out, derivable … a`. A model check (`closed : module -> facts -> bool`, one
naive round) adds completeness, and negation then rests on checked lower strata. The meta evaluator is
slow on large outputs, so this is a CI and audit mode, not the default.

## 7. Worked examples

The syntax follows the reference. 7.1 and 7.2 use only features that exist today, with the semantic
families written by hand. P7 would derive them from `std/graph`'s `tc`, and P2 would add the
explicit-implicit conveniences. 7.3 needs P2 and P5.

### 7.1 Reachability is transitive

The shallow semantics of `tc` (`std/graph`: `path X Y :- g.edge X Y.` and `path X Z :- g.edge X Y,
path Y Z.`), written by hand:

```hugin
model : Type = { node : Type, edge : node -> node -> Type }.   (* the model of `graph` *)

path : (m : model) -> m.node -> m.node -> Type.
step1 : {m : model} -> {x y : m.node} -> m.edge x y -> path m x y.
step2 : {m : model} -> {x y z : m.node} -> m.edge x y -> path m y z -> path m x z.

trans : {m : model} -> {x y z : m.node} -> path m x y -> path m y z -> path m x z.
trans (step1 E) Q = step2 E Q.
trans (step2 E P) Q = step2 E (trans P Q).
```

Coverage: the two constructors. Termination: `P` is a variable inside the constructor pattern
`step2 E P`. Universes: `model : Type₁`. `path` stays in `Type₀` only because `m`, `x` and `y` are
forced implicit binders, which is today's exemption. Under D2, `m` is a fixed first index promoted to a
parameter, so `path` still lives in `Type₀`.

With P7, `path` is `tc.path.sem` and `step1`/`step2` are its rule constructors. The statement about the
actual relation then reads: for every instance `t = tc g` and every run whose input determines the model
`m`, `t.path a b` is printed iff `tc.path.sem m ⟦a⟧ ⟦b⟧` is inhabited (adequacy, 6.4). So `trans`
proves that every instance of `tc`, in every run, derives a transitive relation.

### 7.2 Two closure programs derive the same facts

The left-linear rule `path X Z :- path X Y, g.edge Y Z.` in place of the right-linear one:

```hugin
lpath : (m : model) -> m.node -> m.node -> Type.
lstep1 : {m : model} -> {x y : m.node} -> m.edge x y -> lpath m x y.
lstep2 : {m : model} -> {x y z : m.node} -> lpath m x y -> m.edge y z -> lpath m x z.

lcons : {m : model} -> {x y z : m.node} -> m.edge x y -> lpath m y z -> lpath m x z.
lcons E (lstep1 F) = lstep2 (lstep1 E) F.
lcons E (lstep2 P F) = lstep2 (lcons E P) F.

toL : {m : model} -> {x y : m.node} -> path m x y -> lpath m x y.
toL (step1 E) = lstep1 E.
toL (step2 E P) = lcons E (toL P).

toR : {m : model} -> {x y : m.node} -> lpath m x y -> path m x y.
toR (lstep1 E) = step1 E.
toR (lstep2 P F) = trans (toR P) (step1 F).

iff : Type -> Type -> Type = [a] [b] { to : a -> b, from : b -> a }.
sameFacts : {m : model} -> {x y : m.node} -> iff (path m x y) (lpath m x y) = { to = toL, from = toR }.
```

Under adequacy, `sameFacts` states that both programs print the same `path` facts for every input. A
"rewrite" here is a hand edit. 7.3 makes it a transformation.

### 7.3 A module-wide rewrite preserves the derived facts (deep)

A module-wide directive that reverses the body of every rule, of the kind a join-order optimiser
would apply:

```hugin
%use "std/reflect". %use "std/directives". %use "std/list". %use "std/eq". %use "std/semantics".
revRule : rule -> rule.
revRule (horn Hs B) = horn Hs (reverse B).
revBodies : list rule -> list rule = [rs] map revRule rs.

(* body satisfaction is order-independent *)
allRev : {P : formula -> Type} -> {fs : list formula} -> all P fs -> all P (reverse fs).
(* … by induction on fs, with allSnoc : all P fs -> P f -> all P (append fs [f]) *)

memberMap : {r : rule} -> {rs : list rule} -> member r rs -> member (revRule r) (revBodies rs).

sound : {rs : list rule} -> {lo d : db} -> {a : gatom} ->
        derivable rs lo d a -> derivable (revBodies rs) lo d a.
sound (input X) = input X.
sound (fire M Ps H) = fire (memberMap M) (allRev (mapAll sound Ps)) H.
sound (sub D S) = sub (sound D) S.
```

`complete`, the converse, is the same proof with `reverse (reverse B) = B`, which is a `std/eq` lemma
used through `subst`. `mapAll sound Ps` recurses into the nested `all`, and the size-change check
accepts it if `mapAll` is a local function whose calls `sound` sees (as for `tree.lift.1`, reference
`meta/families.md`). Otherwise `sound` and its `all` case are written as two mutually recursive
functions. `headFact` reads only `heads r`, but `revRule r` reduces only on a constructor, so the
`fire` case first splits `r` into `horn Hs B`, through a `where`-local helper. Then `H` carries over
unchanged. This is the kind of step that P3's `with` shortens. Together, `sound` and
`complete` make `revBodies` a *verified* directive: `%reorder` can be used with the guarantee that it
changes no fact.

## 8. Batches

Each batch is one PR. Line counts are rough (Scala plus Hugin library plus reference and tests).
"Standalone" marks batches that are useful even if the full goal is never reached.

| batch | content | lines | unlocks | risks | standalone |
|---|---|---|---|---|---|
| **P1** honest logic | `x : A = %postulate.`; an unmarked postulate is a warning, then an error (D1); `--safe`; `--print-assumptions` / `%assumptions f.` (postulates, trusted primitives, adequacy lemmas); index promotion to parameters and forced-binder rule (D2); reference: a "Consistency" section | 500–800 | trustworthy proofs | migration of programs that rely on silent postulates; D2 may move a few families up a level | **yes**: catches typos that make postulates |
| **P2** proof basics | `std/eq` (J, `subst`, `cong`, `sym`, `trans`), `empty`, `unit`, `dec`, `iff`; explicit implicits `f {n = e}` and implicit patterns; `%opaque` theorems (no unfolding, no eager evaluation, W0003 exempt); `decEq` for atoms with a symbol conflict rule; polymorphic families confirmed | 900–1400 | 7.1–7.3 conveniences; lemmas about `std/nat` and `std/list` | parser space for `{n = e}` next to records and implicit binders (reference `meta/records.md`, brace disambiguation) | **yes** |
| **P3** `with` / rewrite | `with` abstraction desugared to a `where`-local function over the abstracted goal; `rewrite e` via `subst` | 600–900 | shorter proofs | Agda's experience: ill-typed abstractions; the error messages | yes |
| **P4** proof by reflection | `std/decide`: `so : bool -> Type`, `decide`; `less`/`equal` lemmas for `nat` | 300–500 | arithmetic side conditions, small finite models | evaluation cost (bounded by memoisation and native `nat`) | **yes** |
| **P5** deep semantics, positive | `std/semantics`: `value`, `zint`, terms, formulas without negation, `derivable` with subfacts, monotonicity, the model-theoretic equivalence; possibly a positivity extension for unsaturated nesting | 1200–1800, mostly Hugin | 7.3; theorems about directives | positivity of the nested `all`; meta evaluation speed | partly (a reference semantics in the language) |
| **P6** negation and aggregates | strata (`model`), `not`, `count`/`sum`/`min`/`max` with finite witnesses; bound columns maybe later | 1000–1500 | full stratified Datalog∃! | aggregate proofs are heavy | no |
| **P7** shallow families | `%semantics r` or functor: derived `r.sem`, model records of signatures, rule constructors; adequacy lemma trusted first, then generated | 1200–1800 | 7.1/7.2 tied to real relations | head unification with arithmetic; open types across files (closed-world carrier, D4) | no |
| **P8a** proof-tree export | negative premises in `%derivations`; Tantow et al. JSON export | 300–500 | external verified checking of runs | format drift | **yes** |
| **P8b** certified runs | `--certify`: reified output checked by a meta checker proven against P5/P6 | 800–1200 | per-run guarantees without a verified engine | meta evaluator speed on large outputs | no |

Order: P1 → P2 → (P4, P3) → P5 → P7 → P6 → P8b. P8a can go at any time.

## 9. Decisions for the designer

| | decision | options | recommendation |
|---|---|---|---|
| D1 | postulate syntax and policy | keep silent postulates; marker `= %postulate` with a warning; marker required (error) | marker, a warning for one release, then an error with a quick fix; `--safe` rejects marked ones too |
| D2 | forced large indices | keep; Agda 2.6.4 (count forced large binders); Lean (promote fixed indices to parameters, exempt only parameters); exclude forced large binders from size-change | Lean's promotion, which keeps `vec A`, `quoted A`, `eq` and 7.1 small, plus Agda's default for the rest |
| D3 | semantics first | deep only; shallow only; deep, then shallow with adequacy | deep as the specification (P5), shallow (P7) with an adequacy lemma that is trusted and listed at first, generated later |
| D4 | carrier of values | `⇑A` (syntactic: wrong for arithmetic); a mirror type per object type; one universal `value` plus a typing predicate | universal `value`; functor proofs use abstract model carriers. Open types: the carrier is closed over the whole program at staging |
| D5 | engine | trusted; verified; certificate | trusted by default, certificate mode (P8); no verified engine |
| D6 | `Prop`, irrelevance | add `Prop`/`SProp`; none | none for now; revisit if quotients or subset types with proof fields are needed |
| D7 | automation and kernel | tactics; meta reflection; proof by reflection; core re-checker | proof by reflection (P4) and the language server's goals; a core re-checker only if proofs must convince third parties |
| D8 | integers in proofs | trusted `int` axioms; `zint` by clauses over `nat` with native acceleration | `zint`: consistent by construction, like `std/nat` |
| D9 | K | keep; `--without-K` | keep: UIP is consistent, simplifies matching, and Hugin has no univalent ambitions |
| D10 | generativity | ignore; forbid functor instantiation in opaque theorems; theorems about models only | theorems about models (6.3); audit whether memoised closed applications can share a module instance across items |

## 10. Sources

- agda/agda a3f41e8: `doc/user-manual/language/{safe-agda,postulates,prop,irrelevance,runtime-irrelevance,with-abstraction,reflection,without-k,two-level,termination-checking,opaque-definitions}.lagda.rst`,
  `doc/user-manual/tools/command-line-options.rst` (`--large-indices`, `--forced-argument-recursion`),
  `src/data/lib/prim/Agda/Builtin/Equality.agda`, `src/full/Agda/TypeChecking/Rules/LHS/Unify.hs`,
  `src/full/Agda/TypeChecking/Forcing.hs`, `src/full/Agda/Termination/TermCheck.hs`,
  `test/Fail/Issue6654{a,b,c}.agda`; issue agda/agda#6654, PR #6661, CHANGELOG 2.6.4.
- leanprover/lean4 0bb12a8: `src/Init/Prelude.lean` (`Eq` :73, `lcProof` :242, `sorryAx` :794),
  `src/Init/Core.lean` (`propext` :1605), `src/kernel/inductive.cpp` (`elim_only_at_universe_zero`
  :510), `src/kernel/type_checker.cpp` (`reduce_nat` :668), `src/Lean/Elab/MutualInductive.lean`
  (`inductive.autoPromoteIndices` :52, `fixedIndicesToParams`), `src/Lean/Elab/PreDefinition/{Structural,WF,MkInhabitant}`,
  `src/Lean/Elab/Tactic/{Rewrite,Induction,Decide,Omega,Grind}.lean`, `src/Lean/Elab/Print.lean`.
- rocq-prover/rocq 29f5238: `doc/sphinx/language/core/{sorts,inductive}.rst`,
  `doc/sphinx/addendum/{sprop,extraction,rewrite-rules}.rst`,
  `doc/sphinx/proofs/writing-proofs/equality.rst`, `theories/Corelib/Init/Logic.v` (`eq` :379).
- V. Benzaken, É. Contejean, S. Dumbrava: Certifying Standard and Stratified Datalog Inference Engines
  in SSReflect, ITP 2017, LNCS 10499, 171–188 (doi 10.1007/978-3-319-66107-0_12; HAL hal-01745566).
- A. Bonifati, S. Dumbrava, E. J. Gallego Arias: Certified Graph View Maintenance with Regular Datalog,
  TPLP 18(3–4), 2018 (arXiv 1804.10565).
- P.-L. Bégay, P. Crégut, J.-F. Monin: Developing and Certifying Datalog Optimizations in Coq/MathComp,
  CPP 2021.
- A. Schlichtkrull, R. R. Hansen, F. Nielson: Stratified Datalog, Archive of Formal Proofs, 2025
  (theories `Datalog`, `Bit_Vector_Framework`, `Reaching_Definitions`, …); SAC 2024.
- J. Tantow, L. Gerlach, S. Mennicke, M. Krötzsch: Verifying Datalog Reasoning with Lean, ITP 2025,
  LIPIcs 352, 36.
- R. Shahin: A Shallow Embedding of Datalog in Lean, arXiv 2605.02113.
- N. Vazou et al.: Refinement Reflection: Complete Verification with SMT, POPL 2018. F* and Meta-F*
  (Martínez et al., ESOP 2019).
- D. Annenkov, P. Capriotti, N. Kraus, C. Sattler: Two-level type theory and applications, MSCS 2023
  (arXiv 1705.03307). A. Kovács: Staged compilation with two-level type theory, ICFP 2022.
- D. Zhao, P. Subotić, B. Scholz: Debugging Large-scale Datalog: A Scalable Provenance Evaluation
  Strategy, TOPLAS 2020. M. Arntzenius, N. Krishnaswami: Datafun, ICFP 2016.
- C. S. Lee, N. D. Jones, A. M. Ben-Amram: The size-change principle for program termination, POPL 2001.
  J. Cockx, A. Abel: Elaborating dependent (co)pattern matching, ICFP 2018.
- Hugin 28dbcb1: `reference/src/meta/{index,universes,families,clauses,coverage,termination,functions,staging,records}.md`,
  `reference/src/{reflection,directives}.md`, `reference/src/std/{nat,reflect}.md`,
  `reference/src/object/{index,facts,arithmetic,bound-columns,aggregates,io,termination}.md`;
  `core/elab/{SplitProblem,SizeChange,Inductives,DerivedFunctions}.scala`, `core/{Primitives,Unification,NatArithmetic}.scala`,
  `src/main/resources/hugin/stdlib/{prelude.hgn,std/reflect.hgn,std/graph.hgn,std/directives.hgn,std/nat.hgn}`;
  `docs/NOTES.md` (Architecture, Decisions B1/B2, Typed object code, Glued evaluation, Approximate
  conversion); `docs/REDESIGN.md` §3.3, §6.3, §6.5.
