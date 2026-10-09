# Typed object code in the meta level

Design note for [issue #56](https://github.com/k0uks1/hugin/issues/56), including the triage items C1
(functor bodies are not object-typed once) and C2 (`⇑τ ≤ ⇑τ'` at the meta level) of
`docs/history/TRIAGE.md`. Status: approved by the designer and implemented (batches A and B); the
decisions of the implementation, and where it deviates from this note, are in `docs/NOTES.md`, "Typed
object code (#56)".

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 design, 5 alternatives, 6 effects,
7 migration, 8 sources.

## 1. Recommendations

1. **Object typing moves into the core.** The object type system (subtyping, meets, fact types, operand
   rules) is implemented once, over core values, as a constraint engine. The elaborator feeds it while it
   elaborates object code at stage 0, so object code inside meta functions, formula functions, quotes
   and functor bodies is checked where it is written. `ObjTyper` is deleted.
2. **One boundary check remains**, the analogue of Lean's kernel: staged items whose code came from
   meta code are checked again by the same engine, for what only the staged item shows (the meet of a
   variable that was passed into a generator, instance-specific subtyping). Items without meta code are
   not checked twice.
3. **C1:** a functor body is object-typed once, with the parameters' types abstract (opaque). **C2:**
   `⇑` is covariant: `⇑τ ≤ ⇑σ` if `τ ≤ σ`, decided by the core.
4. **Typed reflection follows Qq and Scala:** a typed layer over the untyped data, not intrinsically
   typed syntax. `quoted τ` wraps a `term` with a phantom object type. A quoted pattern binds a hole at a
   position of known object type `σ` as `quoted σ` (`typed $E $G $T` gives `E : quoted expr`), and quote
   content is elaborated as object code, so a generator that misplaces a hole is rejected at its
   definition. The quoted-pattern syntax does not change.
5. **Untyped reflection stays** as the representation and the escape hatch (`term`, `formula`, `rule`,
   `item`, `module`, `decl`), as `Expr` in Lean and `quotes.reflect` in Scala. Reflected data is always
   elaborated again (unchanged); `%demand` and other directives that are generic over all relations stay
   untyped.
6. **No index for contexts.** Rule variables are names whose types are meets of their uses; a formula's
   free variables compose by meet. Aggregates stay locally nameless. Generated variable names get a
   reserved form that source syntax cannot produce, as Lean encodes macro scopes inside names.

## 2. Hugin today

Object code in the core is ordinary core syntax at stage 0 (`Tm.App` of object constants, whose types
are object arrows), plus `Tm.Obj` for the forms without a meta counterpart (`core/ObjForm.scala`). The
core types it by unification (`core/elab/ObjectCode.scala`), with one exception:
`Coercions.coeObjectData` keeps a term whose object data type does not unify with the expected one and
leaves the decision to `obj/typing/ObjTyper.scala`, which runs on the staged program after the handover.

Measured on 68a74fb (scratch programs, not committed):

| program | result |
|---|---|
| `bad : int -> prop.  bad N = typed (lit N) (lit N).` (column 2 is `typ`), unused | accepted |
| the same, used in `ok 1 :- bad 1.` | E0402 at the generator's text, found after staging |
| `swap : ⇑expr -> ⇑typ -> ⇑prop.  swap E T = typed T E.` | E0901 at the definition |
| `w : var -> prop.  w X = up X.` with `up : expr -> prop`, `var <: expr` | E0901 (a valid upcast rejected) |
| a functor body `out X :- g.edge X X.` with `out : (x : expr) -> rel` | accepted per instance |

So the core is already strict where meta code meets object code (`⇑τ` against `⇑σ` is unification,
invariant), and lenient where object terms meet object types. The first rejects correct programs (C2),
the second accepts ill-typed generators until they are used. Variable types by meets (Definition 6.1 of
the draft) exist only in `ObjTyper`, so an implicit object type argument that only a meet determines is
reported at staging (E0909, NOTES "Open issues (after Phase B)").

Reflection (`docs/NOTES.md`, "Reflection", "Explicit quotes (#76)") is untyped: quotes are reified from
syntax (`core/elab/QuoteTerms.scala`) without object typing, holes have reflective types (`$E : term`),
and reflected data is turned into syntax and elaborated like hand-written code (`Reflection.scala`).

## 3. Prior art

Clones at: lean4 0bb12a8, quote4 e7c4cdd, scala3 1095192, AndrasKovacs/staged 9c4e201; GHC's
`ghc-internal` TH sources fetched from master on 2026-10-09. MetaOCaml was not read from source and is not
used as evidence below.

### 3.1 Lean 4

- **Representation.** `Expr` (`src/Lean/Expr.lean`, `inductive Expr`) is untyped and locally nameless:
  `bvar` de Bruijn indices under binders, `fvar` for variables of the local context, `mvar` for holes.
  Typing is external: `inferType` (`src/Lean/Meta/InferType.lean`, `inferTypeImp`) *assumes* a
  type-correct term; `Meta.check` (`src/Lean/Meta/Check.lean`, `checkAux`) re-checks applications and
  binders with `isDefEq`.
- **Re-checking.** An elaborator returns an `Expr`; `elabTermEnsuringType` and `ensureHasType`
  (`src/Lean/Elab/Term/TermElabM.lean`) compare `inferType e` with the expected type by `isDefEq` and
  insert a coercion or fail. Every declaration goes through the kernel (`src/Lean/AddDecl.lean`,
  `Kernel.Environment.addDecl`, skipped only with `debug.skipKernelTC`). Untyped metaprograms are safe
  because of this boundary.
- **Syntax quotations.** `Syntax` (`src/Init/Prelude.lean`, `inductive Syntax`) is untyped;
  `TSyntax ks` is a wrapper indexed by syntax categories whose doc comment says the index "is not
  otherwise enforced". `stxQuot.expand` and `quoteSyntax` (`src/Lean/Elab/Quotation.lean`) turn a
  quotation into code that builds the tree; antiquotations `$x` are inserted as `TSyntax.raw`. Syntax
  patterns are compiled by `compileStxMatch`/`getHeadInfo` into checks on node kinds and arities
  (`HeadCheck.shape`): no types.
- **Hygiene.** `quoteSyntax` adds the macro scope of the current expansion to every identifier a
  quotation introduces (`addMacroScope quotCtx val scp`) and pre-resolves global names at the
  quotation's site (`Syntax.Preresolved`). Scopes are encoded inside the name with the reserved component
  `_hyg` (`Name.hasMacroScopes`, `addMacroScope` in `src/Init/Prelude.lean`); `withFreshMacroScope`
  starts a new expansion. `Quotation/Precheck.lean` resolves identifiers of quoted terms early to report
  unbound names at the quotation.

### 3.2 Qq (quote4)

- `Quoted α` (`Qq/Typ.lean`) is `Expr` with a phantom index (`def Quoted (α : Expr) := Expr`);
  `Quoted.unsafeMk` is the unchecked constructor, `Quoted.check` the checked one (`inferType`, `isDefEq`),
  and `CoeOut (Quoted α) Expr` forgets the index implicitly.
- `q(t)` (`Qq/Macro.lean`, `Impl.macro`) elaborates `t` with Lean's own term elaborator in an
  *unquoted* local context, in which every variable `x : Q(α)` of the meta program becomes a variable
  `$x : α` (`unquoteLCtx`); the result is checked by `ensureHasType` against the unquoted expected type and
  quoted back into an `Expr`-building term. The object code is type-checked when the metaprogram is
  elaborated, by the same elaborator that checks hand-written terms.
- `~q(pat)` (`Qq/Match.lean`, `elabPat`, `mkIsDefEqCore`) elaborates the pattern in the unquoted context;
  pattern variables are metavariables whose types the elaboration determines (`$a : α`), and may be
  functions (`getPatVars`, arity). Matching runs `isDefEq` at reducible transparency under
  `withNewMCtxDepth`, so it matches up to definitional equality.

### 3.3 Scala 3

- `Expr[+T]` and `Type[T]` (`library/src/scala/quoted/Expr.scala`, `Type.scala`) are the typed layer;
  `quotes.reflect` trees are the untyped one. `asExprOf[T]` (`QuotesImpl.asExprOf`) is a checked cast
  that throws `ExprCastException`; `asTerm` forgets the type.
- `typedQuote` (`compiler/src/dotty/tools/dotc/typer/QuotesAndSplices.scala`) types the quote body with
  the ordinary typer at the next level (`quoteContext`); `typedSplice` types a splice against `Expr[T]`
  one level down. Level consistency is a separate check (`staging/CrossStageSafety.scala`).
- Quoted patterns: `typedQuotePattern` types the pattern body as an expression in pattern mode; a hole
  gets type `Expr[pt]` from the expected type at its position, a higher-order hole `$f(x̄)` the type
  `Expr[(T̄) => pt]` (`typedSplicePattern`, `typedAppliedSplice`). The matcher
  (`compiler/src/scala/quoted/runtime/impl/QuoteMatcher.scala`) matches structurally and checks the
  type of the matched code against the hole's (`typeOf('{e}) <:< T`).
- Reflect constructors build typed trees (`QuotesImpl`, `Apply.apply` calls `tpd.Apply`); extra
  well-formedness checks run only with `-Xcheck-macros`. Escaping local variables are rejected after
  expansion (`transform/Splicer.scala`, `checkEscapedVariables`).

### 3.4 Kovács, staged 2LTT

- The demo elaborator (`demo/Elaboration.hs`) has one bidirectional `check cxt t a st` and
  `infer`/`inferS` indexed by the stage; object terms are checked against object types by the same
  algorithm (`(P.Quote t, VLift a) -> check cxt t a S0`, and any term checked against `VLift a`). `coe`
  inserts quotes, splices and `Lift` and falls back to unification; `⇑` is invariant
  (`(VLift a, VLift a') -> unifyCatch`).
- Staging (`demo/Staging.hs`) assumes well-typed input (`impossible` on ill-typed cases); the paper
  (ICFP 2022, §5) proves that staging preserves typing, so no re-check is needed.
- §6 of the paper: intensional analysis of `⇑A` is not stable in the presheaf model; analysable syntax
  should be a deep embedding (the STLC example, `demo/examples/STLC.2ltt`, uses intrinsically typed
  syntax).

### 3.5 Typed Template Haskell

`Code m a` and `TExp a` (`GHC/Internal/TH/Monad.hs`) are newtypes over the untyped `Exp`; typed quotes
`[|| … ||]` are checked when the quote is constructed (the doc comment's `True == "foo"` example);
`unsafeCodeCoerce` and `unTypeCode` convert between the layers. `TExp`'s parameter is nominal so that
`coerce` cannot change the claimed type. `Lift.liftTyped` (`Lift.hs`) is the typed counterpart of `lift`.

### 3.6 What the references agree on

1. **Object code is typed by the elaborator that types hand-written code**, when the metaprogram is
   elaborated: Kovács (one stage-indexed `check`), Qq (`q(…)` runs Lean's elaborator), Scala
   (`typedQuote` runs the typer). Hugin's deferral to a later typer is the exception.
2. **The typed layer is a phantom index over an untyped representation** (`Quoted α := Expr`,
   `Code m a` over `Exp`, `Expr[T]` over trees), with an unchecked and a checked conversion and an
   implicit or explicit forgetful one. Intrinsically typed syntax appears only as a user-level deep
   embedding (Kovács's STLC).
3. **Holes in patterns get types from their position** (Scala: `Expr[pt]`; Qq: elaborated pattern
   variables); higher-order holes get function types.
4. **There is a trusted boundary check on the final result** where untyped construction is allowed:
   Lean's kernel, Scala's `asExprOf`/`-Xcheck-macros`. Kovács needs none because nothing untyped exists.
5. **Hygiene is by names with scopes** in Lean's syntax (macro scopes encoded in names), by symbols in
   Scala; core `Expr` is locally nameless.

## 4. Design

### 4.1 One constraint engine, two feeders

`core/objtype/` holds the object type system over core values: `ObjTypes` (subtyping, members, meet,
join; a port of `obj/typing/TypeOps.scala` from `OType` to `Val`), `ObjConstraints` (a store per scope:
variable bounds, postponed checks, and their solution; a port of `RuleTyper.run`), and the problems
(today's `TypingProblems`, codes unchanged). It is fed by

- **the elaborator**, while it checks object code at stage 0: `coe` between object types emits a
  subsumption check, an occurrence of an object variable emits a bound, and a check that depends on a
  variable's type is postponed; the store of a scope is solved when the scope ends (4.3);
- **the boundary walker**, which synthesises the types of a staged item's closed object code (constants,
  literals, variables, `Tm.Obj` forms) and feeds the same store (4.5).

This is Kovács's architecture with one Hugin-specific addition: object variables are not typed at their
binder but by the meet of their uses, a property of a whole rule, so their checks are postponed to the
end of the scope, as Lean postpones elaboration problems to the end of a declaration.

### 4.2 The judgements

- **Subtyping** `τ ≤ σ` on stage-0 types: base types and their refinements; open types with the edges
  `τ <: a` and the result types of constructors (`FactTy c ≤ T` for `c : τ̄ -> T`); fact types of
  relations and structs below `rel`; unions member-wise; family applications invariant in their
  arguments. Edges are declarations, elaborated before object items; edges of a module body are part of
  the body's context.
- **Polarity.** A position is *constructing* (a head, a constructor term in a head, the fields of `with`)
  or *matching* (body atoms, comparisons, aggregates). Constructing positions require `τ ≤ σ` (E0402
  "type mismatch"). In matching positions a constructor term or literal requires `τ ≤ σ` (E0402 "pattern
  can never match"), a variable adds the bound `σ`, and code of type `⇑τ` whose shape is unknown (a
  spliced parameter) requires that `τ` and `σ` meet.
- **Variables.** The type of a rule variable is the meet of its bounds (E0401 if empty); then equations
  and aggregates type the variables without bounds, and the postponed checks run (heads, projections
  `X.l` on closed types, comparisons, arithmetic, ascriptions as checked downcasts, E0405).
- **Families and implicit arguments.** A meet of two applications of the same family unifies their
  arguments, so implicit object type arguments are solved by meets inside the elaboration of the item.
  What stays unsolved is E0206 at the item, not E0909 at staging.
- **Fact identity, bound columns.** `t as X` gives `X : FactTy c`; a column `min τ` holds values of
  `τ`. E0605 stays where it is; E0606 needs the components and stays in `obj/check`.
- **Shared data (#80).** The object side of `T ā : data.` is an ordinary object family, so nothing is
  special; `T.lift`'s clauses build object constructor terms and are checked once, at their definition.

### 4.3 Scopes

A store is opened and solved for: a rule or query (its variables); a clause or definition of a meta
function whose body contains object code (its `Tm.Fresh` variables); an entry of a quote (4.6); a module
body (once, see C1). Parameters of type `⇑τ` are fixed types, not bounds.

**C1.** A functor body is elaborated once with its parameters as variables; their object types are
abstract: `g.node ≤ σ` holds only for `σ = g.node` or what the body's own edges give. A head that needs
`g.node ≤ expr` is rejected at the body, as an ML functor body or Kovács's rigid variables would be.
Meets with an abstract type are left to the boundary check of the instance (they can only make a rule
dead, never produce an ill-typed fact). The functor program in §2 becomes an error at the body; the fix
is to give the parameter the concrete type (`edge : expr -> expr -> rel`).

### 4.4 `⇑` at the meta level (C2)

`coe` relates `⇑τ` and `⇑σ` by `τ ≤ σ` (identity coercion), contravariantly in function domains as
`coeOpt` already does. With an unsolved side it unifies, as now. `w X = up X` of §2 is accepted;
`down X` with `down : var -> prop` and `X : ⇑expr` stays an error, now worded as an object subtyping
failure inside E0901.

### 4.5 The boundary check

After staging, an item whose elaboration involved meta code (a splice, a formula function, a generic
family rule, a module instance, reflected data) is checked again by the engine; other items keep the
result of their elaboration. What the boundary check can still find:

- a variable passed to a generator that uses it at a narrower type than its parameter, so that the meet
  over the whole staged rule is empty (E0401, a dead rule);
- instance-specific subtyping: an edge from a family instance (`list int <: foo`) used by a generic rule,
  or a meet with an abstract type of a functor body.

Both carry the provenance notes of today. The check produces the variable types the object phases use
(`CompilationUnit.varTypes`, filled by `ObjTyper` now). Reflected data (`$e.`, directives, `term` and
`formula` values in object code) is elaborated like hand-written code, unchanged, and is the other
place where untyped construction is re-checked.

### 4.6 Typed reflection

Following 3.6 (2), the typed layer is a phantom index over the untyped data, not an intrinsically typed
syntax and not `⇑`:

```text
quoted : ⇑type -> Type.          (* prelude *)
qterm  : term -> quoted A.        (* unchecked, the escape hatch: Qq's unsafeMk *)
raw    : quoted A -> term.
```

- `quoted τ ≤ term` is an implicit coercion (`raw`), and `quoted τ ≤ quoted σ` if `τ ≤ σ` (Scala's
  `Expr[+T]`). A `quoted τ` value in object code stands for its term, as a `term` does today.
- **Holes in quoted patterns.** The hole `$X` at an argument of a resolved object constant whose column
  type `σ` is closed binds `X : quoted σ` (the clause binds the data and defines `X = qterm X'` in its
  `where` block, as higher-order holes do now). `$..Xs` stays `list term`, a hole whose position has no
  known type (`$R $X $Y`) stays `term`, formula and entry holes stay `formula`/`rule`/`item`, `$F[V]`
  stays `term -> formula`.
- **Quote content is elaborated as object code**, then reified from the elaborated term (Qq's `q(…)`)
  instead of from syntax: an entry is elaborated like a rule in the quote's meta context, a hole of type
  `quoted σ` is a stage-0 placeholder of type `σ`, a hole of type `term` a placeholder of unknown type, a
  meta value of a base or shared type a placeholder of its lifted type (its data is still `tint e` or
  `T.reify ḡ e`). The engine checks the entry (4.3). So in the prelude-style `guard`,
  `'{ typed.check $T $G }` with `T : quoted typ` is E0402 at `guard`'s definition.
- **No match-time type test.** Scala's matcher tests the matched code's type; here the hole's type is
  assumed, because data can be ill-typed only through `qterm` or hand-built constructor terms, and every
  piece of data is elaborated again when it is reflected. An ill-typed input then fails at reflection,
  with the provenance of today; case trees and coverage are unchanged.
- `⇑` stays opaque (Kovács §6): no conversion from `⇑τ` to data is added.

### 4.7 What stays untyped

`term`, `formula`, `rule`, `item`, `module`, `decl`, `sym` stay as they are: the representation, the
target of reification, and the type of directives that are generic over all relations (`%demand` works
for any `R : sym` with heterogeneous columns, which no type index describes). Typed formulas get no
index: a formula has the object sort `prop`, and its well-typedness is checked where it is built (4.6)
and where it is reflected (4.5).

### 4.8 Names, locally nameless, hygiene

- Rule variables stay names. A formula's free variables are the variables of the rule it is reflected
  into (reference chapter "Reflection"), and their types compose by meet, so a typed index for contexts
  would add nothing. Aggregate binders stay locally nameless (`tbound`).
- Staged code is hygienic already (`Tm.Fresh`, `X#k`). For reflected data, a generated variable name
  gets a reserved form that source syntax cannot produce, as Lean puts `_hyg` into names with macro
  scopes; the prelude's `%demand` invents `_a`, `_ba`, … today, which a program can capture. Reflection
  accepts the reserved form and prints it as now (`X#k`).

## 5. Alternatives rejected

- **Keep `ObjTyper` as the checker of hand-written code and add a core checker for generators.** Two
  implementations of one type system, which drift apart; the issue asks for one checker. The
  boundary check reuses the engine instead.
- **Fully integrated subtyping in `coe` with variable metas solved by unification.** It would type
  `typed X X` by the first occurrence and miss meets; variable types in Datalog are a property of the
  rule, so postponement to the end of the scope is required.
- **Intrinsically typed reflective families** (`term : ⇑type -> Type` with typed constructors, as in
  Kovács's STLC). Object subtyping would need proof-relevant upcasts in data, argument lists become
  heterogeneous, and `%demand` could not be written. No reference does this for its metaprogramming API.
- **Typed holes as `⇑σ`** (Scala's `Expr[T]` is both staging and pattern type). Needs reification of
  `⇑`, which Kovács §6 and `docs/design/stage-polymorphism.md` §3 exclude; `⇑` stays opaque.
- **A match-time type test for typed holes** (Scala's `<:<`). Needs guards in case trees and an
  elaboration per matched hole; the reflection re-check gives the same safety.
- **Abstract functor parameters checked per instance** (C1 unchanged). Errors per application instead of
  once; rejected in favour of the ML discipline, with the meets deferred.

## 6. User-visible effects

Newly rejected, at the definition:

- generators whose object code is ill-typed, also when unused (`bad N = typed (lit N) (lit N).`, E0402);
- formula functions with ill-typed comparisons or projections (`cheap I = I.price < "x"`, E0402);
- functor bodies that rely on an abstract parameter type being a subtype of a concrete one (§4.3);
- quotes whose content is ill-typed (`'{ edge 1 "x" }` with `edge : node -> node -> rel`, E0402), and
  quotes in directives that misplace typed holes.

Newly accepted: upcasts of `⇑` (§2's `w`); spliced code of type `⇑τ` in a matching position of type
`σ` when `τ` and `σ` meet (today E0901 unless they unify); implicit object type arguments determined by
meets (was E0909).

Moved: object type errors found today after staging are reported at the generator, the quote or the
functor body; the boundary check reports only what depends on the staged item, with provenance. W0003
stays the only diagnostic for an unused generator that is well-typed.

Error codes: no new codes. A spliced `⇑τ` that does not fit its object position is E0402 (today
E0901, from unification). E0401, E0402, E0404 and E0405 are reported by the core (their explanations
gain a generator example); E0901 for `⇑` mismatches gets a note on object subtyping; E0206 replaces E0909
for unsolved object types. Hover shows the types of object variables inside formula functions and
quotes (#54).

## 7. Migration

Batch A, object typing in the core (goal (a), C1, C2): `core/objtype/{ObjTypes,ObjConstraints,
ObjProblems}`; the elaborator's feeding (`Coercions`, `ObjectCode`, `ObjectItems`, clause and definition
ends, module bodies); declaration checks (E0404) into `ObjectDecls`; the boundary walker in the handover
with `varTypes`; delete `ObjTyperPhase`, `RuleTyper`; `obj/typing/TypeOps` stays for the operations of
`Records`, `Lower` and the facts loader (not a checker). About +1100/−650 lines; goldens: the moved
diagnostics, new negatives for generators, C1 and C2.

Batch B, typed reflection (goal (b)): `quoted`, `qterm`, `raw` and the coercions; quote content
elaborated as object code and reified from the core term (rewrites most of `QuoteTerms`); typed holes in
`QuotedPatterns`; the reserved names for generated variables and their use in `%demand`. About
+800/−550 lines; goldens `c1_*`, `c2_*`, `c3_*`, round-trip and `SharedDataSuite` unchanged in output.

Batch C, documents: reference chapters "Staging", "Reflection" and the object typing chapter (where the
checks now happen), error explanations, `docs/NOTES.md`.

Batch A does not depend on B; B's quote checking needs A's engine.

## 8. Sources

- lean4 0bb12a8: `src/Lean/Expr.lean`, `src/Init/Prelude.lean` (`Syntax`, `TSyntax`, macro scopes),
  `src/Lean/Elab/Quotation.lean`, `src/Lean/Elab/Quotation/Precheck.lean`,
  `src/Lean/Elab/Term/TermElabM.lean`, `src/Lean/Meta/InferType.lean`, `src/Lean/Meta/Check.lean`,
  `src/Lean/AddDecl.lean`.
- quote4 e7c4cdd: `Qq/Typ.lean`, `Qq/Macro.lean`, `Qq/Match.lean`.
- scala3 1095192: `compiler/src/dotty/tools/dotc/typer/QuotesAndSplices.scala`,
  `staging/CrossStageSafety.scala`, `transform/Splicer.scala`, `inlines/Inliner.scala`,
  `compiler/src/scala/quoted/runtime/impl/{QuoteMatcher,QuotesImpl}.scala`, `library/src/scala/quoted/`.
- AndrasKovacs/staged 9c4e201: `demo/Elaboration.hs`, `demo/Staging.hs`, `demo/examples/STLC.2ltt`,
  `icfp22paper/paper.tex` (§2.3 "Inferring Staging Operations", §5 "Soundness of Staging",
  §6 "Intensional Analysis").
- GHC master: `libraries/ghc-internal/src/GHC/Internal/TH/{Monad,Lift}.hs`.
