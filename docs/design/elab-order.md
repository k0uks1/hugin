# Elaboration in dependency order

Design note for [issue #91](https://github.com/k0uks1/hugin/issues/91): definitions are elaborated
before the clauses of functions, so a type that computes with a function defined by clauses is
rejected. Status: proposed, for review by the designer. Nothing is implemented.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 assessments, 5 alternatives rejected,
6 effects, 7 batches, 8 sources.

## 1. Recommendations

1. **Elaborate the declaration items of a file by the strongly connected components of their dependency
   graph, in topological order.** A function defined by clauses is two nodes, its signature and its
   clause group; so is a formula function (declaration, rules). A mention of a function is an edge to
   its clause group. A definition that uses a function is therefore checked after that function's
   clauses, and after the clauses of every function those clauses call.
2. **Ties are broken by today's order** (declarations and definitions before clause groups, then source
   position). A file in which no declaration or definition mentions a function by clauses is elaborated
   in exactly today's order.
3. **Inside a component, today's order:** its declarations and definitions (with the retry loop and the
   E0101/E0104/E0105 reports of today), then its clause groups in source order, then its formula
   functions. An application of a function of the same component whose clauses come later is stuck, as
   today and as in an Idris 2 `mutual` block. This is not a new error; the error it causes gets a note
   that names the function and the cycle.
4. **Module bodies follow the same order** once #100 batch 1 has landed, with one constraint on #100:
   a body's object members come first, so the context over which member functions are lifted is fixed
   before any member function. `where` blocks keep their textual order.
5. **The per-function checks keep their place; the formula-function cycle check (E0105) runs per
   component.** Size-change termination already runs after each case tree is installed; with
   rule 1 a later component never sees a function whose termination is still undecided.
6. **No change of granularity** for #66 blocks (one item or clause group each) or for incrementality
   (`Signatures` stays one query). The signatures-only elaboration of library files also elaborates the
   clause groups that a declaration or definition depends on.
7. **No new error codes.** One class of accepted programs becomes rejected (4.9). The reference changes
   in `meta/index.md` "Order of elaboration" (batch 1) and `modules.md` "Module bodies" (batch 2).

## 2. Hugin today

`Items.elabDeclarations` (`core/elab/Items.scala`, line 50) runs fixed phases over a file's declaration
items: `%use` and the declarations and definitions in source order, an item that refers to a later one
retried after it (`elabInDependencyOrder`, line 127); `checkObjectDeclarations` and the derived
`T.lift`/`T.reify` functions (`defineSharedFunctions`); every clause group in order of first appearance
(`elabClauseGroups`, line 236), one `Core.inBlock` each; formula functions by rules, then
`checkFormulaCycles`; `%export` last. Function signatures exist from the first phase on, with
`GlobalKind.Function(arity, None)`: applications are stuck until the case tree is installed. A stuck
application in an already evaluated value reduces later, when it is forced after the case tree exists
(row 9 below). `ProgramElab.declarations` (line 121) runs all of this as one part, `Signatures` in the
query database; object items are then elaborated one by one in forks.

`Clauses.elabFunction` installs a case tree and calls `SizeChange.checkTermination` (`Clauses.scala`,
line 66). The call graph is per file, but checked per installation, by components (`SizeChange.scala`,
line 377): "cycles through functions elaborated later are stuck until those are checked" (line 368).

Measured on bf14ffb (scratch programs, not committed; all start with `nat`, `zero`, `suc`,
`one : nat = suc zero`, `plus` by clauses, `vec`, `vnil`, `vcons`, `eqn`, `refl`):

| # | program | result |
|---|---|---|
| 1 | `vec3 : Type = vec int (plus one (suc one)).` `v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).` (the issue) | E0901 ``expected `vec3`, found `vec int (suc (suc (suc zero)))` `` |
| 2 | `v : vec int (plus one one) = vcons 1 (vcons 2 vnil).` | E0901 |
| 3 | `two : nat = plus one one.` `w : eqn two (suc one) = refl.` | E0901 |
| 4 | `g : nat -> nat = [x] f x.` `f zero = zero.` `f (suc N) = g N.` `t : eqn (g one) zero = refl.` | E0901 at `t` |
| 5 | `m = { v : vec int (plus one one) = vcons 1 (vcons 2 vnil). }.` | E0901: a body is part of its top-level definition |
| 6 | `%export { v2 : nat2 }.` with `nat2 : Type = vec int (plus one one)` and `v2 : nat2 = …` | E0901 at `v2`, then E0204 |
| 7 | `h : nat -> vec int (plus one one).` `h _ = vcons 1 (vcons 2 vnil).` with `plus` written after `h` | E0901 at `h`'s clause: clause groups go in source order |
| 8 | the same with `plus` written before `h`; also `g : vec int (plus one one) -> int.` `g (vcons X _) = X.` | accepted |
| 9 | `two : nat = plus one one.` `g : eqn two (suc one) -> int.` `g refl = 0.` | accepted: `two`'s stuck value reduces in the clause phase |
| 10 | `d : vec int (k zero) = vcons 1 vnil.` `k zero = one.` `k (suc N) = vlen d.` | E0901 at `d`, no hint that `k` comes later |
| 11 | `c zero = zero. c (suc N) = zero.` `q : (x y : nat) -> eqn (c x) (c y) -> nat.` `r : nat = q one _ refl.` | accepted: `c one` is stuck, so `c one = c α` solves α := one by arguments |
| 12 | the same as a clause, `s N = q one _ refl.` | E0901: `c one` reduces to `zero`, `zero = c α` is unsolvable |
| 13 | `pick zero = int.` … `t : type = pick zero.` `r : t -> rel.` `r 1.` | accepted: object typing forces `t` after the clauses |
| 14 | in a `where` block: `q zero = one.` … then `p : vec int (q zero) = vcons 1 vnil.` | accepted: `where` items are elaborated in order |

Rows 1–7 are the issue. Row 10 is a real cycle. Rows 11 and 12 show that some accepted programs rely on
the current order (4.9). Row 9 shows that a value computed with a stuck function is not stale: only the
check of an item needs the case tree, never a later reuse of its value.

## 3. Prior art

Clones (`--depth 1`, in the scratchpad): leanprover/lean4 b8182f6, agda/agda 192e0d4 (sparse:
`src/full/Agda/TypeChecking`, `src/full/Agda/Syntax/Concrete`, `doc/user-manual/language`),
idris-lang/Idris2 1c630e6, AndrasKovacs/smalltt ea99b0f.

### 3.1 Lean 4

- Commands are elaborated in source order; a forward reference is an unknown identifier. Recursion
  between declarations needs `mutual … end` (`Elab/Declaration.lean`, line 288).
- In a mutual block the headers are elaborated first (`elabHeaders`, `Elab/MutualDef.lean`, line 209),
  then the bodies with the block's functions as auxiliary *local* declarations (`withFunLocalDecls`,
  line 359, used in `finishElab`, line 1347). A body cannot unfold a function of its own block.
- After the block, `addPreDefinitions` (`Elab/PreDefinition/Main.lean`, line 288) splits it into SCCs of
  the reference graph (`partitionPreDefs`, line 43) and compiles each by structural or well-founded
  recursion. Only then do later commands unfold them; well-founded definitions become irreducible
  (`Elab/PreDefinition/Mutual.lean`, line 33).

### 3.2 Agda

- `checkDecls` checks declarations in order (`Rules/Decl.hs`, line 144). A signature without a
  definition opens an inferred mutual block that runs until every such signature is defined
  (`inferMutualBlocks`, `Syntax/Concrete/Definitions.hs`, line 261; user manual
  `mutual-recursion.lagda.rst`, "Forward declaration", line 95). `interleaved mutual` lets the user
  interleave clauses; it is desugared by "grouping the clauses for a function together with the first of
  them" (line 90).
- Inside a block, `checkMutual` checks the items in order (line 882), and a function reduces in the
  items after its clauses, before the block's termination check. Termination and positivity run at the end of the block (`mutualChecks`, line 277;
  `checkTermination_`, line 290). Only functions that *failed* termination are not unfolded; the check for
  unconfirmed termination is commented out (`TypeChecking/Reduce.hs`, line 740).
- The user chooses the order inside a block by writing it.

### 3.3 Idris 2

- Declarations are processed in order (`processDecls`, `TTImp/ProcessDecls.idr`, line 149). A
  function's compile-time case tree is added as soon as its clauses are checked (`addDef … PMDef`,
  `TTImp/ProcessDef.idr`, line 936), before coverage and totality (lines 951–960).
- A `mutual` block is desugared into all type declarations, then all definitions (`splitMutual`,
  `Idris/Desugar/Mutual.idr`, line 57). The tutorial (`docs/source/tutorial/typesfuns.rst`, line 552):
  "none of the function types can depend on the reduction behaviour of any of the functions in the
  block". Forward declarations give finer control "if you need to rely on the behaviour of a mutually
  defined function for something to typecheck".

### 3.4 smalltt

Top-level definitions are elaborated in order (`elabTopLevel`, `src/Elaboration.hs`, line 276), each
unfoldable by the later ones (glued, as in #66). There is no recursion, so no ordering question.

### 3.5 What the references agree on

1. **A function unfolds in every item checked after its clauses.** None of them postpones unfolding to
   the end of a file.
2. **Within a recursive group, types do not see the group's reductions:** Lean's local functions,
   Idris 2's types-then-definitions split. Agda allows it only in the order the user writes.
3. **Recursive groups are explicit** (Lean, Idris 2) or inferred from signature/definition order (Agda).
   Lean computes SCCs only after elaboration, for compilation. No reference infers the order from a
   dependency graph; they all ask the user to write definitions before their uses, which Hugin does not
   (its items may be written in any order, reference `meta/index.md`).

## 4. Assessments

### 4.1 The graph

**Assessment: one node per declaration item, two per function, edges from syntactic mentions.**

- Nodes: each declaration (inductive family, constructor, postulate, object declaration, subtyping edge),
  each definition, each `%use`, `%export`; for a function by clauses its signature `sig f` and its clause
  group `body f`; for a formula function its declaration and its rules.
- Edges: an item mentions a name declared in the file: an edge to that name's node, and for a function
  or formula function to its body. `body f` depends on `sig f`. A mention of a name opened by a `%use`
  of a file-local module is an edge to that `%use`. `%export` depends on every node.
- Mentions are collected from the syntax (identifiers, path heads), ignoring binders that shadow a
  file name. An extra edge can only put more items after a clause group or merge components, and inside
  a component the order is today's (4.2), so over-approximation never orders worse than today.
- Signatures can depend on clause groups (`sig g → body plus` for row 7). A definition is one node,
  type and value: its value may be unfolded by any item that mentions it.

Edges to the clause groups of *called* functions (`body f → body g`) are what makes termination and
reduction safe across components: when an item is checked, every function it can reduce is complete
and its termination is decided (4.5).

### 4.2 Order between and within components

**Assessment: topological, ties by today's order; inside a component, today's phases.** Components are
computed by Tarjan's algorithm and emitted by Kahn's algorithm, picking among the ready components the
first by (phase, source position), phase being 0 for `%use`, 1 for declarations and definitions, 2 for
clause groups and the derived functions, 3 for formula functions. Inside a component the existing
functions run on its items: `elabInDependencyOrder`, `elabClauseGroups`, the formula functions. E0101
(definitions in a cycle), E0104 and E0105 keep their meaning: a cycle without a function by clauses is
still a cycle among definitions.

`predeclare` stays global and first (object constants are usable as types before their declaration);
`checkObjectDeclarations` runs after the last component, since it only reports; diagnostics are sorted
by position (`MetaLevel`, `reporter.sorted`) and `--print-after elaborate` prints in source order
(`Staging.render`), so neither shows the new order. The derived functions are a node depending on the
shared families, their constructors and `term`.

### 4.3 A cycle that needs a case tree

**Assessment: stuck, as now, with a note.** Row 10 is a cycle `d → body k → d`. Inside the component,
`d` is checked before `k`'s clauses, `k zero` is stuck and `d` fails. Alternatives:

- *An error for the cycle* (a new code): which items of a cycle need a case tree is not known before
  they are checked; most cycles (row 4: `g` and `f`) need none, and must stay accepted.
- *Retry a failed item of the component after its clause groups* (a fixpoint): `k`'s clauses already
  failed because `d` was dropped; making it work needs a definition split into a signature and a value
  checked separately, which Hugin does not have for definitions, and errors would depend on the retry.
- *User-written order inside a cycle* (Agda): contradicts "written in any order".

So the rule is Idris 2's: within a cycle, types do not compute with the cycle's functions. The error
gets a note when a value in it is stuck at a function of the file without a case tree: ``note: `k zero`
does not reduce here: the clauses of `k` refer to `d`, so they are checked after it``. The same note
covers a function whose clauses were rejected (``its clauses have errors``) or that may not terminate
(``E0912``), which today gives a bare mismatch as well.

### 4.4 Module bodies and #100

**Assessment: the same graph and the same order for a body's members; batch 2, after #100 batch 1.**
A body is part of its top-level definition, which is one node: row 5 is fixed by batch 1. Batch 2 is
about member functions, which exist only with #100. #100 rule 4 makes a body's order "a file's order": members (signatures and definitions) in dependency
order, then member clause groups, then object items. This note changes what a file's order is, and
bodies follow it: member signatures, definitions and member clause groups ordered by components, the
body's object items after all members.

The constraint is #100's lifting: a member function is a hidden global over the enclosing context and
the body's object members (#100, 4.2), and that context must be fixed when its signature is elaborated.
So in a body the object members come first, in dependency order among themselves and the definitions
their types mention (those see member functions stuck, harmless as row 13 shows), and the closed type
let-binds only the definitions elaborated before the signature; the clauses' `prelude` re-defines the
definitions elaborated before the clause group. #100 batch 1 can land as designed; batch 2 here reuses
the graph code of batch 1 (one helper for files and bodies).

`where` blocks stay sequential (reference `meta/where.md`: "elaborated in order"): they are lexical
and already let a later binding use an earlier function's case tree (row 14).

### 4.5 Termination, coverage, formula functions

**Assessment: unchanged per function; the formula cycle check per component.**

- Size-change termination keeps running after each installed case tree. With `body f → body g` for
  every call, a cycle of calls lies in one component, so when a component is done, the termination of
  each of its functions is decided before anything later can reduce them. Today a clause group may
  reduce a function whose cycle partner comes later and then loses its case tree (E0912); with this order
  that remains possible only inside one component, as in Agda's mutual blocks.
- Calls through definitions (#92) are found because a definition that a clause mentions is in an
  earlier component or earlier in the same one.
- Coverage of a function whose signature computes (row 8) sees the reduced index; a clause that becomes
  impossible gets W0006, not an error.
- A formula function becomes a `GlobalKind.Definition` when its rules are elaborated, and expanding a
  recursive one does not end. Today nothing expands one before `checkFormulaCycles`; with interleaving a
  later definition might. Its cycles lie in one component, so `checkFormulaCycles` runs on each component
  with formula functions, before the next component.

### 4.6 `%use`, `%export`, imports

**Assessment: no change in meaning.** `%use` keeps phase 0 and its retry. `%export` depends on every node
and stays last, so its signature sees every case tree (row 6 works once `v2` does). Imported files are
elaborated before the importing file, so their names have no node.

### 4.7 #66: freezing and block-relative numbering

**Assessment: no change.** Each declaration item and each clause group stays one `inBlock`; the blocks
run in a different order, and each freezes the unknowns created before it, which are all solved or
`allowUnsolved` (`checkSolved` at the end of every block). The spike of #66 (2.3) found that no accepted
program solves an earlier block's unknown, and the order of blocks does not change that. Unknowns are
numbered from `?0` per block as today. Glued definitions (#66 batch 2) unfold lazily, so a definition
elaborated after a clause group needs nothing new. Object items still come after all declarations, so
forks and `Moved` are unaffected.

### 4.8 Incrementality and signatures-only files

**Assessment: no change of granularity.** `Signatures` (docs/INCREMENTALITY.md, step 9 and "Still
coarse") elaborates all declaration items together and stays one query; its cut-off fingerprints do not
change. The components are the natural unit for splitting it later (`DeclSig` per component instead of
per file), which this note does not do.

`ProgramElab.signatures` (line 98) elaborates a library file without clause groups
(`FileEnv.signaturesOnly`), and `StdlibCache.declaresObjects` treats any diagnostic as "may declare
object constants". A definition that needs a case tree would now report an error there and disable a
lazy re-export. So in that mode the clause groups that a non-clause node depends on are elaborated; the
others are still skipped.

### 4.9 Compatibility

**Assessment: one class of programs becomes rejected; accept it.** Row 11 is accepted because `c one` is
stuck only because `c`'s clauses come later; the reference (`meta/functions.md`) describes comparing
stuck applications by arguments for applications that do not reduce "because a split meets a variable or
an unknown", and row 11 is not one. With this order `r` behaves as `s` in row 12. Every other change
makes an application reduce that was stuck, which accepts more. The batch measures the goldens and the
standard library and lists every changed result in its NOTES entry; if the class is not empty in the
library, the designer decides before merge.

### 4.10 Diagnostics and the reference

**Assessment: no new codes; one note; three reference sections.**

- E0901 (and the other errors with a value in their message) gets the note of 4.3.
- E0101, E0104, E0105 unchanged.
- `reference/src/meta/index.md`, "Order of elaboration": the declaration items are elaborated in
  dependency order: an item after the items it refers to and after the clauses of the functions it
  refers to; items that refer to each other in a cycle are elaborated declarations and definitions
  first, then clauses, and a type in a cycle does not compute with a function of the same cycle; an
  example with the issue's program.
- `reference/src/meta/functions.md`, "Definitions": a definition may compute with functions defined by
  clauses in its type and value.
- `reference/src/modules.md`, "Module bodies" (batch 2, with #100's text): the members of a body are
  elaborated in the order of a file, its object members first.

## 5. Alternatives rejected

- **Today's phases with only the clause groups sorted** (callees first): fixes row 7, not the issue.
- **All clause groups before all definitions:** clauses mention definitions (`g` in row 4), so
  definitions would be stuck in clauses instead.
- **User-written mutual blocks** (Lean, Idris 2, Agda): a new syntax, against "any order".
- **Lazy elaboration on demand** (elaborate `plus`'s clauses when `v` first needs them): every
  `force` could start an elaboration, with nested blocks and error recovery inside conversion; the
  graph gives the same order for acyclic programs without that.
- **An error for cycles through a case tree, or a retry fixpoint** (4.3).
- **Splitting `Signatures` per component now** (4.8): an incrementality change of its own.

## 6. Effects

Newly accepted (rows 1–7):

```hugin,ignore
nat : Type. zero : nat. suc : nat -> nat.
one : nat = suc zero.
vec3 : Type = vec int (plus one (suc one)).
v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).
lib = { w : vec int (plus one one) = vcons 1 (vcons 2 vnil). }.
plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
```

Order: `nat`, …, `one`, `vec`, `vnil`, `vcons`, `sig plus`, `body plus`, `vec3`, `v`, `lib`.

Still rejected, with the note (row 10):

```text
error[E0901]: mismatched types
  --> d.hgn:16:24
16 | d : vec int (k zero) = vcons 1 vnil.
   |                        ^^^^^^^^^^^^ expected `vec int (k zero)`, found `vec int (suc zero)`
   = note: `k zero` does not reduce here: the clauses of `k` refer to `d`, so they are checked after it
```

Newly rejected: row 11 (E0901 or E0903 at `r`).

## 7. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md, "Changing the
language").

1. **Dependency order for files.**
   - Code: a helper `elab/ElabOrder.scala` (nodes, syntactic mentions, Tarjan, Kahn with today's
     priority); `Items.elabDeclarations` runs the existing phases per component;
     `checkFormulaCycles` per component; `defineSharedFunctions` as a node; signatures-only mode
     (4.8); the stuck-function note in `ElabErrors`.
   - Reference: `meta/index.md` "Order of elaboration", `meta/functions.md` "Definitions",
     `docs/errors/E0901.md` (the note).
   - Goldens: `run/order_definitions` (rows 1–7), `neg/order_cycle` (row 10 with the note),
     `neg/order_stuck_notes` (rejected clauses, E0912); row 11 as a golden of the new rejection;
     NOTES entry with the measured changes of 4.9.
   - About +220/−40 lines.
2. **Dependency order for module bodies**, after #100 batch 1.
   - Code: `ModuleBodies.elabMembers` uses `ElabOrder`; object members first (4.4).
   - Reference: `modules.md` "Module bodies".
   - Golden: `run/order_members` (a member definition whose type computes with a member function,
     in a file body and a functor body).
   - About +80/−20 lines.

Batch 1 is independent of #100 and of #61; batch 2 needs #100 batch 1.

## 8. Sources

- leanprover/lean4 b8182f6: `src/Lean/Elab/MutualDef.lean` (`elabHeaders`, `withFunLocalDecls`,
  `finishElab`), `src/Lean/Elab/Declaration.lean` (`mutual`), `src/Lean/Elab/PreDefinition/Main.lean`
  (`partitionPreDefs`, `addPreDefinitions`), `src/Lean/Elab/PreDefinition/Mutual.lean`.
- agda/agda 192e0d4: `src/full/Agda/TypeChecking/Rules/Decl.hs` (`checkDecls`, `checkMutual`,
  `mutualChecks`, `checkTermination_`), `src/full/Agda/TypeChecking/Reduce.hs` (`unfoldDefinitionStep`),
  `src/full/Agda/Syntax/Concrete/Definitions.hs` (`inferMutualBlocks`),
  `doc/user-manual/language/mutual-recursion.lagda.rst`.
- idris-lang/Idris2 1c630e6: `src/TTImp/ProcessDecls.idr`, `src/TTImp/ProcessDef.idr` (`processDef`),
  `src/Idris/Desugar/Mutual.idr` (`splitMutual`), `docs/source/tutorial/typesfuns.rst` ("Declaration
  Order and `mutual` blocks").
- AndrasKovacs/smalltt ea99b0f: `src/Elaboration.hs` (`elabTopLevel`).
- Hugin bf14ffb: `core/elab/{Items,Clauses,SizeChange,FormulaFunctions,ModuleBodies,DerivedFunctions,ObjectDecls,Where}.scala`,
  `core/{ProgramElab,Core,Staging,MetaLevel}.scala`, `compiler/StdlibCache.scala`,
  docs/INCREMENTALITY.md, `reference/src/meta/{index,functions,where}.md`, `reference/src/modules.md`;
  `docs/design/elaborator-glued.md` (2.1, which first recorded the issue); `docs/design/module-clauses.md`
  on `design/module-clauses-100` (rules 2 and 4, 4.2).
