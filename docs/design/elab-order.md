# Elaboration in dependency order

Design note for [issue #91](https://github.com/k0uks1/hugin/issues/91): definitions are elaborated
before the clauses of functions, so a type that computes with a function defined by clauses is
rejected. Status: approved by the designer; batch 1 implemented (`docs/NOTES.md`, "Elaboration in dependency order"). The designer's
decisions: follow established practice; inside a cycle the written order must not matter (5.3); the
first rejected class of 5.6, the split of typed definitions and the #100 constraint are accepted.

Contents: 1 recommendations, 2 conformance, 3 Hugin today, 4 prior art, 5 assessments, 6 alternatives
rejected, 7 effects, 8 batches, 9 sources.

## 1. Recommendations

Hugin's files and module bodies are unordered scopes with forward references and mutual recursion
without a `mutual` keyword (reference `meta/index.md`, "Order of elaboration"). For such scopes the
established practice is Haskell's dependency analysis into strongly connected components (SCCs); inside
one component it is the rule of Lean 4's mutual blocks, Rocq's `Fix` and GHC's recursive type groups: the
component's own bodies do not unfold in it. The design takes both.

1. **SCCs in dependency order** (Haskell 2010 §4.5.1, GHC `depAnalBinds`). A file's declaration items
   are elaborated by the SCCs of their dependency graph, in topological order, independent components in
   source order.
2. **Signatures and bodies are separate nodes** (GHC `tc_rec_group`; Agda and Idris mutual blocks). A
   function by clauses is its signature and its clause group; a definition with a declared type
   `x : A = e.` is its signature and its value; a formula function its declaration and its rules. A
   definition without a declared type is one node.
3. **A mention depends on the body** (GHC: a mention of a closed type family depends on its
   declaration, equations included). Hugin's types compute with functions and definitions, so GHC's
   dropping of edges to names with signatures does not apply.
4. **Inside a component, the Lean/Rocq/GHC rule:** all signatures first, then the bodies; no type or
   body of the component unfolds a body of the same component, whatever the written order; bodies of
   earlier components unfold normally. A type or body that needs such a body sees it stuck and fails
   with the ordinary error; the error gets a note naming the cycle.
5. **Termination and the formula-cycle check (E0105) at the end of each component** (Agda
   `mutualChecks`, Lean's SCCs in `addPreDefinitions`), before its bodies become unfoldable, so a
   function still reduces only once its call cycles are known to terminate.
6. **Module bodies** use the same order (batch 2, after #100 batch 1), with the body's object members
   first and member functions after them (Agda's record modules). `where` blocks keep their sequential
   scope and textual order (declaration before use, as in Agda, Idris 2, Lean 4).
7. **No change of granularity** for #66 blocks or `Signatures` (GHC and Agda also recompile per module),
   **no new error codes**, definitions stay non-recursive (E0105, E0101: a Hugin rule). Two classes of
   accepted programs become rejected (5.6); Lean and Rocq reject their analogues.

## 2. Conformance

| decision | precedent | citation | |
|---|---|---|---|
| unordered scope elaborated by SCCs in topological order | Haskell declaration groups; GHC renamer | Report §4.5.1 (`decls.verb` 1687–1712); `Rename/Bind.hs` 647 `depAnalBinds`; `Tc/Gen/Bind.hs` 293 `tcBindGroups` | match |
| independent components in source order | Haskell: "order … is irrelevant"; Agda, Idris, Lean: source order | Report §4.5.1; `Rules/Decl.hs` 144; `ProcessDecls.idr` 149 | match (no observable difference, 5.2) |
| signature and body as separate nodes | GHC drops edges to signed variables; Agda and Idris put signatures before definitions | `Tc/Gen/Bind.hs` 374–378; Agda `Definitions.hs` 1138 `mkOldMutual`, manual `mutual-recursion` 199–201; `Desugar/Mutual.idr` 57 | match |
| a mention depends on the body, not only the signature | GHC type families: one node per declaration with its equations; finished groups are visible, the current group is not | `Rename/Module.hs` 1440 (TCDEP3); `Tc/TyCl.hs` 2456–2472 | match (term-level GHC drops the edge; types do not compute there) |
| no edges for unnamed dependencies | GHC cannot see instance dependencies and retries groups | `Rename/Module.hs` 1545; `Tc/TyCl.hs` 154–256 | not needed: every Hugin clause names its function; derived functions get explicit edges |
| in a component: signatures first, no body of the component unfolds in it, order irrelevant | Lean: block functions are auxiliary locals, compiled after the block; Rocq `Fix`: bodies typed with the functions as assumptions; GHC: a recursive group's tycons are knot-tied, only finished groups are in the global env | `MutualDef.lean` 209, 359, 1347, 1445; Rocq `inductive.rst` 1504; `Tc/TyCl.hs` 2456–2472 | match |
| a type needing a body of its own cycle: stuck, ordinary error | as above; Idris for types: "none of the function types can depend on the reduction behaviour" of the block | as above; `typesfuns.rst` 552–555 | match; the note is an addition |
| Agda/Idris: bodies in written order, a checked body unfolds in later ones | Agda forward declaration; Idris `mutual` definitions pass | `Rules/Def.hs` 435; `Reduce.hs` 735–743; `ProcessDef.idr` 936 | not adopted: written order would decide acceptance in an unordered scope (designer) |
| termination at the end of a component, before its bodies unfold | Agda end of block; Lean per SCC after the block | `Rules/Decl.hs` 277–290; `PreDefinition/Main.lean` 43, 288 | match |
| formula-function cycle check per component | as termination | as above | match |
| object members before member functions in a body | Agda record modules: pattern-matching definitions after the fields; module parameters abstracted over all definitions | manual `record-types` 487–490; `module-system` 172 | match |
| `where` blocks textual | Agda, Idris, Lean: declaration before use in ordered scopes | `Rules/Decl.hs` 144; `typesfuns.rst` 534; Hugin `meta/where.md` 31 | match for an ordered scope; Haskell orders `where` by §4.5.1 because its `where` is unordered |
| definitions not recursive (E0105, E0101) | Agda and Idris allow recursive definitions and check termination | n/a | deviation, kept: a Hugin rule of the reference (`E0105.md`), unchanged by #91 |
| `Signatures` one query per file | GHC and Agda check a module as a whole | n/a (not a semantic question) | match |

## 3. Hugin today

`Items.elabDeclarations` (`core/elab/Items.scala`, line 50) runs fixed phases: `%use`, declarations
and definitions with a retry for forward references (`elabInDependencyOrder`, line 127); derived
`T.lift`/`T.reify` (`defineSharedFunctions`); all clause groups in order of first appearance
(`elabClauseGroups`, line 236), one `Core.inBlock` each; formula functions, then `checkFormulaCycles`;
`%export`. Function signatures exist from the first phase on with `GlobalKind.Function(arity, None)`:
applications stay stuck until the case tree is installed; a value computed while stuck reduces when
forced later (row 9). `Clauses.elabFunction` installs a case tree and calls
`SizeChange.checkTermination` (line 66), which checks the new components of the call graph: "cycles
through functions elaborated later are stuck until those are checked" (`SizeChange.scala`, line 368).

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
| 7 | `h : nat -> vec int (plus one one).` `h _ = vcons 1 (vcons 2 vnil).` with `plus` written after `h` | E0901 at `h`'s clause |
| 8 | the same with `plus` written before `h` | accepted |
| 9 | `two : nat = plus one one.` `g : eqn two (suc one) -> int.` `g refl = 0.` | accepted |
| 10 | `d : vec int (k zero) = vcons 1 vnil.` `k zero = one.` `k (suc N) = vlen d.` | E0901 at `d` |
| 11 | `c zero = zero. c (suc N) = zero.` `q : (x y : nat) -> eqn (c x) (c y) -> nat.` `r : nat = q one _ refl.` | accepted: `c one` is stuck, so `c one = c α` solves α := one by arguments |
| 12 | the same as a clause, `s N = q one _ refl.` | E0901: `c one` reduces to `zero`, `zero = c α` is unsolvable |
| 13 | `pick zero = int.` … `t : type = pick zero.` `r : t -> rel.` `r 1.` | accepted: object typing forces `t` later |
| 14 | in a `where` block: `q zero = one.` … then `p : vec int (q zero) = vcons 1 vnil.` | accepted: `where` items in order |

Rows 1–7 are the issue, row 10 a real cycle, rows 11–12 the programs that rely on today's order.

## 4. Prior art

Clones (`--depth 1`, scratchpad): agda/agda 192e0d4, idris-lang/Idris2 1c630e6, leanprover/lean4
b8182f6, ghc/ghc e7cacf5 (gitlab.haskell.org), haskell/haskell-report 29f5238, rocq-prover/rocq f6a7d73
(`doc/sphinx`), AndrasKovacs/smalltt ea99b0f.

**Agda.** Declarations are checked in order (`checkDecls`, `Rules/Decl.hs` 144); a name is used after
its signature. A lone signature opens an inferred mutual block that ends when every such signature is
defined (`inferMutualBlocks`, `Syntax/Concrete/Definitions.hs` 261; manual `mutual-recursion.lagda.rst`
95–100). An old-style `mutual` block is sorted, "placing the declarations before the definitions"
(manual 199–201; `mkOldMutual`, `Definitions.hs` 1138); `interleaved mutual` groups each function's
clauses with the first of them (manual 88–92). `checkMutual` checks the block's items in order (line
882). A function's clauses are added to the signature as soon as they are checked (`checkFunDef'`,
`Rules/Def.hs` 435, `funTerminates` unknown), and later items of the block unfold them: only functions
that failed termination are not unfolded, the test on unconfirmed termination is commented out
(`unfoldDefinitionStep`, `TypeChecking/Reduce.hs` 735–743). Positivity and termination run at the end
of the block (`mutualChecks`, `Rules/Decl.hs` 277–290). So a type in a block can compute with a
function whose clauses are written before it, not with one written after.

**Idris 2.** "Functions and data types must be defined before use" (tutorial `typesfuns.rst` 534). A
`mutual` block becomes all type declarations, then all definitions (`splitMutual`,
`Idris/Desugar/Mutual.idr` 57); "none of the function types can depend on the reduction behaviour of
any of the functions in the block" (552–555), and forward declarations give control when a definition
must "rely on the behaviour of a mutually defined function" (557–560). Definitions are processed in
order (`processDecls`, `TTImp/ProcessDecls.idr` 149), each compile-time case tree added as soon as its
clauses are checked (`TTImp/ProcessDef.idr` 936), before size-change and coverage (951–960).

**Lean 4.** Commands are elaborated in order; recursion between declarations needs `mutual … end`
(`Elab/Declaration.lean` 288). The block's headers are elaborated first (`elabHeaders`,
`Elab/MutualDef.lean` 209), the bodies with the block's functions as auxiliary local declarations
(`withFunLocalDecls`, 359, in `finishElab`, 1347): no function of the block unfolds inside it. At the
end (`addPreDefinitions`, 1445) the block is split into SCCs (`partitionPreDefs`,
`Elab/PreDefinition/Main.lean` 43) and compiled per SCC; later commands unfold the result, except
well-founded definitions, which become irreducible (`PreDefinition/Mutual.lean` 33).

**Rocq.** `Fixpoint … with …` (`doc/sphinx/language/core/inductive.rst` 449): the `Fix` rule (1504)
types each body with the block's functions as assumptions; types are checked without them.

**Haskell and GHC.** Report §4.5.1 (`report/decls.verb` 1687–1712): "b1 depends on b2 if b1 contains a
free identifier that has no type signature and is bound by b2"; "a declaration group is a minimal set
of mutually dependent bindings … in dependency order. The order of declarations in where/let constructs
is irrelevant." GHC: `depAnalBinds` (`Rename/Bind.hs` 647) builds the SCCs; `tcBindGroups`
(`Tc/Gen/Bind.hs` 293) checks them in order; inside a recursive group a second SCC analysis "omitting
any references to variables with type signatures" (374–378). Types are another matter: type and class
declarations are one node each, a closed type family together with its equations (`Rename/Module.hs`
1440, TCDEP3), checked group by group; inside a group the declarations are knot-tied `TcTyCon`s and
"earlier, finished groups live in the global env only" (`Tc/TyCl.hs` 2456–2472). Open type family
instances are unnamed, so GHC cannot see which declarations need them; it puts them at the end and
retries groups that fail (`Rename/Module.hs` 1545, `Tc/TyCl.hs` 154–256, example #11348 at 191).

**smalltt** elaborates top-level definitions in order (`elabTopLevel`, `src/Elaboration.hs` 276),
without recursion.

## 5. Assessments

### 5.1 The graph

**Assessment: nodes and edges as GHC's type-level analysis.** Nodes: each declaration (family,
constructor, postulate, object declaration, subtyping edge), each untyped definition, each `%use`,
`%export`; `sig`/`body` pairs for functions by clauses, typed definitions and formula functions; the
derived functions. Edges: a mention of a name declared in the file goes to its body (or its only node);
`body x → sig x`; a mention of a name opened by a `%use` of a file-local module goes to that `%use`;
`%export` depends on every node; the derived functions on the shared families, constructors and `term`.
Mentions are collected from the syntax, ignoring shadowing; an extra edge only orders an item later or
merges components. As in GHC every dependency is lexical, because every clause names its function;
GHC's retry for unnamed instances has no counterpart. `predeclare` stays first (object constants are
usable as types before their declaration).

### 5.2 Order between components

**Assessment: topological, independent components in source order.** Tarjan for the SCCs, then Kahn
picking the ready component with the earliest item. Components without a path between them cannot
observe each other's order: neither unfolds the other, each solves its own unknowns (#66), diagnostics
are sorted by position (`MetaLevel`) and `--print-after elaborate` prints in source order
(`Staging.render`). The first draft broke ties by today's phases; that has no precedent and no effect,
so source order (Agda, Idris, Lean) replaces it.

### 5.3 Inside a component

**Assessment: signatures first; the component's bodies are opaque to each other.** This is Lean's rule
(the block's functions are auxiliary local declarations, `MutualDef.lean` 359, compiled only after the
block, 1445), Rocq's `Fix` rule (bodies typed with the functions as assumptions, `inductive.rst` 1504)
and GHC's for a recursive type group (knot-tied tycons, only finished groups in the global env,
`Tc/TyCl.hs` 2456–2472). Signatures are elaborated with today's retry loop (E0104 for type definitions
in a cycle). An untyped definition has no signature: its body is elaborated with the signatures, since
its type comes from it, and its value is opaque to the component like any other body. Then the bodies
(clause groups, typed definition values, rules of formula functions) are elaborated, in source order
for determinism only: while the component is checked, every function, definition and formula function
of it is stuck (applications do not reduce, values do not unfold), so no body can observe another and
the written order never decides acceptance. When the component is done (5.4), its bodies unfold for all
later components; a stuck value computed inside it reduces when forced later (row 9). E0105 and E0101
keep their meaning: a definition value may not reach itself through definition values alone; a cycle
through a clause group is mutual recursion, checked for termination (row 4).

Row 10 is the cycle `sig d → body k → body d`: `d`'s value is checked with `k zero` stuck, in either
written order, and fails with E0901 and the note "`k zero` does not reduce here: `k` and `d` refer to
each other, and inside such a cycle no body unfolds another". Lean and Rocq reject the analogue in
either order. Agda and Idris would accept it with `k`'s clauses written first; that rule is not adopted
(section 6). A new error code is not needed: which item needs a body is known only by checking it, and
all the references give the ordinary error.

### 5.4 Termination, coverage, formula functions

**Assessment: at the end of each component, before its bodies unfold.** Since no body of a component
unfolds inside it, the size-change check of a component runs once all its case trees and definition
values exist, with calls through definitions followed as #92 does; then the component becomes
unfoldable. This is Agda's end-of-block check and Lean's per-SCC compilation, and it keeps Hugin's
invariant that a function reduces only once its call cycles are known to terminate
(`SizeChange.scala` 368; #66 note 2.4). Edges `body f → body g` for every call put a cycle of calls in
one component, so later components see only decided functions. A formula function expands its rules
when unfolded and a recursive one does not end: `checkFormulaCycles` runs on the component at the same
point. Coverage of a clause group sees the indices that earlier components reduce (a clause may newly
get W0006) and those of its own component stuck.

### 5.5 Module bodies and #100

**Assessment: the same order for members; object members first.** A body inside a top-level definition
is part of one node, so row 5 is fixed by batch 1. Member functions (#100) are lifted over the
enclosing context and the body's object members, which must be fixed at the signature. Agda's record
modules have the same constraint: "new definitions need to appear after the field declarations, but
simple non-recursive function definitions without pattern matching can be interleaved with the fields"
(`record-types.lagda.rst` 487–490), and module parameters are "abstracted from all the definitions"
(`module-system.lagda.rst` 172). So: object members first (with the definitions their types mention,
which see member functions stuck, harmless as row 13 shows), then the members by 5.1–5.3, then object
items. The closed type of a member function let-binds the definitions before its signature; its
`prelude` re-defines those before its clause group. #100 batch 1 can land as designed.

### 5.6 Compatibility

**Assessment: two classes become rejected; the first is accepted by the designer, the second follows
from 5.3.** Batch 1 measures goldens and library for both and lists each change in NOTES.

1. Row 11 relies on `c one` being stuck only because `c`'s clauses come later. Agda, Idris 2 and Lean
   require `c` before `r`, so `c one` reduces and `zero = c α` leaves α unsolved there too. The reference
   (`meta/functions.md`) compares stuck applications by arguments when "a split meets a variable or an
   unknown", which row 11 is not.
2. Today a clause group unfolds every clause group elaborated before it, also one of its own cycle
   (`f` written before `g`, `g`'s clauses typed with `f n` reducing, `f`'s clauses calling `g`). Inside
   one component this no longer reduces. Lean and Rocq reject the analogue.

### 5.7 `%use`, `%export`, signatures-only files, #66, incrementality

- `%use` and `%export` keep their meaning (5.1); `%export` sees every case tree (row 6).
- `ProgramElab.signatures` skips clause groups (`FileEnv.signaturesOnly`) and `StdlibCache.declaresObjects`
  reads any diagnostic as "may declare objects": the clause groups that a non-clause node depends on are
  elaborated in that mode.
- #66: each item, clause group and definition value stays one block; earlier blocks' unknowns are frozen
  and solved; numbering per block unchanged; object items and forks still come after all declarations.
- `Signatures` (docs/INCREMENTALITY.md, "Still coarse") stays one query; components are the unit for
  splitting it later.

### 5.8 Diagnostics and the reference

No new codes. The note of 5.3 on errors whose message holds an application stuck at a function or
definition of the file: one of the same cycle, one whose clauses were rejected, or one rejected by E0912. Reference:
`meta/index.md` "Order of elaboration" (dependency order, components, the rule inside a cycle, the
issue's example), `meta/functions.md` "Definitions" (a definition may compute with functions; inside a cycle the type of a
typed definition is known, its value is not), `docs/errors/E0901.md` (the note), and
in batch 2 `modules.md` "Module bodies".

## 6. Alternatives rejected

- **Today's phases with ties or clause groups sorted:** fixes row 7, not the issue.
- **User-written `mutual` blocks** (Lean, Idris, Agda): those languages have ordered scopes; Hugin's
  scopes are unordered, where the precedent is Haskell's analysis.
- **The Agda/Idris rule inside a component** (bodies in written order, a checked body unfolds in the
  later ones; Agda `Rules/Def.hs` 435, `Reduce.hs` 735–743; Idris `ProcessDef.idr` 936): the written
  order would decide acceptance, and Hugin's scopes are deliberately unordered (designer's decision).
- **GHC's retry of failed groups:** needed only for unnamed dependencies.
- **Unfolding before termination is decided** (Agda): the elaborator could loop (5.4); excluded anyway
  by 5.3.
- **Recursive definitions with termination checking** (Agda, Idris): a language change outside #91.
- **Splitting `Signatures` per component now:** an incrementality change of its own.

## 7. Effects

Newly accepted (rows 1–7):

```hugin,ignore
nat : Type. zero : nat. suc : nat -> nat.
one : nat = suc zero.
vec3 : Type = vec int (plus one (suc one)).
v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).
plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
```

Order: `nat`, `zero`, `suc`, `one`, `vec`, `vnil`, `vcons`, `sig plus`, `body plus`, `vec3`, `sig v`,
`body v`. Still rejected, with the note: row 10, in any written order. Newly rejected: row 11, and
clause groups that unfold a group of their own cycle (5.6).

## 8. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md).

1. **Dependency order for files.** `elab/ElabOrder.scala` (nodes, mentions, Tarjan, Kahn);
   `Items.elabDeclarations` per component; typed definitions as signature and value; the component's
   functions, definitions and formula functions stuck until its end; termination and
   `checkFormulaCycles` at the end of each component;
   signatures-only mode; the note in `ElabErrors`. Reference as in 5.8. Goldens:
   `run/order_definitions` (rows 1–7), `neg/order_cycle` (row 10 in both orders, with the note),
   `neg/order_stuck_notes`, row 11; NOTES entry. About +280/−50 lines.
2. **Module bodies,** after #100 batch 1: `ModuleBodies.elabMembers` on `ElabOrder`, object members
   first. Reference `modules.md`. Golden `run/order_members`. About +80/−20 lines.

## 9. Sources

- Haskell 2010 Report §4.5.1 (haskell/haskell-report 29f5238, `report/decls.verb`).
- ghc/ghc e7cacf5: `compiler/GHC/Rename/Bind.hs` (`depAnalBinds`), `compiler/GHC/Tc/Gen/Bind.hs`
  (`tcBindGroups`, `tc_rec_group`), `compiler/GHC/Rename/Module.hs` (Notes [Dependency analysis of type
  and class decls], [Put instances at the end]), `compiler/GHC/Tc/TyCl.hs` (Notes [Retrying
  TyClGroups], [Type checking recursive type and class declarations]).
- agda/agda 192e0d4: `src/full/Agda/TypeChecking/Rules/{Decl,Def}.hs`, `TypeChecking/Reduce.hs`,
  `Syntax/Concrete/Definitions.hs`; `doc/user-manual/language/{mutual-recursion,record-types,module-system}.lagda.rst`.
- idris-lang/Idris2 1c630e6: `src/TTImp/{ProcessDecls,ProcessDef}.idr`, `src/Idris/Desugar/Mutual.idr`,
  `docs/source/tutorial/typesfuns.rst`.
- leanprover/lean4 b8182f6: `src/Lean/Elab/{MutualDef,Declaration}.lean`,
  `src/Lean/Elab/PreDefinition/{Main,Mutual}.lean`.
- rocq-prover/rocq f6a7d73: `doc/sphinx/language/core/inductive.rst`. smalltt ea99b0f:
  `src/Elaboration.hs`.
- Hugin bf14ffb: `core/elab/{Items,Clauses,SizeChange,FormulaFunctions,ModuleBodies,DerivedFunctions,ObjectDecls,Where}.scala`,
  `core/{ProgramElab,Core,Staging,MetaLevel}.scala`, `compiler/StdlibCache.scala`, docs/INCREMENTALITY.md,
  `reference/src/meta/{index,functions,where}.md`, `docs/errors/E0105.md`; `docs/design/elaborator-glued.md`
  (2.1, 2.4); `docs/design/module-clauses.md` on `design/module-clauses-100`.
