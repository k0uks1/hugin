# Elaboration in dependency order

Design note for [issue #91](https://github.com/k0uks1/hugin/issues/91): definitions are elaborated
before the clauses of functions, so a type that computes with a function defined by clauses is
rejected. Status: proposed, revised after the designer's review ("match what Idris, Agda and Lean do;
follow established theory"). Nothing is implemented.

Contents: 1 recommendations, 2 conformance, 3 Hugin today, 4 prior art, 5 assessments, 6 alternatives
rejected, 7 effects, 8 batches, 9 sources.

## 1. Recommendations

Hugin's files and module bodies are unordered scopes with forward references and mutual recursion
without a `mutual` keyword (reference `meta/index.md`, "Order of elaboration"). For such scopes the
established practice is Haskell's dependency analysis into strongly connected components (SCCs); inside
one component it is the mutual-block rule of Agda, Idris 2, Lean 4 and Rocq. The design takes both.

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
4. **Inside a component, the Agda/Idris rule:** all signatures first, then the bodies in the order
   written; a body that is checked unfolds in the bodies after it. A type or body that needs a body
   written later in the same component sees it stuck and fails with the ordinary error, as in all
   five systems; the error gets a note naming the cycle and the order.
5. **Termination and the formula-cycle check (E0105) per component** (Agda `mutualChecks`, Lean's SCCs
   in `addPreDefinitions`). Hugin keeps its stricter invariant that a function reduces only once its
   call cycles are known to terminate.
6. **Module bodies** use the same order (batch 2, after #100 batch 1), with the body's object members
   first and member functions after them (Agda's record modules). `where` blocks keep their sequential
   scope and textual order (declaration before use, as in Agda, Idris 2, Lean 4).
7. **No change of granularity** for #66 blocks or `Signatures` (GHC and Agda also recompile per module),
   **no new error codes**, definitions stay non-recursive (E0105, E0101: a Hugin rule). One class of
   accepted programs becomes rejected (5.6); Agda, Idris 2 and Lean reject its analogue.

## 2. Conformance

| decision | precedent | citation | |
|---|---|---|---|
| unordered scope elaborated by SCCs in topological order | Haskell declaration groups; GHC renamer | Report §4.5.1 (`decls.verb` 1687–1712); `Rename/Bind.hs` 647 `depAnalBinds`; `Tc/Gen/Bind.hs` 293 `tcBindGroups` | match |
| independent components in source order | Haskell: "order … is irrelevant"; Agda, Idris, Lean: source order | Report §4.5.1; `Rules/Decl.hs` 144; `ProcessDecls.idr` 149 | match (no observable difference, 5.2) |
| signature and body as separate nodes | GHC drops edges to signed variables; Agda and Idris put signatures before definitions | `Tc/Gen/Bind.hs` 374–378; Agda `Definitions.hs` 1138 `mkOldMutual`, manual `mutual-recursion` 199–201; `Desugar/Mutual.idr` 57 | match |
| a mention depends on the body, not only the signature | GHC type families: one node per declaration with its equations; finished groups are visible, the current group is not | `Rename/Module.hs` 1440 (TCDEP3); `Tc/TyCl.hs` 2456–2472 | match (term-level GHC drops the edge; types do not compute there) |
| no edges for unnamed dependencies | GHC cannot see instance dependencies and retries groups | `Rename/Module.hs` 1545; `Tc/TyCl.hs` 154–256 | not needed: every Hugin clause names its function; derived functions get explicit edges |
| in a component: signatures first, then bodies in written order, checked bodies unfold | Agda forward declaration and old-style `mutual`; Idris `mutual` | manual `mutual-recursion` 95–100, 199–201; `Rules/Def.hs` 435 (clauses added when checked); `Reduce.hs` 735–743; `ProcessDef.idr` 936; tutorial `typesfuns.rst` 552–560 | match |
| a type needing a later body of its cycle: stuck, ordinary error | Idris "none of the function types can depend on the reduction behaviour" of the block; Lean auxiliary local functions; Rocq `Fix`; GHC knot-tied `TcTyCon` | `typesfuns.rst` 552; `MutualDef.lean` 359, 1347; Rocq `inductive.rst` 1504; `Tc/TyCl.hs` 2456 | match; the note is an addition |
| termination per component | Agda end of block; Lean per SCC | `Rules/Decl.hs` 277–290; `PreDefinition/Main.lean` 43, 288 | match; stricter on unfolding (5.4) |
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

**Assessment: signatures first, then bodies in the order written; checked bodies unfold.** This is
Agda's forward-declaration and old-style `mutual` rule and Idris's `mutual` rule. Signatures are
elaborated with today's retry loop (E0104 for type definitions in a cycle). Bodies follow in the order
of their items; an untyped definition has no signature, so it is elaborated before the bodies that
mention it (today's retry; Agda and Idris need a signature instead). A typed definition whose value is
not yet checked is opaque, like a postulate (as a formula function is today until its rules are
elaborated). E0105 and E0101 keep their meaning: a definition value may not reach itself through
definition values alone; a cycle through a clause group is mutual recursion and is checked for
termination (row 4), as today.

Row 10: `sig k`, `sig d` (its type mentions `k zero`, fine as a type), then `d`'s value (written first),
with `k zero` stuck: E0901, with the note ``the clauses of `k` refer to `d` and are written after it;
inside a cycle, bodies are checked in the order written``. Written with `k`'s clauses first, Agda and
Idris accept it, and so does Hugin. Lean and Rocq reject it in either order. A new error code for such
cycles is rejected: which item needs a body is known only by checking it, all five systems give the
ordinary error.

### 5.4 Termination, coverage, formula functions

**Assessment: per component, without unfolding unchecked cycles.** Agda unfolds a block's functions
before their termination is known. Hugin keeps its invariant (`SizeChange.scala` 368), because its
elaborator must not loop (#66 note 2.4: a non-terminating function overflowed the stack): a case tree
is checked when installed, and a typed definition value installed inside a component is a node of the
call graph whose installation checks the cycles through it (#92 follows calls through definitions;
today the value always exists first). Edges `body f → body g` for every call put a cycle of calls in one
component, so later components see only decided functions. Coverage sees reduced indices, so a clause
may newly get W0006. A formula function expands its rules when unfolded, and a recursive one does not
end: `checkFormulaCycles` runs per component, before the next.

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

**Assessment: accept the one rejected class.** Row 11 relies on `c one` being stuck only because `c`'s
clauses come later. Agda, Idris 2 and Lean require `c` before `r`, so `c one` reduces to `zero` and the
constraint `zero = c α` leaves α unsolved there too (an unsolved meta or "don't know how to synthesize").
The reference (`meta/functions.md`) compares stuck applications by arguments when "a split meets a
variable or an unknown", which row 11 is not. Batch 1 measures goldens and library and lists each
change in NOTES.

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
definition of the file without a body: later in the cycle, clauses rejected, or E0912. Reference:
`meta/index.md` "Order of elaboration" (dependency order, components, the rule inside a cycle, the
issue's example), `meta/functions.md` "Definitions" (a definition may compute with functions; a typed
definition can be used by clauses before its value is checked), `docs/errors/E0901.md` (the note), and
in batch 2 `modules.md` "Module bodies".

## 6. Alternatives rejected

- **Today's phases with ties or clause groups sorted:** fixes row 7, not the issue.
- **User-written `mutual` blocks** (Lean, Idris, Agda): those languages have ordered scopes; Hugin's
  scopes are unordered, where the precedent is Haskell's analysis.
- **Lean/Rocq's rule inside a component** (no unfolding at all in the block): rejects row 10 in either
  order; Agda and Idris accept the well-ordered version.
- **GHC's retry of failed groups:** needed only for unnamed dependencies.
- **Unfolding before termination is decided** (Agda): the elaborator could loop (5.4).
- **Recursive definitions with termination checking** (Agda, Idris): a language change outside #91.
- **Splitting `Signatures` per component now:** an incrementality change of its own.

## 7. Effects

Newly accepted (rows 1–7, and row 10 with `k`'s clauses written before `d`):

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
`body v`. Still rejected with the note: row 10 as written. Newly rejected: row 11.

## 8. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md).

1. **Dependency order for files.** `elab/ElabOrder.scala` (nodes, mentions, Tarjan, Kahn);
   `Items.elabDeclarations` per component; typed definitions as signature and value (opaque in between);
   definition values as call-graph nodes in `SizeChange`; `checkFormulaCycles` per component;
   signatures-only mode; the note in `ElabErrors`. Reference as in 5.8. Goldens:
   `run/order_definitions` (rows 1–7, row 10 reordered), `neg/order_cycle` (row 10 with the note),
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
