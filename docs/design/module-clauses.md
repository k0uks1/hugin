# Meta functions by clauses in module bodies

Design note for [issue #100](https://github.com/k0uks1/hugin/issues/100). Status: approved by the designer;
batch 1 implemented (see `docs/NOTES.md`, "Member functions in module bodies", for the choices the note
left open); batch 2 not started.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 assessments, 5 alternatives rejected,
6 effects, 7 batches, 8 sources.

## 1. Recommendations

1. **A module body accepts what a file accepts for meta functions.** A declaration `f : A.` with a meta
   type and the clauses `f p̄ = e.` of the same body define a *member function*. The members of a body
   are in scope in the whole body, so member functions may refer to later members and to each other.
2. **Member functions are lambda-lifted,** as local functions of `where` blocks already are
   (`core/elab/Where.scala`) and as Agda abstracts module parameters over a module's definitions: each
   one is a hidden global function over the bound variables of the body's context (the parameters of an
   enclosing functor and the body's object members). The member's value, a field of the module, is that
   global applied to the context. Coverage, size-change termination and the call collection of #92 then
   apply unchanged.
3. **A member function is elaborated once per body, not per instance.** Generativity concerns object
   constants only. Each instance's field is the shared function applied to that instance's arguments and
   object constants.
4. **The order is a file's order.** First the body's signatures and definitions, each after the members
   it refers to (as today), then the clause groups of its member functions, then its object items. Each
   member clause group is a block of its own for #66: it solves its own unknowns.
5. **E0907 keeps covering** what still has no meaning in a body: refinements, families of object
   constants, meta inductive families and postulates, `$e.` items, additive and module-wide directives,
   and `%use`. Formula functions defined by rules follow in a second batch, with the same lifting.
6. **No surface syntax changes.** Programs that compile today keep their meaning.

## 2. Hugin today

`core/elab/ModuleBodies.scala` partitions a body into *members* (`Decl`, `Def`) and object items. Members
are elaborated in dependency order (an item that refers to a later member is retried after it) and bound
in the body's context: an object constant as a bound variable of type `⇑τ`, a definition let-bound. The
body's type is the telescope of its members, and its value a `Tm.Module`. A meta declaration without a
definition is rejected in `objectMember`, and a `Clause` item falls into `objectItemOf`'s last case.
Both are E0907.

Measured on 0f23678 (scratch programs, not committed):

| program | result |
|---|---|
| `m = { double : nat -> nat. double zero = zero. double (suc N) = … }.` | E0907 at the declaration, E0907 at each clause ("this item in a module body are not supported", sic) |
| a functor body with `double : int -> int.` and `double N = N + N.` | E0907, then E0903 for `N`: the clause is read as a definition |
| `m = { double : nat -> nat = [n] twice n. twice : … = [n] suc (suc n). }.` | accepted: forward references between definitions work |
| `m = { loop : int -> int = [n] loop n. }.` | E0101, where the top level gives E0105 |
| `m = { near : node -> prop. near X :- edge X _. hub X :- near X. … }` | E0907, then E0101 for `near` in `hub`: the rejected member's uses are reported |
| `m = { color : Type. red : color. }.` | E0907, then E0101 |
| `f N = g N where g : nat -> nat. g zero = zero.` | E0911 with ``missing: `f.g _ (suc _)` ``: the lifted parameter `N` shows as `_` |

At the top level (`core/elab/Items.scala`, `elabDeclarations`) declarations and definitions come first,
in dependency order, then every clause group (`elabClauseGroups`, one `inBlock` each), then formula
functions, then `%export`. Functions are globals (`GlobalKind.Function`) whose case trees are filled in
after all signatures exist, which is what makes forward references and mutual recursion work. The
reference states this order in "The meta level", "Order of elaboration".

`where` blocks already have functions by clauses inside a context: `Where.lift` closes the function's
type over the context (`Π` for bound variables, `let` for defined ones), adds a hidden global
`owner.name`, and defines the local name as that global applied to the bound variables. `prelude`
re-expresses the context's names over the global's first arguments at each leaf, and the clauses are
padded with wildcards for those arguments.

Size-change termination (`core/elab/SizeChange.scala`) records the calls of every leaf and closes the
call graph once per file (`checkTermination`). Since #92 it follows calls through definitions, record
fields, module members (`member`, which visits a member's `Defined` term) and functor applications.

## 3. Prior art

Clones (`--depth 1`, in the scratchpad): rossberg/1ml 028859a, agda/agda a3f41e8 (sparse:
`src/full/Agda/TypeChecking/Rules`, `doc/user-manual/language`), leanprover/lean4 0bb12a8. OCaml was not
read and is not used as evidence.

### 3.1 1ML

- A structure `{ B }` is a sequence of bindings, and `SeqB` elaborates `B2` in the environment extended
  with the row of `B1` (`elab.ml`, `EL.SeqB`, line 579): members see earlier members only.
- Recursion is an expression, `rec (X : T) => E`, with an annotated type, and the recursive expression
  must be pure ("recursive expression is not pure", `elab.ml`, `EL.RecE`, line 500). Mutual recursion is
  a `rec` over an annotated record: `{even; odd} = rec (self : {even : …; odd : …}) => { even x = …
  self.odd …; odd x = … }` (`README.txt`, "Recursive Functions"). The README adds: "there is no nicer
  syntax for recursive declarations yet."
- `local B1 in B2 end` is `include (let B1 in {B2})` (`README.txt`, derived syntax): helpers are hidden
  lexically. 1ML checks no termination.

### 3.2 Agda

- A parameterised module abstracts its parameters over every definition in it: "module parameters …
  are abstracted from all the definitions in the module", so `Sort.insert : (A : Set)(_≤_ : …) → A →
  List A → List A` outside `module Sort (A : Set)(_≤_ : …)` (`module-system.lagda.rst`, "Parameterised
  modules"). `checkSection` checks a module's declarations inside `newSection` with its telescope
  (`Rules/Decl.hs`, line 920).
- A record declaration also creates a *record module* parameterised by a value of the record
  (`Rules/Record.hs`, `addSection m`, line 359), and definitions written in the record declaration go
  into it. Only non-recursive definitions without pattern matching may be interleaved with the fields,
  "because the type of the record constructor needs to be expressible using let-expressions"
  (`record-types.lagda.rst`, "Record modules").
- Mutual recursion needs each signature before its uses (`mutual-recursion.lagda.rst`, "Interleaved
  mutual blocks"), and termination is checked per mutual block (`mutualChecks` calls
  `checkTermination_`, `Rules/Decl.hs`, line 275).

### 3.3 Lean 4

- `instance : C where f | 0 => … | n+1 => …` is a structure instance. `expandWhereStructInst`
  (`Elab/MutualDef.lean`, line 371) turns `where` fields into `{ … }` notation, and
  `expandStructInstField` (`Elab/StructInst.lean`) turns a field with match alternatives into
  `f := fun x => match x with …`. A field is a non-recursive `match`.
- Recursive helpers are `let rec` or the `where` declarations of the enclosing definition. They are
  lifted to top-level definitions closed over the free variables they use. Mutually recursive ones are
  closed over the union of their free variables, found by a fixpoint (`Elab/MutualDef.lean`, the
  comment before `namespace FixPoint`: `f` and `g` "must be in the closure of both"). They are checked
  for termination with the definition that contains them.

### 3.4 What the references agree on

1. **Functions inside a module or record are lambda-lifted** over the module's parameters (Agda) or over
   the variables they capture (Lean). Neither keeps a closure per instance.
2. **Recursion between members needs the signatures first:** Agda's mutual blocks, Lean's `let rec`
   headers, 1ML's annotated `rec`. Where the language has no such step (1ML structures), members see only
   earlier members.
3. **A record's fields and its recursive functions are kept apart:** Agda's record module, Lean's lifted
   auxiliary definitions. Hugin can make a member function a field because its lifted global exists,
   with its type, before its case tree.

## 4. Assessments

### 4.1 Scope: forward references and mutual recursion

**Assessment: a body's scope is a file's scope.** A member function may be called by every member and
object item of the body, before or after its signature, and member functions may be mutually recursive.
The clauses of `f` are the items `f p̄ = e.` of the body that declares `f`, anywhere in the body, in
order. A body's `f` shadows a file's `f` in the whole body (the reference, "Modules", "Scopes"), so its
clauses are its own: a clause in a body for a function declared outside it is E0915 (no declaration in
this body).

This needs no fixpoint and no `rec`. Signatures are elaborated with the other members, the lifted
globals exist from then on, and the case trees are filled in after all members, as at the top level. A
definition or a later member's type that needs a member function's case tree while the members are
elaborated sees it stuck, as a top-level declaration does (the clauses come after the declarations). A
definition that refers to itself is E0105, as at the top level (today E0101 in a body).

1ML's sequential scope with `rec` is rejected: it would make bodies differ from files, which is what the
issue removes. Agda's record-module split is rejected: in Hugin the body is the module, and the 1ML-style
`lib : S = { f (suc n) = … }` needs `f` as a field.

### 4.2 Lifting

**Assessment: lift each member function over all bound variables of the body's context,** with the
code of `Where.lift`, `closeOver` and `prelude`, shared between the two. The bound variables are the
parameters of enclosing functors and lambdas, and the object members of the enclosing bodies, all of
type `⇑τ` or a meta type. Definitions and other member functions are let-bound in the closed type and
re-defined at each leaf. Every member function of a body takes the same leading arguments, so a call
between two of them passes those arguments through unchanged.

Lean's minimal closure (the union of the variables that a group of functions uses) is rejected for now:
it saves arguments that cost nothing measurable, and it needs a fixpoint over the call graph. The global
is named after the member's path (`lib.double`, `tc.step` for a functor `tc`). The leading arguments are
hidden from users: coverage messages, `--print-after elaborate` and hover show `lib.double (suc _)`,
not one `_` per captured variable. This also fixes `where` functions (`f.g _ (suc _)` today).

### 4.3 Coverage and termination

**Assessment: unchanged, per member function.** Clauses are padded with wildcards for the leading
arguments, which never split, so coverage (E0911) and unreachable clauses (W0006) are those of the
written clauses. Termination is the file's one size-change check:

- a call `g t̄` between member functions is a call between globals; the leading arguments give `⇊=`
  arcs, which neither help nor harm;
- a call through a path, `lib.g t` or `r1.g t` for an instance `r1 = tc …`, reaches the member's
  `Defined` term, the global applied to the context, through #92's `member` and functor application
  rules, so it is the same call;
- a call through a functor parameter (`g.step` of a module passed in) is a call with unknown arguments,
  as today.

A non-terminating member function is E0912 at its clause. An imported file's member functions are
checked when that file is elaborated, as its top-level functions are.

### 4.4 Staging and generativity

**Assessment: a member function is not generative.** The case tree is elaborated once, where the body is
written. For a functor body, that matches #56's rule that a functor body is typed once. An instance's
field is the global applied to the instance's environment: its functor arguments and fresh object
constants. Two instances `r1 = tc g` and `r2 = tc g` have fields that compute the same results but
mention their own relations when they return object code.

Meta code is pure, so per-application elaboration would give the same function every time. It would
also put coverage and termination errors at every application instead of at the body. A member function
whose right-hand side evaluates a module body creates instances at its call sites, as a top-level
function does (`core/Modules.scala`, instances memoised per site).

### 4.5 Incrementality

**Assessment: no change of granularity.** A body is part of its top-level item (one slice, step 9 of
`docs/INCREMENTALITY.md`), and a definition is elaborated with all declarations and clauses
(`Signatures`). Editing a member clause therefore elaborates the declarations again, exactly as editing a
top-level clause does today. Per-member queries would need `Signatures` split per declaration, which
`docs/INCREMENTALITY.md` lists as still coarse for the whole top level. They belong to that work, not
here.

### 4.6 `%export` and sealing

**Assessment: member functions are fields like definitions, so both apply unchanged.** `%export S.` can
name a module field whose type lists member functions (`{ lib : { double : nat -> nat } }`), and
transparent ascription `lib : { double : nat -> nat } = { … }.` hides the other members (E0906 on
selection). The lifted globals are hidden: they are in no scope, so `%use` cannot open them and an
export signature cannot name them.

Sealing (`(e :> S)`, `docs/design/stdlib.md` 4.6 on `design/stdlib-61`, not scheduled) makes a
definition opaque to conversion, not to evaluation. When it lands, the call collection must still follow
a sealed definition, as staging does; this note adds no constraint beyond that. The issue's example
`lib : S = { f (suc n) = …. }` works with `:` now and with `:>` then.

### 4.7 #66: freezing and blocks

**Assessment: each member clause group is a nested block.** Today `Core.inBlock` does nothing inside a
block, so a module definition is one block and everything in it shares its unknowns. Member clause groups
get the top level's discipline:

- the body's members are elaborated, and their unknowns must be solved (E0903 at the signature), before
  the first member clause group, as a top-level signature is its own item;
- a member clause group freezes the unknowns created before it and solves its own; unknowns are numbered
  from `?0` within it in diagnostics;
- `inBlock` saves and restores `frozen` and `blockStart` instead of returning early, so blocks nest.
  Other nested elaboration (`where`-lifted functions, a body's object items) stays in its enclosing
  block.

### 4.8 Error codes

**Assessment: no new codes.**

- E0907 keeps: refinements, families of object constants, meta inductive families and postulates
  (a meta declaration without a definition and without clauses in the body), `$e.` items, additive and
  module-wide directives, `%use`; formula functions by rules until batch 2. The message gets a subject
  of its own per case ("a clause in a module body" no longer exists; "this item in a module body are not
  supported" is fixed).
- A member that E0907 rejects is erroneous: uses of its name are not reported (E0101 today), as for an
  item with a syntax error.
- E0915 (clauses without a declaration) covers a clause whose function the body does not declare.
- E0105 replaces E0101 for a member definition that refers to itself.
- E0911, W0006 and E0912 are reported at member clauses with the member's path.

Meta inductive families in bodies stay E0907. Agda lifts them like functions (module parameters become
datatype parameters, `module-system.lagda.rst`), so they are possible. In a functor body, however, the
question is whether a type is generative per application, as in ML functors, or shared. Nothing in #61
needs them, and they need a design of their own.

## 5. Alternatives rejected

- **1ML's sequential bodies with an explicit `rec`** (4.1): bodies would differ from files, and `rec`
  needs a type annotation that a signature already gives.
- **Agda's record module** (4.1): functions next to the module, not in it, so a signature could not list
  them.
- **A closure per instance** (evaluating the clauses in each instance's environment): the case tree is
  the same for every instance, and coverage and termination would run per application.
- **Lean's minimal closure** (4.2): a fixpoint over the call graph for fewer arguments, no visible gain.
- **Per-member incrementality** (4.5): needs the split of `Signatures`, which is a change for the whole
  top level.
- **Meta inductive families in bodies now** (4.8): generativity of types is a separate question.

## 6. Effects

Newly accepted:

```hugin,ignore
nat : Type. zero : nat. suc : nat -> nat.
arith = {
  even : nat -> bool.
  even zero = true.
  even (suc N) = odd N.
  odd : nat -> bool.
  odd zero = false.
  odd (suc N) = even N.
  half : nat -> nat.
  half (suc (suc N)) = suc (half N).
  half _ = zero.
}.
graph : Type = { node : type, edge : node -> node -> rel }.
hops (g : graph) = {
  bound : nat -> int.
  bound zero = 0.
  bound (suc N) = 1 + bound N.
  near : g.node -> g.node -> rel.
  near X Y :- g.edge X Y.
}.
```

`arith.even` and `arith.odd` are mutually recursive and checked for coverage and termination where they
are written. `hops`'s `bound` is one function shared by all instances.

Newly rejected at the member: a non-covering or non-terminating member function (E0911, E0912), with its
path in the message. Changed messages: E0105 for a self-referencing member definition (was E0101), no
E0101 after an E0907 member, E0907's subjects, and coverage messages of `where` functions without the
lifted arguments.

Size: about +350 and −60 lines of Scala for batch 1, +120 for batch 2; goldens about +200.

## 7. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md, "Changing the
language").

1. **Member functions by clauses.**
   - Code: `ModuleBodies` (signatures as members with lifted globals, the clause groups after the
     members, the scope of clauses); `Where`'s lifting moved to a helper shared with it; `Core.inBlock`
     nesting; hidden leading arguments in coverage messages and printing; E0105 and the erroneous
     names in bodies; E0907's subjects.
   - Reference: `modules.md` "Module bodies" (member functions, scope, the order, E0907's list, an
     example with mutual recursion in a functor body); `meta/index.md` "Meta items" and "Order of
     elaboration" (a body as a file, member clause groups as items); `meta/clauses.md` (the clauses of a
     function are those of the file or body that declares it); `meta/where.md` (if the coverage message
     example changes); `docs/errors/E0907.md`, `E0915.md` and `E0105.md`.
   - Goldens: `run/mc_member_functions` (forward references, mutual recursion, calls through instances
     and paths, a functor body, `%export` of a module field), `neg/mc_member_totality` (E0911, E0912,
     W0006 at members), `neg/mc_body_unsupported` (what E0907 keeps, without cascades), and a
     `where` coverage message. NOTES entry.
   - About +350/−60 lines.
2. **Formula functions by rules in bodies.**
   - Code: the rules of a body's formula function as its clauses, lifted like a member function.
   - Reference: `modules.md` (E0907's list), `meta/staging.md` "Formula functions" (in a body).
   - Golden: `run/mc_formula_members`.
   - About +120 lines.

Batch 2 needs batch 1's lifting. Neither depends on #61's later batches, and #61 B4 and B5 can use
batch 1 once it lands (the issue's queue).

## 8. Sources

- rossberg/1ml 028859a: `README.txt` (kernel and derived syntax, "Recursive Functions"), `elab.ml`
  (`EL.SeqB`, `EL.RecE`).
- agda/agda a3f41e8: `doc/user-manual/language/module-system.lagda.rst` ("Parameterised modules"),
  `record-types.lagda.rst` ("Record modules"), `mutual-recursion.lagda.rst`,
  `src/full/Agda/TypeChecking/Rules/Record.hs` (record section), `Rules/Decl.hs` (`checkSection`,
  `mutualChecks`, `checkTermination_`).
- leanprover/lean4 0bb12a8: `src/Lean/Elab/MutualDef.lean` (`expandWhereStructInst`, the `let rec`
  closure), `src/Lean/Elab/StructInst.lean` (`expandStructInstField`).
- Hugin 0f23678: `core/elab/ModuleBodies.scala`, `core/elab/Items.scala`, `core/elab/Where.scala`,
  `core/elab/SizeChange.scala`, `core/Modules.scala`, `core/Core.scala` (`inBlock`),
  `docs/INCREMENTALITY.md`; `docs/design/stdlib.md` on `design/stdlib-61` (4.5, 4.6).
