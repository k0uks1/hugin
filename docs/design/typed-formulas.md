# Typed reflection beyond terms: formulas, rules and items

Design note for [issue #96](https://github.com/k0uks1/hugin/issues/96), the follow-up of #56
(`docs/design/typed-object-code.md`). Status: proposed, for review by the designer. Nothing is
implemented.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 assessments, 5 alternatives rejected,
6 effects, 7 batches, 8 sources.

## 1. Recommendations

1. **No context index and no typed formula type.** The context of a piece of object code built by a
   generator is the meta context: the `quoted τ` values it mentions, each checked at its type where the
   piece is written. This is Qq's design (`unquoteLCtx`), and #56 already implements it for terms. An
   open formula is a meta function over typed values, `quoted node -> formula`, as open code is a
   function in Scala's higher-order holes, λProlog's `A -> o` and Kovács's `⇑A → ⇑B`.
2. **Typed atoms are `quoted τ` for a type of facts `τ`.** Facts are terms, so a term of the fact type
   `edge` is an atom of `edge`. A `quoted τ` whose index is a type of facts is accepted where a
   `formula` is expected, through a new primitive `qatom`. A generator that returns `quoted edge`
   instead of `formula` gets its columns checked where it is defined, and its atom can stand in a head.
3. **Typed variables.** `qvar : string -> quoted A` makes a variable with a reserved name that source
   syntax cannot write, so generators share variables between pieces through typed meta values instead
   of plain names.
4. **One hole, one variable.** Within one quote, the occurrences of a hole of type `quoted τ` are one
   object variable for meets: their body positions meet with each other and with `τ` (E0401 at the
   generator). Today each occurrence is checked alone.
5. **A lint for variables bound by name through a hole** (W0007, `hole_capture`): a variable of a rule
   quote that only an untyped formula hole can bind is captured by name. This is the one composition
   that typing cannot see, and the lint points at the typed rewrite.
6. **What stays untyped:** `formula`, `rule`, `item`, `module`, `$..Xs : list term`, `$F[V] : term ->
   formula`, and `%demand` and every other directive that is generic over relations. They keep the
   boundary check of #56: reflected data is elaborated again.

No surface syntax changes. Existing programs keep their meaning; the new checks reject only generators
that can build ill-typed rules.

## 2. Hugin today

#56 types quotes where they are written (`core/elab/TypedQuotes.scala`, `checkQuoted`): the content is
read into `OTerm` and `OFormula` and checked by `ObjCheck` as a rule, a body or a term. A hole of type
`quoted τ` is code of type `τ` (`OTerm.Code`), a hole of type `term` is code of unknown type, and a
formula, rule or sequence hole is dropped (`QuoteReader.formulas` returns `Nil` for it). Plain
uppercase variables are checked by meets inside the quote. A quoted pattern's hole at a column of known
type binds `quoted τ` (`QuotedPatterns.typedHole`).

Measured on 9b82924 (scratch programs in the scratchpad, not committed):

| program | result |
|---|---|
| `a : formula = '{ lives X _ }.` `b : formula = '{ lives _ X }.` `r : rule = '{ odd :- $a, $b }.` | accepted |
| `mk F = '{ born X :- $F }.` with `F : formula`, used as `$[mk '{ lives X _ }].` | E0402 at reflection |
| `at_home X = '{ lives $X _ }.` and `in_city X = '{ lives _ $X }.`, `X : quoted person` | E0402 at `in_city` |
| `mk F = '{ born $c :- $(F c) }`, `F : quoted city -> formula`, used with `[p] '{ lives $p _ }` | E0402 at the lambda |
| `g X = '{ both :- teaches $X, cleans $X }.`, `X : quoted staff`, `teaches : teacher -> rel`, `cleans : janitor -> rel` | accepted |
| `e : quoted edge = '{ edge a b }.` | accepted |
| `r : rule = '{ $e :- edge a a }.` with that `e` | E0901 (`quoted edge` is not a `formula`) |
| `bad F = '{ $F :- edge X Y }.` used as `$[bad '{ X < Y }].` | E0202 at reflection |
| `gen X = '{ path $X Y :- edge $X Z }.` used as `$[gen '{ a }].` | E0501 at reflection |
| `x : quoted node = '{ X }.` | accepted, the plain name `X` |

So the typed layer of #56 already composes when pieces share variables through `quoted τ` values: each
piece checks the value at its type. What is not checked at the generator is (i) variables shared by
plain name between separately built pieces, (ii) atoms, which have no typed form and so cannot carry
their relation's columns into a head, (iii) a typed hole used twice in one quote, and (iv) static rules
of a whole rule (range restriction, bound columns).

## 3. Prior art

Clones (`--depth 1`, in the scratchpad): quote4 e7c4cdd, scala3 1095192, lean4 0bb12a8,
AndrasKovacs/staged 9c4e201, gallais/generic-syntax d8d217a, metaocaml/ber-metaocaml 8891433,
teyjus/teyjus 5cb5153, abella-prover/abella 957bb74, standardml/twelf 4224d07. Kiselyov, Kameyama and
Sudo (APLAS 2016) was read as the PDF from the second author's page. Typed Template Haskell was read
from source for #56 (`ghc-internal`, `GHC/Internal/TH/Monad.hs`) and is not repeated here.

### 3.1 Qq (quote4)

- `Quoted α := Expr` (`Qq/Typ.lean`). There is no separate type of formulas: a proposition is a term
  `Q(Prop)` and a proof of `p` is a `Q($p)`. The index is a type, never a context.
- The context is the meta program's local context. `unquoteLCtx` (`Qq/Macro.lean`) walks the local
  context and adds, for every `x : Q(α)`, a variable `$x : α` to a new *unquoted* local context; a
  variable whose type has a `ToExpr` instance enters as itself, and `QuotedDefEq` assumptions enter as
  equations. `q(…)` is elaborated in that context and quoted back by `quoteExpr`, whose `exprBackSubst`
  maps each unquoted variable to the meta value it came from. A free variable that is not in the map is
  an error ("unknown free variable"): a quote cannot mention an object variable that the meta context
  does not hold.
- Binders: object variables under a binder enter the meta context as new `Q(α)` values
  (`withLocalDeclDQ`, used in `Qq/Match.lean`; `quoteLCtx` does the converse for `by_elabq`). Open terms
  never appear as values; a body under a binder is handled with the binder's variable as a meta value.
- Patterns: `getPatVars` (`Qq/Match.lean`) turns each `$x` into a metavariable, and `$f a₁ … aₙ` into a
  metavariable of an n-ary function type (`mkNAryFunctionType`). `elabPat` elaborates the pattern in the
  unquoted context, so pattern variables get their types from elaboration, and binds them as local
  declarations of their inferred types; matching is `isDefEq` at reducible transparency under
  `withNewMCtxDepth` (`mkIsDefEqCore`).

### 3.2 Scala 3

- `typedSplicePattern` (`typer/QuotesAndSplices.scala`): a hole `$x` gets type `Expr[pt]`; a
  higher-order hole `$f(y₁, …, yₙ)` gets `Expr[(T₁, …, Tₙ) => pt]`, where `Tᵢ` is the type of `yᵢ`, an
  identifier bound by a lambda inside the quote. Quoted lambdas carry their parameter types, so `Tᵢ` is
  known. `typedAppliedSplice` reports "Missing arguments for open pattern"; arguments must be
  identifiers, and `var`s are refused.
- `QuoteMatcher.scala`: a plain hole matches only code closed under the pattern's own binders
  (`isClosedUnder()`); a higher-order hole matches code whose free pattern-bound variables are among its
  arguments and abstracts them (`lift`). `Expr[T]` is never open with respect to the quote.
- `QuotePatterns.checkPattern` restricts type arguments of higher-order holes to type variables
  introduced in the pattern.

### 3.3 MetaOCaml and environment classifiers

- BER MetaOCaml (`ber-metaocaml-153/NOTES.txt`, N101): environment classifiers were removed; the code
  type is `'a code`, "possibly open code". "The scope extrusion check made it possible to remove
  environment classifiers while still preserving the static guarantee: if the generator finishes
  successfully, the generated code is well-typed and well-scoped." The check is dynamic. The okmij page
  on MetaOCaml says classifiers caught only rare errors and "often gave false positives".
- Kiselyov, Kameyama, Sudo, *Refined environment classifiers* (APLAS 2016): code types `⟨t⟩^γ` carry a
  classifier `γ`, a type-level name of a binding environment; classifiers are partially ordered, and code
  of `γ₁` is used at `γ₂ ⊒ γ₁` by subsumption. A future-stage `λ` introduces a fresh classifier below
  the current one (rule for `λx.e`, Fig. 7; the order, Fig. 8). The paper's motivation is effectful
  generators, where well-scopedness is not structural. Its contexts compose along a nesting order of
  binders.

### 3.4 Intrinsically typed syntax with contexts

- generic-syntax (`src/Generic/Syntax.agda`): `Tm d s : I ─Scoped`, `I ─Scoped = I → List I → Set`; a
  term is indexed by its sort and an ordered context. Variables are typed de Bruijn indices (`Var`:
  `z`, `s`, `src/Data/Var.agda`); `Scope T Δ i = (Δ ++_) ⊢ T i` extends the context under a binder.
  Weakening is not free: `th^Tm` (`Generic/Semantics/Syntactic.agda`) is a renaming traversal along a
  `Thinning`. `Generic/Semantics/Elaboration/Typed.agda` elaborates bidirectional raw syntax into typed
  terms by a `Semantics` whose result depends on a `Typing` of the context.
- Kovács (`demo/Cxt.hs`): the elaborator's one context `Cxt` holds meta and object variables, each with
  its stage (`bind cxt x a st`); `⇑A` has no context index. Open object code is a meta function over
  `⇑A`. The analysable STLC (`demo/examples/STLC.2ltt`) is a user-level deep embedding with
  `Con`, `Var : Con → Ty → U1`, `Tm : Con → Ty → U1` and `snoc` contexts.

### 3.5 λProlog, Twelf, Abella

- Teyjus (`source/tables_gen/pervasives/pervasives.in`): goals and clauses are terms of type `o`; `,`,
  `;`, `:-` and `=>` are `o -> o -> o`, `pi` and `sigma` are `(A -> o) -> o`. A clause's free variables
  are closed by `pi`, so an open formula is an abstraction `A -> o` whose binder fixes the variable's
  simple type. There is no context index; the context is the λ-binders (HOAS).
- Twelf (`doc/guide/twelf.texi`, "Term Reconstruction"): a clause is a constant declaration; free
  variables get "most general types" by reconstruction and implicit quantifiers. The per-clause context
  is inferred, never written. Contexts appear only for hypothetical judgements, as regular worlds
  (`%block`, `%worlds`).
- Abella (`examples/process-calculi/session_types/sess.thm`): contexts of the specification logic are
  explicit in the reasoning logic (`{G, hyp y C |- hyp X A}`), described by user predicates (`ctx G`).
  This is a proof system over specifications, not a metaprogramming API.

### 3.6 What the references agree on

1. **No metaprogramming API indexes code by a context.** Qq, Scala, MetaOCaml and Typed Template Haskell
   index by a type only. MetaOCaml removed its classifiers; refined classifiers are a calculus for
   effectful generators. Context-indexed syntax appears as a user-level embedding (Kovács's STLC,
   generic-syntax) where weakening is a traversal.
2. **The context of a quote is the meta context.** Qq's unquoted local context, Scala's splices and
   `Expr` arguments, Kovács's single `Cxt`, λProlog's binders: an object variable that crosses a quote
   boundary is a meta value of a code type.
3. **Open code is a function.** Scala's `$f(x)` binds `Expr[T => R]`, Qq's `$f x` a function-typed
   metavariable, λProlog `A -> o`, Kovács `⇑A → ⇑B`. Parameter types come from annotated binders.
4. **Per-declaration inference of variable types** (Twelf's reconstruction, Hugin's meets) works on a
   whole clause, not on fragments.

## 4. Assessments

### 4.1 The options

**Assessment: (c), the context is the meta context. Reject (a) and (b).**

(a) `quoted_formula Γ` with `Γ : list (string × ⇑type)` fails on Hugin's own rules. The context of a
conjunction is the pointwise meet of its parts, `Γ₁ ⊓ Γ₂`, a judgement of the object type system on
opaque `⇑type` values. In a generic function `conj : quoted_formula G₁ -> quoted_formula G₂ ->
quoted_formula (G₁ ⊓ G₂)` the meet is stuck, and checking a hole against a stuck context needs
conversion modulo the semilattice laws of `⊓`. Meets are not invertible, so a quoted pattern
`'{ $F, $G }` against `quoted_formula Γ` cannot give `F` and `G` any context. Subtyping would need a
variance for `Γ` (contravariant for matching positions, covariant for constructing ones), and every
signature of every generator changes. generic-syntax shows the cost of ordered contexts: weakening is a
renaming traversal, and Hugin's rules have no binders that would order them.

(b) A checked-formula type that remembers "well-typed in isolation" buys nothing: two well-typed
formulas conjoin to an ill-typed one (`lives X _` and `lives _ X`), so the flag does not compose. Quotes
are already checked where they are written.

(c) adds no type former for formulas. Its context is what Qq's is: the `quoted τ` values in the meta
context. Two pieces that share a variable share a meta value of a fixed type, and each piece is checked
against it. Hugin needs three additions to make this complete enough to use: typed atoms (4.2.7),
typed variables (4.2.8) and one variable per repeated hole (4.2.1). What it buys, concretely:

- a generator that builds an atom gets its columns checked at its definition and can put the atom in a
  head (today: `formula`, unchecked as a head until reflection, E0202);
- a hole used twice in one rule with no common type is E0401 at the generator (today: at reflection);
- pieces that share a variable through `qvar` are checked against its type, so a piece that uses it in
  the wrong column is rejected where the piece is written (today: plain names, found at reflection);
- the remaining name-based composition is reported by the lint (4.2.9).

### 4.2 Hugin specifics

#### 4.2.1 Meets over uses, and composition

**Assessment: the checker computes meets inside one quote, for plain variables and, new, for repeated
holes; across pieces, a typed variable is checked against its declared type, and the meet over the
whole rule is the boundary check's.**

Inside one quote, plain variables are typed by meets (today). New: the occurrences of a hole whose
expression is the same meta variable `X : quoted τ` are read as one variable `$X`: every body position
adds a bound, and `τ` is a further bound, so their meet must be non-empty (E0401). In a head, `$X` keeps
the rule of #56: `τ ≤ σ`, since the data may be a constructor term, not a variable. The identity of a
hole is the core variable it refers to (a de Bruijn level), not its value.

Across pieces, a typed variable `x : quoted τ` is checked at `τ` in each piece: `τ ≤ σ` in a head, a
non-empty meet with `σ` in a body. This does not guarantee a non-empty meet over the whole rule: with
`staff` having members `teacher` and `janitor`, two pieces using `x : quoted staff` at `teacher` and at
`janitor` both pass, and the reflected rule is E0401. Declaring the variable at the type the rule needs
(`quoted teacher`) makes the per-piece checks exact. The declared type is not data (types are not data,
and `⇑` is not reified, #56 4.6), so the reflected rule cannot carry it; the boundary check covers the
rest.

#### 4.2.2 Subtyping

**Assessment: unchanged from #56.** `quoted τ ≤ quoted σ` if `τ ≤ σ`, `quoted τ ≤ term`; new:
`quoted τ ≤ formula` if `τ` is a type of facts (4.2.7). Passing `x : quoted staff` to a generator that
takes `quoted teacher` is E0901: a meta function's parameter type is its declared type, not a bound.
Narrowing a variable is a decision of the generator that creates it (`qvar` at the narrow type).

#### 4.2.3 Named patterns

**Assessment: nothing to add.** A named pattern `r { l = $X, .. }` is analysed as the atom of `r` with
its arguments in column order, so its holes are typed by their columns (measured: `person { name = $N,
age = $A }` binds `A : quoted int`). As a typed atom, `'{ r { l = $X, .. } }` at `quoted r` is checked
like any term of `r`.

#### 4.2.4 Aggregates

**Assessment: binders stay locally nameless and plain; a typed variable cannot be bound by an
aggregate.** The variable an aggregate binds is the plain variable its term names, represented by
`tbound`. A `quoted τ` value is free in the quote (it comes from the meta context), as in Scala, where a
plain hole matches only code closed under the quote's binders. Typed holes inside aggregate bodies are
checked like any (measured: `owner V $P` with `P : quoted int` is E0402). Abstracting over the bound
variable stays with `$F[V]` (4.3).

#### 4.2.5 Negation

**Assessment: nothing to add.** Atoms and holes under `not` are matching positions; a typed atom under
`not` is a formula like any other. Safety of negation (every variable of a negated atom bound
positively) is a rule of the whole rule and stays at reflection with range restriction (4.2.6).

#### 4.2.6 Typed rules: heads, bodies, range restriction, bound columns

**Assessment: heads and bodies are checked as today, with typed atoms allowed in both; range
restriction, negation safety and bound columns stay at reflection.** A rule quote is checked as a rule:
its heads at constructing positions, its body at matching ones. A head may be a typed atom
`$a : quoted r`, whose columns were checked when `a` was built; the quote checks only that `r` is a
type of facts. Range restriction (E0501) is not decided at the generator: a variable can be bound by
name through an untyped formula hole or a `term` hole, so "unbound" is not known. The lint (4.2.9)
reports the case that typing cannot see. Bound columns (E0605) depend on the staged relation and stay
where they are.

A typed rule type (`qrule r`, indexed by the head's fact type) is rejected: nothing consumes the index,
and a rule is checked as a whole where it is written.

#### 4.2.7 Atoms

**Assessment: an atom of `r` is a `quoted r`; `qatom : quoted A -> formula` is a primitive, inserted as
the coercion where a formula is expected and `A` is a type of facts.**

Facts are terms, and a relation's fact type is an object type, so `'{ edge a b }` checked against
`quoted edge` is already accepted and checked at constructing positions (measured). What is missing is
the way back: `quoted edge` is not a `formula` (E0901). `qatom` reduces on closed data `qterm (tapp s
ts)` to `fatom s ts`, and stays stuck on any other term, like `derive` and `labels`. Stuck data is
reported when it is reflected (E0918, with the note "the term of type `quoted r` is not an atom"). It is
a primitive because the meta level is total: a prelude clause for the other terms would have to invent
a formula. The coercion is checked at the meta level: `A` must be a type of facts (a relation, struct or
constructor type, an open type of facts, a union of them, or `(rel)`), otherwise E0901 with the note
"`node` is not a type of facts".

A typed atom built as a term is checked at constructing positions (`τ ≤ σ` for its variables), so it
fits both a head and a body. A body atom that narrows a variable (`teaches $X` with `X : quoted staff`)
is written in a formula quote instead.

#### 4.2.8 Variables and hygiene

**Assessment: `qvar : string -> quoted A`, a prelude definition, `qvar N = qterm (tvar (N ^ "#v"))`.**
Source syntax cannot write `#`, so `qvar "x"` cannot capture a variable of the program, as the names of
`%demand` (`_a#0`) since #56. Names are values, so two `qvar "x"` in one rule are one variable; two
different hints are two variables. The type `A` is the generator's statement of the variable's type;
the variable has no type of its own until the rule's meet, so `qvar` checks nothing. Display drops the
suffix, as for `%demand`'s names.

A fresh-name supply (a counter, Lean's macro scopes) is rejected: the meta level is pure, and
determinism by hint is what a rule needs (the same name is the same variable).

`'{ X }` checked against `quoted τ` stays as it is (a plain, capturable name), since programs use it.

#### 4.2.9 Name capture through holes

**Assessment: a lint, W0007 `hole_capture`, warning by default if the probe in batch 3 finds no false
positive in `tests/`, `examples/` and the reference.** A plain variable of a rule or item quote that
occurs in a head or a typed position and is bound by no positive atom or equation of the quote, while
the quote's body has a hole of type `formula`, `list formula` or `term`, can only be bound by name
through that hole. The warning says so and names the typed rewrite (pass the variable to the hole as a
`quoted τ`). It cannot see sharing between two quotes that are combined later (`'{ odd :- $a, $b }`
with `a` and `b` mentioning `X`); that stays at reflection.

#### 4.2.10 Items and modules

**Assessment: unchanged.** An item is a rule, a named rule, a query, an error or a declaration; its
quote is checked as such. `irelation s cols` declares a relation from `colof` references, which are
checked when the item is reflected. `module = list item` has nothing to index.

#### 4.2.11 `%demand` and module-wide directives

**Assessment: they stay untyped, as Lean's `Expr`-level metaprograms (`simp`, `omega`) stay on `Expr`
while Qq serves fixed shapes.** `%demand r m` handles any `r : sym` with heterogeneous columns: it takes
atoms apart with `'{ $S $..Ts :- $..B }`, compares symbols with `same`, and builds `fatom (derive R
"check") (dinputs M Ts)`. A typed signature would need

- the column types of a symbol as data, `coltypes : sym -> list ⇑type`, which #56 excludes (types are
  not data);
- a heterogeneous list `targs : list ⇑type -> Type` for `$..Ts`, and `modes` indexed by column types;
- an equality that `same R S` refines (`coltypes R ≡ coltypes S`), which needs identity types and
  decidable equality on symbols at the meta level;
- subtyping between the columns of `r` and the arguments of its calls inside `targs`.

That is a dependently typed reflection of the object signature for one directive whose output is
checked anyway, by goldens and by the boundary check of every program that uses it. The typed additions
of this note do not touch it: `qatom`, `qvar` and the repeated-hole rule apply only where typed values
occur.

### 4.3 Quoted patterns

**Assessment: unchanged, apart from typed atoms in expressions.** Holes at typed columns bind
`quoted τ` (#56); `$..Xs` binds `list term`; formula, rule and item holes bind their categories;
`$F[V]` binds `term -> formula` (or `term -> term`).

- Typing `$F[V]` as `quoted τ -> formula` (Scala's `Expr[T => R]`) is rejected: Scala takes `T` from
  the lambda's annotation, and Hugin's aggregate binder has none; a type found by meets inside the
  pattern would be wider than the data's. `quoted τ ≤ term`, so `F (qvar "w")` works already.
- A hole in an atom position binding `quoted (rel)` (an atom pattern with its type) is rejected: the
  data at that place is `fatom`, so the binding would need a conversion that is total on formulas, and
  the hole's type is not tested when matching (#56 4.6).
- A head hole stays `formula`, for the same reason.

### 4.4 Surface syntax

**Assessment: none.** New prelude names `qatom` and `qvar` (with the `q` of `qterm`, so they are unlikely
to clash; a program's own names shadow them as for other prelude names). The coercion `quoted τ ≤
formula` is inserted by the elaborator. Programs that type-check today keep their meaning; generators
newly rejected are those of 6.1.

### 4.5 Interaction with #66

**Assessment: compatible; three constraints.**

- `quoted` stays a postulated type former (#56, and `elaborator-glued.md` section 5), so the problem
  `quoted τ =? quoted σ` is decided on the indices, never by unfolding. `qatom` is a primitive and does
  not unfold; `qvar` is a definition and unfolds to `qterm (tvar …)` in the unfolded read-back only, and
  its type keeps the index.
- Quote checks run at the end of the block, in the order of `elaborator-glued.md` 4.1: the #56 store is
  solved, the hole types are read with metas instantiated, then `checkSolved`, then freezing. An
  unsolved hole index is `OTy.Unknown` (no report), never a frozen meta of a later block.
- The identity of a repeated hole is the core variable it refers to, so it does not depend on folded or
  unfolded forms. Object types of indices are computed from forced (unfolded) values, as `objEnv.oty`
  does, so `name : type = string` in an index is `string`.

## 5. Alternatives rejected

- **Context-indexed formulas and rules**, (a) in 4.1.
- **A checked-formula layer**, (b) in 4.1.
- **Refined environment classifiers for rule scopes** (`formula γ`, one classifier per rule being built):
  classifiers order nested binders; a rule's variables are not nested, and their types are meets, which
  a classifier does not record. MetaOCaml dropped classifiers for false positives.
- **Checking closed holes by evaluating them at the quote**: it moves reflection earlier for closed
  pieces only, while generators' pieces are parameters; it costs evaluation during elaboration.
- **Plain variables local to their quote** (Qq's "unknown free variable"): it would catch every name
  capture, but changes the meaning of programs that share variables by name, including the reference's
  `p X :- $body.`, and of reflected formulas in object code.
- **Carrying a typed variable's declared type into the data** (an ascription on reflection): ascriptions
  are checked downcasts with run-time meaning and have no representation (E0917), and types are not data.
- **Strict body positions for typed holes** (`τ ≤ σ` also when matching), which would make per-piece
  checks compositional: it rejects narrowing, a legitimate use of a body atom, and changes #56's rule
  for spliced code.
- **A formula constructor for typed atoms** (`fterm : term -> formula`): it changes the reflective type
  `formula`, so every function that covers `formula` (the prelude's `openF`, `fvars`, programs' own)
  gains a missing case (E0911).
- **A typed `%demand`**, 4.2.11.

## 6. Effects

### 6.1 Checked at the definition, before and after

Typed atoms. Before, a generator of atoms returns `formula`, and a non-atom in a head is found at
reflection (E0202):

```hugin,ignore
node : type. a : node. b : node.
edge : node -> node -> rel.
link : quoted node -> quoted node -> formula.
link X Y = '{ edge $X $Y, edge $Y $X }.
both_ways : rule = '{ $(link '{ a } '{ b }) :- edge a b }.
$[both_ways].
```

After, `link` returns `quoted edge`; the conjunction is rejected at `link` (E0917, a conjunction is not
a term; measured), and `'{ $(link X Y) :- … }` puts a checked atom in the head:

```hugin,ignore
link : quoted node -> quoted node -> quoted edge.
link X Y = '{ edge $X $Y }.
both_ways : rule = '{ $(link '{ a } '{ b }) :- edge a b }.
```

A generator that misplaces a column of its atom is E0402 at its definition, as typed terms are today.

Repeated holes. Before, accepted; the rule is E0401 when reflected with a variable. After, E0401 at `g`:

```hugin,ignore
staff : type.
teacher : (n : string) -> staff.
janitor : (n : string) -> staff.
teaches : teacher -> rel.
cleans : janitor -> rel.
both : rel.
g : quoted staff -> rule.
g X = '{ both :- teaches $X, cleans $X }.
```

Name capture. Before, accepted at `mk`; E0402 at the reflection `$[mk …]`. After, W0007 at `mk`:

```hugin,ignore
person : type. city : type.
lives : person -> city -> rel.
born : city -> rel.
mk : formula -> rule.
mk F = '{ born X :- $F }.
```

The typed rewrite, with `qvar`; the misplaced variable is E0402 at the lambda, where the piece is
written (measured with `qterm (tvar "c#v")` in place of `qvar "c"`):

```hugin,ignore
mk : (quoted city -> formula) -> rule.
mk F = '{ born $c :- $(F c) }
  where c : quoted city = qvar "c".
$[mk ([p] '{ lives $p _ })].
```

### 6.2 What stays at reflection

- a variable shared by plain name between pieces built apart (`'{ odd :- $a, $b }`), except what the
  lint sees;
- the meet of a typed variable over pieces checked apart (4.2.1);
- range restriction, negation safety, bound columns, stratification, termination;
- everything built with constructors, `qterm` or untyped holes, and all output of `%demand` and other
  generic directives;
- a `qatom` of data that is not an application (E0918).

### 6.3 Diagnostics

No new error codes. E0401 is reported at a generator for a repeated hole; its explanation gains that
example. E0901 gets the note "`τ` is not a type of facts" for the atom coercion. E0918 gets the note for
a stuck `qatom`. New warning W0007 "variable bound by name through a hole", lint `hole_capture`, with an
explanation in `docs/errors/W0007.md`. Hover (#54) shows `quoted r` for typed atoms.

### 6.4 Size

About +450 and −30 lines of Scala and prelude, +200 lines of reference and explanations, six goldens:

| part | files | lines |
|---|---|---|
| repeated holes | `TypedQuotes.QuoteReader` (holes as variables with a bound), `ObjCheck` (none) | +60 |
| typed atoms | prelude `qatom`, the builtin's reduction, `Coercions`/`TypedQuotes.coeQuoted` (to `formula`), `QuoteReader` (typed atoms in heads and bodies), `Reflection` (stuck `qatom`) | +180 |
| typed variables | prelude `qvar` | +5 |
| lint | a pass over analysed quotes (`Q`), `Code.W0007`, `Lint.HoleCapture` | +120 |
| goldens | `neg/tf_repeated_holes`, `neg/tf_typed_atoms`, `run/tf_typed_atoms`, `run/tf_qvar`, `neg/tf_hole_capture` (warning), a round trip in `run/tf_typed_atoms` | +90 |

## 7. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md, "Changing the
language"). `reflection.md` is also being edited by the reference audit (its introduction); these batches
touch the sections "Quotes", "Typed terms" and "Holes" and follow the audit.

1. **Repeated holes.** Code: `QuoteReader`. Reference: `reflection.md` "Quotes" (the paragraph on how a
   quote is object-typed: the occurrences of one hole are one variable), with a `compile_fail,E0401`
   example; `object/types.md` "Where object code is typed" (one sentence and a link);
   `docs/errors/E0401.md` (the generator example). Golden `neg/tf_repeated_holes`. NOTES entry.
2. **Typed atoms.** Code: `qatom` (prelude, builtin), the coercion, `QuoteReader`, `Reflection`.
   Reference: `reflection.md`, "Typed terms" becomes "Typed terms and atoms" with a `hugin,run` example
   (a generator of atoms used in a head and a body) and a `compile_fail,E0901` example (`quoted node` as
   a formula); the table of reflective types (`qatom`); `prelude.md` "Reflection" and "Booleans and
   primitives" (`qatom` is a primitive); `notation.md` glossary ("typed atom");
   `docs/errors/E0901.md` and `E0918.md` (notes). Goldens `neg/tf_typed_atoms`, `run/tf_typed_atoms`.
3. **Typed variables and the lint.** Code: `qvar` (prelude), the lint, `Code.W0007`. Reference:
   `reflection.md`, a subsection "Typed variables" under "Typed terms and atoms" with a `hugin,run`
   example (pieces sharing `qvar` variables) and a remark on name capture; `prelude.md` (`qvar`);
   `notation.md` glossary ("typed variable"); `docs/errors/W0007.md`; the list of lints in
   CONTRIBUTING.md, "Lints and fixes". The probe over `tests/`, `examples/` and the reference decides the
   default level, and the pull request reports it. Goldens `run/tf_qvar`, `neg/tf_hole_capture`.

Batch 1 is independent. Batch 3's lint names the typed rewrite of batch 2's examples, so it comes last.
`directives.md` does not change: it says already that directives work on the untyped reflective types.

## 8. Sources

- quote4 e7c4cdd: `Qq/Typ.lean` (`Quoted`, `Quoted.check`, `QuotedDefEq`), `Qq/Macro.lean`
  (`UnquoteState`, `unquoteExpr`, `unquoteLCtx`, `quoteExpr`, `quoteLCtx`), `Qq/Match.lean`
  (`getPatVars`, `mkNAryFunctionType`, `elabPat`, `mkIsDefEqCore`, `makeMatchCode`).
- scala3 1095192: `compiler/src/dotty/tools/dotc/typer/QuotesAndSplices.scala` (`typedSplicePattern`,
  `typedAppliedSplice`, `typedQuotePattern`), `compiler/src/dotty/tools/dotc/quoted/QuotePatterns.scala`
  (`checkPattern`), `compiler/src/scala/quoted/runtime/impl/QuoteMatcher.scala` (the rules for term
  and higher-order holes, `Env`).
- metaocaml/ber-metaocaml 8891433: `ber-metaocaml-153/NOTES.txt` (N101), `ber-metaocaml-153/README`;
  okmij.org, "MetaOCaml" page (read 2026-10-09).
- O. Kiselyov, Y. Kameyama, Y. Sudo, *Refined Environment Classifiers: Type- and Scope-safe Code
  Generation with Mutable Cells*, APLAS 2016 (PDF from cs.tsukuba.ac.jp/~kam/papers/aplas2016.pdf):
  §1, Fig. 1, Figs. 5, 7 and 8.
- gallais/generic-syntax d8d217a: `src/Generic/Syntax.agda`, `src/Data/Var.agda`,
  `src/Generic/Semantics/Syntactic.agda`, `src/Generic/Semantics/TypeChecking.agda`,
  `src/Generic/Semantics/Elaboration/Typed.agda` (Allais, Atkey, Chapman, McBride, McKinna, ICFP 2018).
- AndrasKovacs/staged 9c4e201: `demo/Cxt.hs`, `demo/examples/STLC.2ltt`.
- teyjus/teyjus 5cb5153: `source/tables_gen/pervasives/pervasives.in`, `examples/misc/maps.mod`.
- standardml/twelf 4224d07: `doc/guide/twelf.texi` ("Term Reconstruction", "Regular Worlds").
- abella-prover/abella 957bb74: `examples/process-calculi/session_types/sess.thm`.
- Hugin 9b82924: `core/elab/TypedQuotes.scala`, `core/elab/QuotedPatterns.scala`,
  `core/elab/QuoteTerms.scala`, `core/elab/Reflection.scala`, `core/objtype/ObjCheck.scala`, the
  prelude's reflection and `%demand`; branch `design/elab-66`, `docs/design/elaborator-glued.md`
  sections 4.1 and 5.
