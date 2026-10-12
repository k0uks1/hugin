# #186 implementation — decisions log (for final report to designer)

## Lead decisions
- L1: P1 relaunched with a fresh agent continuing the stopped agent's uncommitted WIP, under the designer's "officially begin"; scope from the final note (incl. D2, %assumptions).
- L2: P2 and P8a started in parallel with P1 (independent areas per plan; P8a "any time").
- L3: Each PR body carries a "Decisions" section; the note's "Implementation decisions" section is updated at the end (single docs PR) to avoid parallel conflicts.

## Agent decisions (per PR)
### P1 (feat/proofs-p1-postulates, 6d1379a)
1. E0925 for --safe; covers imported files.
2. %postulate only as top-level definition (expr → E0103; module body → E0907).
3. Trusted primitives = %builtin ops + native std/nat; meta int arithmetic/evaluator not listed; --safe doesn't reject trusted primitives.
4. `%assumptions NAME.` top-level directive; counts as use for W0003; output to explanations stream (not visible in editors: no info severity).
5. --print-assumptions resolves root file first, prefers meta constant.
6. D2 recomputed per constructor; shortening prefix re-checks earlier constructors (E0914 note).
7. Predicativity exemption only implicit param binders; termination excludes all param-position binders.
8. Clause-less check after all declarations of a file; skipped for signature-only elaboration of imports.
### P8a (feat/proofs-p8a-export, a12eccc)
1. --export-proofs <file> + --proof-format trees|ordered-graph (default trees).
2. Pinned to CertifyingDatalog checker v0.2.0.
3. Negation/comparisons exported as assumption-relation leaves ("not r", "<") (Gelfond–Lifschitz reduct).
4. Unsupported constructs (constructor terms, arithmetic, aggregates, as, bound heads) omitted with warning; facts listed hugin.assumedFacts.
5. Bound-column heads omitted (Limit Datalog ≠ least model).
6. Input facts → bodyless rules.
7. Least-depth proof via BFS fixpoint, deterministic.
8. Export the engine's transformed program (post demand/records/disjunction), qualified names.
9. Negative premises printed, not stored as values.
10. Aggregate witnesses deferred to P6/P8b.
11. Pretty JSON.
12. New reference page "The command line".
Also: unnamed rules never had derivation facts — documented as limitation (names in P7b).
### P2 (feat/proofs-p2-basics, 4fa20dc)
1. `:=` recognized in parser as ':' '=' in braces; one name per braces.
2. {x := e} only names implicits before the next explicit binder (Agda rule); clause arity grows; constructor patterns any implicit.
3. New E0926 (named implicit errors); reuse E0915/E0701/E0907.
4. %opaque is a file-level item for own defs; not in module bodies (E0907).
5. Opaque = own GlobalKind, not a postulate; termination still follows opaque calls.
6. decEq in Hugin from `same` + trusted primitives sameTrue (reduces to refl) and apart (never reduces); canonicity kept.
7. All in std/eq; `sym` name clash with std/reflect resolved by %use selection; J named eqElim; uip, emptyElim added.
8. "atomic value" wording.
Also fixed: parser misread `{x y : A}` multi-binders; crash in Universes.objectPartsValid on `P x`.
Lead note: sameTrue/apart are trusted primitives → must appear in P1's assumption listing (check after both merge).
- L4: Merged P2 (#194) before P1 (#192) (P2 green, P1 still fixing CI); P1 then merges base and extends the assumption walk into opaque definitions (P2 agent's finding) + decEq golden.
- L5: P3 started right after P2 merged; P4 started in parallel (independent of P2).
- L6 (designer request, lead decision): new batch P2b after P4 — symbolic %infix bound to functions; Idris-style type-directed operator overloading (no typeclasses); equality operator ≡ with ASCII `==` (=` taken by definitions/formulas; `==` unused); precedences match object table (≡ 4, + - 6, * / 7, ^ 8 right).
- L7: Fuzz hang (mutant with 2^63 numeral) is a pre-existing compiler bug, not P1's: filed #195; fix = weak-head on-demand index unification (Cockx–Abel/Lean defeq) + evaluator polls Cancellation (stops leaked threads → OOMs). Fuzz generator unchanged. P1 may merge when CI green.
### P1 follow-up (e9922f0): assumption walk follows opaque definitions (term/case tree); golden p1_assumptions_opaque.
### P3 (feat/proofs-p3-match, 7abc73e → pending `in` fix)
1. `match`, `rewrite` reserved keywords; LEAD OVERRIDE: `in` contextual (only after `rewrite e`), since `in` is a common Datalog relation name (C#/Rust/Kotlin contextual keywords).
2. Equation arg only when named (`match H :`), as implicit {H : eq e y}.
3. match H:/rewrite use std/eq's eq/refl/subst/sym when loaded (Agda BUILTIN EQUALITY); else E0929.
4. Abstraction: numerals atomic (N+k contains N+j, j<k); no occurrence → goal unchanged for match, error E0928 for rewrite; recheck skips universes.
5. Branch patterns parsed above `|`; nested match in non-last branch needs parens (Lean).
6. Codes E0927 ill-typed abstraction, E0928 cannot rewrite, E0929 no equality library.
7. Termination messages report f and f.match.
Also: termination error label now shows a call on the cycle (general fix).
- L8 (process): benchmarks serialized via scratchpad/benchlock (flock); plain java, targeted programs only; overlapping runs discarded.
- L8 amended (designer): never re-run full benchmarks; use existing numbers with a contention note, plus deterministic step counts; no new timed runs.
### #195 fix (PR #197)
1. Delayed applications reuse neutral Rigid(Glob f, sp) (no thunk value).
2. whnf: strict under 32-poll budget (memoised), else stepwise (avoid call-by-name blowup).
3. Diagnostics show normal form only if ≤64 polls.
4. Cancellation polled every 1024 case-tree runs; platform cancellation only → LSP in-query cancellation filed as #198.
- L9 (process): agents must use wait timeouts ≤ 2× expected suite time (P4 hung 21 min unnoticed behind a 58-min wait); include in all future prompts.
- L10 (designer rule): agents do NOT run test suites locally before pushing — only compile/format and the tests they newly wrote or changed; CI runs the full suite. Include in every future prompt.
### P4 (feat/proofs-p4-int, 8942fbb, draft PR)
1. int family in std/nat (toInt needs it); arithmetic in std/int; `int` = base type at object level, family at meta level.
2. i-prefixed names (iplus…).
3. Division toward zero (object level, Lean Int.tdiv); x/0 = 0 at meta (Lean/Rocq).
4. Object code: meta operands computed exactly, result range-checked; div by zero still E0909.
5. Meta ints without std/nat+std/int → E0931.
6. Native results capped at 2^24 bits (stay stuck).
7. Unknown operand type → primitive arithmetic node.
8. E0909 note wording kept ("overflow") — revisit.
9. E0930 (64-bit crossing), E0931.
Perf: int_arith +17% (BigInt function application vs Long primitive) — accepted for now, noted in PERFORMANCE.md; candidate follow-up.

## Lead decisions (continued)
- **L11 — P5 split into two PRs.** P5a: values, relation references, `program`, `derives`/`premises`, positivity, index unification on object code, `add64`, §11.1 as a test. P5b: `holds` and its soundness, monotonicity, the model-theoretic equivalence, §11.2–11.3. Reason: 1600–2300 estimated lines is too big for one reviewable PR; P5a is the foundation P5b and P7a/P7b build on.
- **L12 — P4 integer-vs-constructor comparison.** A native `IntNum` is compared with `ofNat`/`negSucc` by expanding the literal one constructor layer and comparing arguments; the view is never re-normalised. Prior art: Lean 4 kernel (Nat literal → `Nat.succ` on demand, one direction only); Agda `constructorForm` (literal → `suc`). Hugin differs in folding `ofNat <numeral>` to `IntNum` during evaluation (for compactness and native arithmetic), which is why the comparison must not call `whnf` on the view.

## P2b (agent)

- *Syntax.* `%infix op f.` binds a symbol to a meta function; it has no associativity or precedence,
  since the symbol keeps its place in the one operator table (`+ -` 6 left, `* /` 7 left, `≡` between
  `|` and `::`, non-associative). A binding therefore never changes how a file parses, and parsing stays
  independent of imports (the `%infix` prescan and slices are unchanged). Lean 4's `infixl:65 " + " =>
  HAdd.hAdd` also binds a notation to a function in one command; fixing the fixity per symbol is OCaml's
  rule (an operator's precedence is given by its first character). The name form `%infix assoc p name.`
  is unchanged.
- *Symbols.* `+ - * / ^ ≡`, with `==` as the ASCII spelling of `≡` (a new token; `=` stays the sign of
  definitions and object comparisons). The comparisons `< <= > >= <>` are not bindable: they are object
  formulas. `≡` sits at internal level 42, below `::` (45) and arithmetic and above `->` and `|`, so
  `x :: xs ≡ ys` and `(n m : nat) -> n + m ≡ m + n` need no parentheses: Agda's `infix 4 _≡_` below
  `infixr 5 _∷_`. In the user-level table it is in the column of level 4 with `|`.
- *`^`.* It stays at level 6, left, where the object level has it as string concatenation; Agda's
  `infixr 8 _^_` would change the object grammar. `^` is bindable, and the library binds it to nothing
  (`std/nat` has no power function).
- *Where a binding may be declared.* In the file that declares the function (Haskell's rule for fixity
  declarations, Agda's for operators); the function is a meta constant with at least two explicit
  arguments. Otherwise E0701, as for `%opaque`. In a module body it is E0907.
- *Scope.* A binding travels with its function: it is in effect wherever the function's name denotes
  the function (declared in the file, opened by `%use`, opened by the prelude), as an Agda operator is
  its name. `%use "std/nat" (minus).` brings `-` and not `+`. Module values carry their file's bindings
  (`ImportedModule.operators`).
- *Overloading.* Idris 2's type-directed choice among alternatives, without classes. Idris prunes the
  alternatives by the target's head and then elaborates each and keeps those that succeed
  (`TTImp.Elab.Ambiguity`); here the candidates are compared by the heads of their types only: results
  against the expected type, then, if several remain, the first explicit domain against the type of the
  left operand (the right one if the left one is a literal), which is inferred once and passed on as
  the argument. Each operand is elaborated exactly once, so nested operators are linear and nothing is
  backtracked or undone. An unknown head (an unsolved type, a stuck type-level application) fits every
  candidate; a type variable of the context is rigid and fits only a generic domain. Several fit:
  E0932; none fits and no built-in meaning applies: E0933, listing the candidates.
- *Built-in meanings.* A fitting binding is preferred; the built-in operators remain the fallback where
  none fits (meta `int` via `std/int`, meta floats and strings). The successor `e + k` on a nat-like
  type comes first, also where `+` is bound. An integer literal next to an operand of unknown type still
  makes it an `int`, and literals alone are integers (`1 + 1 ≡ 2` is about `int`): the literal default is
  not changed by bindings. Object code never applies bindings; `≡` there is E0933.
- *Patterns.* `p op q` is a constructor pattern if `op` denotes a constructor of the expected type (the
  infix constructors of Agda and Haskell); a binding to a function is not a pattern (E0915, naming the
  function), since clause heads stay constructor patterns (D11). `std/nat`'s `plus` is a function, so
  `N + M` is not a pattern; `N + k` stays the successor pattern.
- *`std/int`.* It binds `+ - * /` to `iplus`, `iminus`, `itimes`, `idiv`, the functions the built-in
  operators apply anyway, so that the editor shows them at the operator and the two `+` are told apart
  by types.
- *Printing.* Types and goals still print in prefix form (`eq {nat} (plus 0 n) n`); printing bound
  functions as operators is left open, since printing does not depend on the scope of a file and every
  stored output that shows `plus` or `eq` would change. The arithmetic of `std/int` already prints as
  operators.
- *Tooling.* The operator's position refers to the function: hover shows it with its type, go to
  definition goes to it, and the annotation table of the web editor lists operators. The TextMate
  grammar and the playground colour `≡` and `==` as operators. The inlay hint of the implicit type
  argument of `eq` is shown after `≡` (`≡{nat}`), as after any applied name.
- *Codes.* E0932 (ambiguous operator), E0933 (no binding of the operator fits); E0701 for an invalid
  binding.
- **L13 — P2b review (lead).** Accepted the agent's deviation `^` = level 6 left (object-level string concat; L6's "8 right" would make one symbol parse differently per stage). Accepted "literals alone default to int" as pre-existing behaviour, NOT changed in P2b; FLAG FOR DESIGNER: Lean defaults numerals to `Nat` (default_instance OfNat Nat), so `0 + 16 ≡ 16` would be about nat there; changing Hugin's default is a separate language decision. Error codes: P2b E0932–E0933, P5 starts at E0934.

## P5 (agent)
### P5a (feat/proofs-p5-semantics)
1. Mutual positivity: blocks = SCC of "constructor of F mentions G", recomputed at each constructor declaration; all members strictly positive in all block constructors (Agda Positivity, Lean 4/Rocq mutual). Closes a real consistency hole (mkA : (b -> empty) -> a, mkB : a -> b proved empty). E0913 at the closing constructor. No `mutual` keyword.
2. Index unification on object code: quotes decomposed, spliced vars solved, object constants injective/disjoint, literals and base types disjoint, cycles; arithmetic/persist-vs-literal postponed (agrees with syntactic conversion).
3. Constructor applications checked against the expected type first (result type unified before args, undone on failure; only if result independent of explicit args): Agda checkConstructorApplication, Lean 4 propagateExpectedType. Needed for fire/ppos and 11.3.
4. No `sub`: nested facts are extra heads (T_R subfacts commute with valuation, facts.md); subfactOf would need code inspection (D13).
5. instAtom returns `pat r (option (list value))` (relation outside the option), fire/ppos adapted: refutes other relations despite stuck head arithmetic.
6. Terms cv/cc/capp/carith/cneg; variables as `member`; comparisons ccmp + holdsCmp family; pcmp C Ps.
7. intOf : ⇑int -> int trusted primitive; add64/sub64/mul64/div64/neg64; floats, string concat uninterpreted.
8. No new error codes.
- **L14 — P5a review (lead).** Accepted: (a) mutual positivity per SCC (fixes a pre-existing inconsistency: `mkA : (b -> empty) -> a.` / `mkB : a -> b.` proved `empty`); (b) no `sub` — nested facts as extra heads (agent's §15 rationale; FLAG FOR DESIGNER as a deviation from §7.2); (c) `intOf` is a `%builtin`, so it shows up under `%assumptions`/`--safe` like other trusted primitives.
- **L15 — P7a started in parallel with P5b.** P7a needs only P5a's `program`/values (merged as e8ef07b); P5b is library proofs over `derives`. Running them concurrently shortens the critical path P5→P7a→P7b. Conflict control: P7a puts its library in a separate file where reasonable; error codes P5 E0934–E0939, P7a E0940+.
### P5b (feat/proofs-p5b-holds)
1. holds = certifying naive evaluation (facts carry derivations; unchecked candidate matching + checked body with proofs); soundness = fromSome + monotone from the empty db; holds takes no db; derivable n p : decider.
2. `same`/sameTrue/apart/decEq extended to closed canonical object code (syntactic, agrees with index unification); quoted patterns keep atomKey.
3. monotone (db) and grow (program extension); model as single-constructor family isModel; least, derivesModel, leastModel (record of both directions; iff is Type₀-only).
4. Expected-type propagation generalised from constructors to all meta constants with family-application results (Lean propagateExpectedType); needed by 11.2 as written.
5. MemoKeys: Pi/Lam/Lift/RecTy read back once per value object (keys never closed, never used); functions below arity stable. p5_holds 22s → 4s; hits/misses unchanged. No benchmark run (improvement).
6. 11.3 premRev via foldl accumulator; complete direction not included.
- **L16 — P5b review (lead).** Accepted: `holds` as a certifying evaluator (sound, incomplete — never true for underivable facts); expected-type-first extended from constructors to all meta constants with family results (Lean 4 `elabAppArgs` / Agda bidirectional checking; rolled back on failure); `same` decides canonical closed object code (syntactic, consistent with D13's syntactic conversion of object code). OPEN, to track: §11.3 converse (`complete`) untested; `holds` incompleteness for variables bound only in comparisons/constructor terms; verbose hand-written derivations until P7b.

## P7a (agent)
### P7a-1 (955d613) code bridge; P7a-2 (f0b442c) programOf — branch feat/proofs-p7a-quote
1. Module `std/quote`: quote/unquote/quoteF/unquoteF/symOf as %builtin trusted primitives (core/CodeBridge.scala); ctors found by name from declared types (as qatom). Separate from std/semantics (P5b-safe).
2. Missing syntax forms: tas, tascribe (type as `⇑type`, like quoted's index; types not data, Q5), tproj, twith + update/uset, fas — one ctor per ObjForm (Lean.Expr style). Ascription not a quoted pattern (E0917); lambdas/records stay E0917. std/directives fvars + std/reflect openT/openF extended.
3. quote structural, positions dropped, stuck as a whole on any non-canonical subterm (eq. 2); literal arithmetic already computed at build time (quote ⟨1+2⟩ = tint 3); n-ary And/Or left-nested.
4. Canonical names: hygiene `X#k` renamed by first occurrence, one counter (X#0, Y#1) — locally nameless canonical form (Charguéraud 2012). unquote(quote c) exact for terms/neutral c; up to this renaming for formulas with hygiene vars (conversion compares names).
5. unquote untyped (typed at staging, as reflection); arithmetic rebuilt via the evaluator; >64-bit ints persisted (E0930 at staging); fagg var named V#b<depth>.
6. Conversion rule unquote(quote c)=c in the primitive's reduction on a stuck quote (like $⟨t⟩=t); no unifier change.
7. D12 realised as PROVED lemmas quoteUnquote/quoteUnquoteF (refl) on the image of quote; unrestricted postulate would be inconsistent (qterm (tarith 1 2) ↦ ⟨3⟩). Deviation from "trusted lemma", in the safe direction. FLAG.
8. Insertion only with std/quote loaded (found via module value, as std/eq for match): unquote at `quoted A`→`⇑B` (A≤B) and for open data in object code (closed data still reflected at elaboration); quote only in term holes, quoteF in formula holes (symmetric extension).
9. symOf : {R : ⇑type} -> ⇑R -> sym, identity on constant code.
10. programOf: contextual special form (like P3's `in`; Lean quote / Agda quoteTerm are syntax). Body read with functor applied to fresh variables (no instance created; D10), data built over the body environment and applied to args → computes under substitution. Instances via recorded ModuleInstance env (=recorded origin). ModuleBody records context names/types.
11. Bare functor `programOf f` = [x̄] programOf (f x̄) : graph -> program (deviation from §1 `tcP : program`; closed program needs code for abstract g.node). FLAG.
12. own i = relations/structs/constructors of the body in source order; arg l = field path, qualified by param name only with several env vars; ext s otherwise; vars by first occurrence (heads first); index from 1; label from @n.
13. Var types: object typing's solution, else column type (wildcards, formula-function vars); else E0942.
14. input = inputOf (in std/quote, so std/quote loads std/semantics): arg/ext and own relations without rules (EDB, Abiteboul–Hull–Vianu); strata = Tarjan SCCs, deps first (P6 refines).
15. Heads = head + constructor terms preorder (P5a no-sub); body `(r t̄ as X)` = atom + ccmp ceq X ⟨fact⟩, X of fact type.
16. E0940 std/quote not loaded; E0941 not a module (incl. `here`); E0942 outside positive fragment / member constructor terms (generative, no code) / untypable var.
17. `programOf here` DEFERRED: file object rules are elaborated after all meta declarations; needs a new phase + moving dependents + cycle rejection. E0941 with a note.
18. Proof A (sameFacts tc/tc2) checked over programOf in tests/run/p7a_program.hgn; implicit g must be passed ({g := G}) since programOf (tc g) doesn't determine g by unification — P7b generalisation.
- **L17 — P7a review (lead).** One PR (#203) with two reviewable commits instead of two PRs (agent could not report mid-run). Accepted: D12 converse round trip PROVED for quote-produced data instead of trusted (general statement is false: `tarith 1 2` unquotes to `3`) — FLAG FOR DESIGNER (design said "conversion rule"; only the `unquote (quote c) ≡ c` direction is definitional). Bare functor `programOf f : graph -> program` (not `program`) — FLAG FOR DESIGNER. `programOf here` deferred (needs elaboration phase after object rules). Pre-existing bug found (meta definition named like a rule label `@n` lands in its module's component) → filed as an issue.
- **L18 — P7a CI fixes.** Pre-existing coverage blow-up (value-class probes enumerated numeral intervals one by one; literal 2^63−1 vs `M + 1` ⇒ 2^63 probes) fixed on the P7a branch: intervals > 20 numerals become one class `Q + a` (Q < b − a); ≤ 20 keep listing numerals so existing messages are unchanged. Corpus timeouts addressed in the compiler (SplitProblem.solve substitutes only what mentions the solved variable), never by raising suite timeouts. `std/quote` no longer loads `std/semantics` (2.5 s elaboration); `programOf` needs both, E0940 says so.
- **L19 — P7b and P6 in parallel after P7a merged (73492ea).** Plan order was P7b → P6; they touch different layers (P7b: notation/elaboration + small library additions; P6: `std/semantics` stratified semantics), so running them concurrently is safe with conflict control: P7b E0945–E0949, P6 E0950+; both additive in `std/semantics`. Both get a per-golden time budget (~4 s) because the whole-corpus CI suites have a 30 s limit and `std/semantics` alone elaborates in ~2.5 s.

## P6 (agent)
### P6 (one commit, negation + aggregates together) — branch feat/proofs-p6-negation
1. `derives`/`premises` UNCHANGED (positive fragment, monotone; P7b's ⊢ unaffected). New mutual pair `nderives`/`npremises` (stratum derivations) = derives + `nneg`/`nagg`, whose premises read the db parameter `d` (completed lower strata), never derivations → strictly positive, P5a per-block check accepts unchanged; no stratum/size index. Perfect model = Type-valued recursion over strata (§7.2): `perfect p d = layers p p.strata (inputs p d)`, `layers p (s::ss) m = layers p ss (nderives (layer p s) m)`. Prior art: Apt–Blair–Walker / Przymusinski 1988 iterated fixpoint; Benzaken–Contejean–Dumbrava DatalogCert (strata in order, negation against lower interpretation); Tantow et al.'s checker = positive proof trees, Hugin's export reads negation in the Gelfond–Lifschitz reduct of the computed model (= perfect model for stratified programs) — same "negation reads a fixed db" idea.
2. `layer p s` = rules with ANY head in s (nested-fact rules also belong to the constructor's stratum, as the compiler adds them, ref object/facts); every relation is input of a layer, so all lower facts (incl. early nested facts) are `ngiven`; start db `inputs p d` = d restricted to p's input relations.
3. Name `cnot` (not §7.2's `cneg`, which is P5a's integer negation term). Locals first: `cnot us (a : catom (append us ts))`, `eappend`; `absent` = ∀ local values, `notIn` (defined and not a fact; undefined atom ⇒ negation fails, ref object/arithmetic "formula with undefined operation does not hold").
4. Aggregates: `cagg us o x t bs`; witness `aggHolds` = record {all, sound, complete, once (distinct), value} over `sat d` (body read entirely in d). Record-valued FUNCTION, not a family → nested aggregates raise no positivity question (structural recursion). `aggOf` on meta ints, one range check (order-independent, partial sums irrelevant); undefined term or min/max of nothing ⇒ none. count counts valuations; programOf reads count's term as constant 1. sum/min/max int-only (E0942 otherwise).
5. SPLIT: stratified semantics in new module `std/strata` (flat name like other std modules). Measured `%use "std/semantics".` elaboration (min of 6, --stats): base 2191 ms; all-in-one 2567 ms (+376); split: std/semantics 2192 ms, std/strata 2558 ms total. cnot/cagg must stay in std/semantics (families closed per file); added clauses holdsIn=empty, fromHolds, search=[], checkBody=none ⇒ such rules never fire in derives/holds.
6. programOf: locals = literal's vars not bound outside negations/aggregates (by atom, comparison, aggregate result: canonical-order binders, ref object/aggregates "grouping variables"), in rule-var order (named vars, then wildcards); not rule vars; same-named locals in two aggregates OK. Negated atoms and all atoms of aggregate bodies are negative edges; negative edge inside an SCC ⇒ E0950 (compiler stratifies modules only at instantiation, E0601; programOf reads uninstantiated functors).
7. programOf now rejects atoms of relations with a bound column (E0942): best-value semantics not modelled; previously only arithmetic on such a column happened to be rejected (silent mis-modelling risk otherwise).
8. `holds` NOT extended: certified negation/aggregates need completeness of lower strata = certified model check (P8b `closed`, §7.6); its basis `nmodel`/`nleast`/`nderivesModel`/`nleastModel` provided in std/strata. holds stays sound.
9. Monotonicity: derives monotone (db, program); nderives monotone in program (`ngrow`), not in db; per-stratum least model (`nleastModel`); `perfect` not monotone in input facts — proved counterexample (tests/run/p6_negation.hgn `notMonotone`). OPEN: `perfect p d a ↔ derives p d a` for negation-free programs not proved (needs a strata-order lemma).
10. Codes: E0950 (module programOf cannot stratify). E0942 no longer covers negation/int aggregates; e0942 neg test keeps its purpose with disjunction instead of negation, plus min-over-strings and bound-column cases.
- **L20 — P6 review (lead).** Accepted: separate `nderives`/`npremises` in new `std/strata` (keeps `derives` positive/monotone and `std/semantics` load time unchanged); `cnot` instead of design's `cneg` (name clash with integer negation); `holds` for stratified programs deferred to P8b (needs certified completeness of lower strata = P8b's `closed`). OPEN: `perfect ↔ derives` for negation-free programs not yet proved.

## P7b (agent)

1. Syntax: `⊢`/`|-` one token, level between `->` and `|`/`≡`, non-assoc; `[e]` directly after the turnstile; atom = application. Tree `Judgment`, elaborated to `derives (programOf P) e (atom ρ [v t̄])`, no core rule (Abella `{L |- A}`, Iris `P ⊢ Q`, Lean `notation`).
2. Rule names lex as `name.digits` (Select with digits) only directly after a name (Isabelle `tc.intros(1)`).
3. The notation needs only std/semantics (not std/quote, not the name `programOf`); E0945 otherwise.
4. Program kind from the head's declared type: functor alone → generalised; application/module → programOf; `program` value → as is (relations by its `relations` names, argument types inferred). Functor applications are never evaluated for this (generativity, D10).
5. Atom resolution = programOf's reading: own members by name in source order, parameter relations by path with programOf's label rule, other names in the judgment's scope as `ext s` (a symbol is the relation; Abella resolves atoms in the spec signature). Arguments checked against column types at the application's arguments.
6. Generalisation: `{d : db}` first, then alone-functors' params by name/type in order, then free uppercase vars; same-name params merged if types unify (E0946 else); decl params / names in scope not rebound; only in declaration types and parameter types (Agda `variable`, Lean auto-bound) — elsewhere E0946/E0947.
7. Programs of bodies stay folded in normal forms (Readback) and index-unification solutions; their applications unify arguments first, solving metas (Lean lazy delta: same head → args first). Removes P7a's `{g := G}` (p7a_program simplified). May pick a less general solution (not injective), never unsound.
8. Rule names = pattern synonyms computed from the program value (Agda), not generated constructors; `r.k` = crule head/index (first head). Multi-head rules named by the first head only (deviation from 7.3 "a name for each", which would contradict crule.index). Labels name rules only where the name is otherwise unbound (never shadow).
9. Patterns: `fire {xs := econs X…} (there^j here) (ppos refl p … pnil) here`, comparisons `pcmp _`; rule vars as implicit-binder pattern vars (in scope unless a pattern var or an outer/left rule var has the name). Fixed latent bug: explicit pattern vars now always shadow implicit binders. Chapter 1's `{X := w}` must be `{X := W}`.
10. Expressions: check goal, member, vars (metas or `{X := e}`), head, premises, comparisons last by evaluation `fromSome (decideCmp …) tt` (E0948 if not true). `given I` (1 arg) = notation with `tt` from `so true`, E0949 for false; 2 args = constructor.
11. Coverage: below `given`/`fire` of a known program, Π includes fire's member/head positions and their `there` chains → derivations split into the program's rules; no absurd clauses for other relations (design's "coverage over rule-name cases"; Agda needs absurd clauses, Lean `contradiction`); one-level emptiness unchanged elsewhere.
12. Splits: goal relation's rule names, premises named by relation initials (fresh per case, split var name reusable), `given` iff input. Printing: `derives (programOf (f ā)) d (atom ρ vs)` → `f ā ⊢ r t̄`, `[d]` omitted for `d`; functor name recorded at first functor use. OPEN (cosmetic): hole contexts print binder types unfolded (`g : {node : type, …}`, `d : gatom -> Type`).
13. `decide : {d}{p}{a} -> (n : nat) -> so (holds n p a) -> derives p d a` appended to std/semantics; name clash with std/decide's `decide` kept (chapter 1 writes `decide 3 tt`); p5_holds and the reference holds-example use the generic one via `%import "std/decide"`.
14. `here ⊢` unavailable (P7a deferred `programOf here`): decide demo uses a module with facts in its body (`trip ⊢ path berlin rome`); input relations contribute nothing to `holds`.
15. Adequacy statement in reference std/semantics "Adequacy" (positive fragment, trusted, d defined by what arg/ext/input-own denote for m).
16. Codes E0945 (atom/library), E0946 (generalisation), E0947 (database), E0948 (rule names, incl. undecided comparison), E0949 (given).
- **L21 — P8b started in parallel with P7b** after P6 merged (4b79384). P8b depends on `derives`/`std/strata` and P8a's export, not on P7b's notation. Error codes E0955+. P8b also owns `closed` (certified completeness per stratum), which unblocks stratified `holds` (deferred from P6).
- **L22 — P7b review (lead).** Accepted the notation design (folded program functions unified by arguments first, Lean lazy delta; rule names as pattern synonyms, Agda). FLAG FOR DESIGNER: (a) `decide` in `std/semantics` shares its name with `std/decide`'s generic `decide` (kept because chapter 1 writes `decide 3 tt`; generic one now reached via `%import "std/decide"`) — candidate for P2b-style type-directed overloading of names or a rename; (b) multi-head rules named only by first head (§7.3 said one name per head); (c) proof B writes `{X := W}` not `{X := w}`. OPEN: notation not wired to P6's `nderives`; golden wall times ~4 s (library load dominates — `std/semantics` elaboration speed is the lever if CI corpus timeouts reappear).
- **L23 — P9a ("honest types") implemented ahead of P9 design approval.** Reason: it only turns two silently wrong behaviours on the merged base into errors — (1) applied relations in meta types elaborate to an uninhabited `⇑(r t̄)` (E0960), (2) `P ⊢ r t̄` over programs with negation/aggregates is read in positive `derives` and can contradict the run, e.g. `never : m ⊢ ok berlin -> empty` (E0961). No new language feature; reversible. P9b–P9e wait for designer approval of #207. RE-JUDGE: designer may prefer to hold even P9a until approval.

## P9a (agent)
- E0960 is raised where the elaborator lifts an object type into a meta type: the coercion `rel -> Type` (checking against a universe, also below the η-expansion of a Π, which gives the "not a type family" message), `liftType` (mixed meta arrows, declared types with parameters), the explicit `⇑A`, formula-function parameters and signature field types. It fires when the lifted type is the fact type of an application with at least one explicit argument (partial applications included, since they are equally empty). Unapplied and nullary relations keep their fact-type meaning; object-level positions are untouched (E0909 there, as before). File relations (`road x y`) are E0960 too.
- E0960 is a `TypeProblem` (help names `P ⊢ r t̄`, generic; no owner lookup, that is P9b). E0961 is a `JudgmentProblem`, detected on the evaluated program value (a rule body with `cnot`/`cagg`), so it covers modules, functor applications, functors written alone and program values whose rules evaluate; a program value that does not evaluate is not checked. The error's message is the design's text; the note names the rule's head relation.
- Chapter 1 of proofs.md: `{X := W}` (and its uses `T W R`, the hand check, Bridges), and also `firstHop (path.2 {Y := W} E P) = W` in 1.x, the same lowercase pattern variable. The L22c history line (2190) left as it is.

## P8b (agent)

**P8b (certified runs).**

- *Which program is certified.* The program the engine ran, reified by the driver from the rules the proof
  export records (one rule per head, the export's fragment), not `programOf`: `programOf here` does not
  exist (P7a), and 7.4 places `--certify` on link 3 (staged program → output), with link 2 (reification)
  trusted as it is for `programOf`. The certificate carries its program, as Tantow et al.'s JSON does.
  The driver reifies an *untyped* program (`uprogram`: variables by position, constants by value) and
  `typeProgram`, meta code, types it into a `program` (member proofs, the types of comparisons), so the
  trusted reifier builds only data with no implicit arguments to get wrong.
- *Certificate.* The derived facts in the export's settle order (premises first), each with the positions
  of its positive premises among the facts before it, stratum by stratum for a stratified program: P8a's
  proof DAG with back references. The checker finds the rule and the valuation itself, by matching the
  rules against the premises, so the certificate names neither (and is independent of variable order).
- *Certifying checker.* For each fact the checker builds its `derives` (`nderives`) derivation, as P5b's
  `holds` does, so soundness is the result type (`level m`: facts with proofs in `m`); no soundness proof
  of a search (McConnell et al.'s certifying algorithms; Lean's `decide`).
- *`closed`, the model check.* For each rule, the candidates of its body (positive atoms matched against
  all facts) are checked: complete, and either the heads are facts or the body is refuted (a failing
  comparison, or a negated atom matched by a fact below, found by a guessed and then verified witness).
  `candsOk` proves the candidates complete (every valuation whose positive atoms are facts agrees with one),
  so the facts are a `model` (`nmodel`) and `least` (`nleast`) gives completeness: Tantow et al.'s
  one-round model check, with its soundness proved instead of trusted. Matching treats a term other than
  a variable or a constant as no constraint, which keeps the proof simple; such terms are outside the
  fragment anyway.
- *Reflexivity without a primitive.* Completeness of matching needs a value to compare equal to itself;
  `same` is stuck on open code and a postulate `same a a = true` is false for float NaN literals. The
  checker instead checks `isSome (eqGatom a a)` once per accepted fact (`selfG`) and the proof derives
  what it needs from it: proof by evaluation of the concrete data, no new trusted primitive.
- *Negation.* A negated atom in a derivation is decided by the facts of the strata below, made complete by
  their model check (P6's `nleast`); `absentIn` proves `absent` from the completeness of matching against
  them (the atom must have variables and constants only, so it is defined). Aggregates are outside the
  fragment (P8a's), so `checkStrata` rejects them; their witnesses would need the same machinery per body.
- *Positive and stratified checkers.* A program without negation is checked against `derives` and its
  least model (`checkPositive`); one with negation against `perfect` (`checkStrata`), stratum by stratum
  with the engine's components as strata, each stratum program computed once (a term `layer p s` in an
  implicit argument would filter the rules at every derivation node: a run of 56 facts went from 47 s to 9 s).
- *`holds` for stratified programs.* `perfectFacts n p ins` evaluates each stratum by `n` naive rounds
  (negations decided by the facts below) followed by its model check; `decidePerfect` then decides
  membership both ways, with `perfectHolds`/`perfectRefutes` deciders. A new function in `std/certify`
  rather than an extension of `holds`, which takes no database and stays the positive fragment.
- *Library and loading.* `std/certify` loads `std/semantics` and `std/strata`; the program loads it
  (E0955 otherwise), like `programOf` needs its libraries (E0940): a checker is something the program
  chooses to trust, and the elaboration (about 1 s on top of `std/strata`) is paid only by programs that
  ask for it. The verdict line goes to stderr; a rejected or uncertifiable run is an error (exit 1).
- *Codes.* E0955 (no `std/certify`), E0956 (outside the certified fragment: a rule the export leaves out,
  a value that is a fact or an infinity, a type the semantics does not model), E0957 (the checker rejects
  the run). Order comparisons are interpreted on integers only (as `std/semantics`), so a comparison of
  strings is E0957, the explanation's example.
- *Memo keys.* The memo of closed applications read back every argument at every reduction; the checker's
  arguments are closures and growing proofs. A key with a function, a type or an open value is never
  closed, so it is now not read back at all (`MemoKeys`: `neverClosed`, `Unused`), which changes no memo
  hit (MemoKeysSuite, LongListsSuite). The checker's own searches stop at the first hit and build a
  membership once (`findFrom`), instead of nesting `optMap there`.
- *Measured limits* (once, `benchlock`, loaded machine, before the last two optimisations): transitive
  closure of a chain of 20 nodes, 209 facts, 12.7 s with `--certify` against 4.8 s without; larger chains
  and the stratified variant failed. After them (single diagnostic runs): 209 facts 3.6 s CPU in the
  checker, 819 facts about 60 s, 56 stratified facts 1.5 s. The cost is quadratic (premise lookup by
  position in a list, the model check's naive join); a certified run is an audit mode for small and
  medium runs. Goldens: p8b_certify 1.5 s, p8b_strata 1.5 s in the test JVM.
- **L24 — P8b review (lead).** Accepted: certify the program the engine ran (Tantow et al.), checker soundness by result type, `closed` proved sound ⇒ least/perfect model; no new trusted primitive (reflexivity checked per fact because NaN). Stratified `holds` delivered (`decidePerfect`). OPEN: checker quadratic (≈60 s for 819 facts) — documented as audit mode for small/medium runs; follow-up candidate: indexed premise lookup and a hash join in `closed`. Aggregates not certifiable (E0956).
- (P9a, CI hang) MutationFuzzSuite timeout on a mc_formula_members mutant was pre-existing (hangs on 1db9441 too). Cause: `closeOver` (Lifting) put a let for every earlier definition into a lifted function's type; `finishMemberFormulas` releases the withheld formula definitions before `formulaCycles`, whose `define` evaluates the cycle members' types, so a let of a cyclic member (`pong`, declared before `ping`'s declaration when `ping`'s rules come first) unfolded forever, on the heap (the machine's frames), never polling cancellation. Fix: closeOver drops unused lets, as closeTerm does. No cancellation poll added to definition unfolding: the poll invariant ("only clause functions recurse") holds again once definitions are acyclic, and the evaluator hot path stays unchanged. Regression golden: tests/neg/mc_formula_cycle_order.
- **L25 — pre-existing hang fixed on the P9a branch.** `closeOver` (Lifting.scala) wrapped a lifted member's type in lets for every preceding definition, so the E0105 cycle check evaluated a released formula cycle (`ping`↔`pong`) without end → heap exhaustion; the evaluator never polled cancellation because only clause steps poll. Fix: drop unused lets, as `closeTerm` already does (cf. #178). FOLLOW-UP CANDIDATE (not done, needs a benchmark): poll cancellation on definition unfolding as defence in depth.
- **L26 — process failure (lead): #209's CI hung ~2.5 h before I noticed; the user had to point it out.** Cause of the miss: I treated `check_suite.completed` events for superseded commits as noise and never checked the elapsed time of the live run. Rule from now on: if a PR's test jobs run longer than 2× their normal ~7 min, cancel the run and diagnose immediately. Diagnosis: only 5/98 suites reported within 2 min, then nothing — deadlock-like; P8b's tests had never completed on CI (both earlier runs superseded). One-off exception to "no local suites" granted to the P8b agent to reproduce once with jstack.
- **L27 — DESIGNER DECISION (approved in conversation): no blessed names in judgments.** (1) A functor written alone before `⊢` is no longer generalised by its parameters' declared names; write the application, `tc G ⊢ …`, with `G` an ordinary free uppercase variable (existing implicit-argument generalisation). (2) An omitted database: in a declaration's type, all judgments without `[…]` share ONE anonymous implicit binder (no name, cannot be referenced or matched); elsewhere it is a metavariable solved by unification, else E0947 asking for `⊢[e]`. To name it: `⊢[D]` with `D` a free uppercase variable. The identifier `d` has no special meaning. Implemented as correction batch P7c before P9b; #207 revised accordingly (drops `f.r` for bare functors and the functor-parameter generalisation pre-pass).
- **L28 — consequence of L27 (lead):** parameter relations in judgments are written through the user's argument (`tc G ⊢ G.edge x y`, `{x : G.node}`), never through the functor's internal binder name `g` (which is not in scope in the statement). Added to P7c. #207 rev 3 (eda5b4d) flagged this; its examples change only `g` → `G`.
- **L29 — DESIGNER APPROVED #207 (level 3.5), condensed decision list:** (1) A + C3; (2) η form for unapplied relations; (3) C3 scope = module/functor bodies AND the file itself, own relations (+ parameter relations in functor bodies) unqualified, lemmas inherited by instances; (4) the phase P9f (program-dependent members after object items, E0962 cycles, delivers `programOf here`), priority over A; (5) prefix `⊢ r t̄` / `⊢[e] r t̄` with the ambient program; (6) stratum-local `nderives` reading for negation/aggregates, replacing E0961 (P9c, after an addendum on negated premises in patterns); (7) multi-head rule names per (rule, head); (8) `decide` clash resolved by type (P2b head rule over E0109); (9) member access without instance + `%opaque` in bodies. Plan: P7c (running) → P9b, P9c, P9d after P7c (same notation code); P9e and P9f start now; P9g after P9f (+P9b).

## P7c (agent)

Branch fix/proofs-p7c-explicit-generalisation, commit c8571b9.
- Functor alone before ⊢: E0946 ("the functor `tc` is written alone before `⊢`…", help "write `tc G ⊢ …`", parameter names capitalised). Checked in a pre-pass over the declaration's type, so it beats `{x : G.node}` failing first.
- `tc G`: G bound by the ordinary free-uppercase rule. Because projections are not postponed, `{x : G.node}` before the judgment needs G's type early: after bindImplicits, `judgmentArgumentTypes` unifies the types of variables written as arguments of a global functor (by position, up to the first non-variable) with the parameter types, and `⊢[D]` variables with `db`. Failures are left to the judgment. Side effect: G's type displays unfolded (`{ node : type, … }`, not `graph`) — cosmetic, open.
- Anonymous database: binder name `#db` (not lexable; hidden by Holes/MetaTooling filters, as `#` names are), origin `BinderOrigin.Database(opSpans)`: only the judgments without [e] that lie in the declaration's type and its parameter types use it (matched by turnstile span), so bodies/clauses/lambdas/local types never pick it up. Printed `{_ : db}` in binders, `_` elsewhere, and omitted in a judgment. E0926's list of implicit names omits it ("takes no implicit argument by name" when it is the only one).
- Elsewhere: fresh meta "the database of a judgment"; unsolved → E0947 (checked before the item's other unsolved metas).
- Follow-up (parameter relations through the argument): `tc G ⊢ G.edge x y`; arguments written as variables are mapped to the body's environment variables by position (through the env that applying the functor builds); label as programOf reads it (`edge` for one parameter, `g.edge` for several). `g.edge` → E0945. Non-variable argument names no relation: `tc {…edge = road} ⊢ road x y` is `ext road`, NOT `arg "edge"` (does not agree with programOf's reading; documented, statements about the parameter need a variable argument). Module values (instances) name no parameter relations. Printer and E0948/E0949 messages show `arg l` through the argument.
- Proof B: theorems use `placed D A` / `coarse A ⊢[D]` with `A.alpha`; `placed` keeps `⊢[d]`.
- proofs-level35.md untouched; proofs.md batch table (P7b row) left historical.
- **L30 — P7c open point (lead):** in `tc { node = city, edge = road } ⊢ road x y`, `road` would silently be `ext road` while the program reads that relation as `arg "edge"` — a different statement. Following P9a's precedent (silently different meaning → error), it is E0945 when an atom resolves to a relation that appears syntactically as (a field of) a non-variable argument of the judgment's functor application; help points to `tc G ⊢ G.edge` or an instance. RE-JUDGE: designer may prefer resolving it to `arg "edge"` instead (needs name resolution by argument value).
- (L30, lead) Relation written as a non-variable argument's value (whole argument or record-literal field, compared by resolved constant, syntactically): naming it in the atom is E0945 (ArgumentRelation), help "`road` is the argument for the parameter relation `edge`; state it through a variable argument (`tc G ⊢ G.edge …`) or through an instance". Also fixed: a global written as an argument (`hops road`) no longer counts as a variable argument (only names in local scope do). Other file relations stay `ext s`.

## P9e (agent)
- Codes: reused E0932/E0933 (meaning carries over); retitled "ambiguous operator or opened name" / "no candidate of the operator or opened name fits". No new codes. New problem cases OperatorProblem.AmbiguousName / NoNameFits (with "opens `n`" labels on the %use items).
- Rule (Overloading.resolveOpened): candidates = all opened globals when ≥2 and all meta constants. Step 1: drop candidates taking fewer than k explicit args (type ends in a known non-function head; unknown head or ⇑ counts as possibly applicable), then compare result head after k args with expected head. Step 2 (several left, k≥1): infer first positional arg once at S1 (+ insert), compare with first explicit domain; the chosen constant is applied to the already-elaborated arg (coe), rest via inferPositionalApp. Arity filtering also applies without an expected type.
- Chosen by result: the head is rewritten to SymRef(id) and elaborated normally (P5 expected-type propagation still applies). recordUse on the name span -> hover/definition show the chosen constant (tested in OperatorBindingsSuite via Ide).
- "Object constant" = stage S0 global, or an opened alias field (Definition = projection) whose type is ⇑A or U0, i.e. a module instance's relation/constructor/type. These keep E0109 (otherwise `%use (tc g1). %use (tc g2).` became E0932).
- Directives `%d` keep E0109 (Directives.application unchanged); documented in directives.md.
- m_use_ambiguous (two meta `double : int -> int`) would now be E0932; changed it to meta-vs-object (new tests/neg/lib/twice_rel.hgn, removed unused twice_b.hgn) to keep E0109 coverage. E0109 doc and modules.md E0109 example moved from metric/imperial `factor` (meta, now E0932) to two `tc` instances' `path`.
- p5_holds: back to plain `%use "std/semantics".` (std/decide stays `(so, decide)`); output unchanged.
- reference std/semantics: the holds example now opens std/decide's decide directly instead of `checker.decide`.
- **L31 — scheduling after P7c merged (bccf709):** P9b (coercion) and P9d (multi-head names) start in parallel — different parts of the notation code; P9c (negation reading, also rule names over nfire) waits for P9d to avoid a three-way conflict in rule-name code. P9f continues; #211 (P9e) re-runs CI on the new base. Error codes: P9b/P9d may take E0963+ (E0962 reserved for P9f).

## P9f (agent)

Branch `feat/proofs-p9f-phase`, commit f6a8130 (on 468f937). Design: proofs-level35.md §4.3.6, decision 20.

- **Prior art / framing.** Lean 4, Isabelle and Agda order "definition before proof" by the text. Hugin's items are unordered (dependency order, #91 `ElabOrder`), so the phase is a dependency-driven split: a declaration about its scope's program depends on all of the scope's rules. Program-independent items keep exactly today's order.
- **Classification (`ProgramPhase`), syntactic, before elaboration.** Direct: `programOf here` or a `Judgment` whose program is `here`, outside nested module bodies (their `here` is theirs). Closure over `ElabOrder.mentions` (the #91 names), units by owner name (signature+clauses, formula function+rules); `%opaque`/`%export` naming one go along. Not deferrable: file `%use`, `%infix`, subtyping edges; body object constants → if they need a dependent name, E0962. A deferred file object constant is reported (E0962) after the phase. Mentions ignore binders (as #91), so a needless deferral is possible but harmless unless a rule uses it.
- **Performance.** Gate = a bounded char scan of each declaration's (and body item's) text for the word `here` (`where`/`there` excluded). No tree walk, no extra pass for ordinary files. Items that use `here` as a name (std/semantics member proofs) get one tree walk each.
- **Ordering.** File: phase-1 declarations (with deferred names in `declaredHere`, `functionNames`, `opaque`, and a `programDependent` map name → chain), object items + module-wide expansion, program, `Items.elabDeferred` (forked state). Body: object constants + other members, object items, program from a temporary `ModuleBody` with the *same body id* (so `programOf tc2` from outside reuses the generated program constant), deferred members appended as fields; object items' terms shifted past them (`shiftItem`).
- **`here` value.** File: own = its relations/structs/constructors in source order (nullary object constants like `berlin` count, consistent with P7a's numbering of bodies), by declared names (qualified library names fixed), rules = assembled rules after module-wide directives; generated definition `programOf here`, displayed `here ⊢ …` (an imported file's by its qualifier). Body: P7b's folded constant applied to the context vars, displayed with the enclosing definition's name. Build failures (no std/semantics, E0942/E0950) are reported at each use of `here`.
- **E0962** at the use: hook in `Names.unresolved` and directive lookup (channel `programDependent`, a per-name read in the footprint/DeclarationsSummary); note gives the chain; `here` itself in an object item = E0962 without chain. E0941 no longer covers `here` (problem's `here` flag removed).
- **Judgments untouched** (P7c area): `here ⊢` reaches `programOfTree` via `judgmentProgram`. Name resolution touched only by one line in `unresolved` (P9e area) plus one in `Directives.unknownDirective`.
- **Incrementality.** Queries: `PhasesOf` (identity equality — trees compare without positions, which made Signatures stale in a first version, caught by IncrementalSuite), `DeclarationsOf` (equality adds deferred *names*), `DeferredOf`, `HereProgramOf` (assembles the object items again, reifies, moves into a fork of the declarations' core recreating family instances; equality = declarations identity + program term + relation ids + var names + instance keys), `ElabDeferred`, `ElabProgram` assembles into a fork of the deferred core and lints all names. ProgramPhaseSuite: proof edit → signatures 0, elabItem 0, elabDeferred 1; comment before a rule → 0/0/0; rule edit → 0/1/1; broken proof equals from-scratch. Body phase stays inside its declaration's item (no new invalidation).
- **Limits/open.** Files with deferred declarations assemble object items twice. A file rule whose head is another module's relation makes `here` unreifiable (E0942 at the use). W0003 can flag a formula function whose only uses are E0962 (annotated in the neg golden). P9b's coerced own relations (P9g) must add a direct form to `ProgramPhase.usesHere`.

## P9d (agent)
- Names per (rule, head): `r.k` = k-th head atom of `r` in program order, then `crule.heads` order (written heads, each followed by its nested facts). `crule.index` unchanged; a single-head rule after a rule with two heads of its relation becomes `r.3` etc.
- Nested facts are `ext` of the file's constructor (bodies cannot declare constructors with code), so `r.k` also names heads of `ext` relations by the constant's name (`circle.1`); own relation wins on a name clash. `arg` heads get no name (none exist).
- Label code: E0948 (the design's code), new problem `LabelHeads` ("which head?", help lists `r.k`). Unknown goal relation: label = first head.
- Rule patterns pass a premise's relation from the rule's body as a hint for nested premise patterns, so labels pick the right head there and a mismatching `r.k` premise is E0948 instead of a later type error.
- Splits list every (rule, head) of the goal's relation, by label when it names that head alone.
- Updated the E0948 UnknownRule note ("one name for each head of `r`"), so e0948_rule_names.check changed by one line.
- Docs: std/semantics.md Rule names (+ run example `flip`), meta/coverage.md Derivations, docs/errors/E0948.md, proofs.md §15 "P9d".

## P9b (agent)
- Hooks: `Bidirectional.infer` (Apply, typePosition, meta stage) and `checkAt` (meta checks, before rule names) → `JudgmentCoercion`; builds P7b's `Judgment` tree and calls `inferJudgmentOf` (new: optional pre-resolved program, for opened names). Prior art: Lean `CoeSort`, Rocq Sortclass coercions, Hugin's own `⇑` insertion.
- Owner found syntactically: module/instance path (global value + record projections → `moduleOf`), global functor applied to explicit args (applied to fresh probes, no instance), opened name = global relation or opened alias (type `⇑τ` checked before unfolding) → `instanceOwning` (scan of moduleInstances). Locals/body-declared names/functor alone: none.
- Coercion active only with std/semantics loaded; owned relation without it → E0960 with "load std/semantics" help. No new code (E0963 unused).
- η form = surface lambda `[x̄] r x̄` (fresh names vs scope and head names) checked against the family; n ≥ 1 explicit binders ending in a meta universe.
- Pre-pass `coercionCandidates` (only with std/semantics): declared type, arrow parts, binder types, record field types, args of a global meta constant whose explicit param is a universe or a family (owned unapplied relation, or lambda body). Head span joins BinderOrigin.Database; written program joins judgmentArgumentTypes. Record field types added beyond §2.5's list (they are binder types).
- E0960 helps: unowned → `P ⊢ r t̄` (η: `[x̄] P ⊢ r x̄`); explicit ⇑ → "without the ⇑"; no library → load std/semantics. Note text lists owned forms. E0945/E0961 from a coerced atom get a note "`fast.path x` is read as the judgment `fast ⊢ path x`".
- Printing: hover "elaborated" of a judgment-typed term shows `P ⊢ r t̄` (from the value); a module without environment displays by name (`trip ⊢`, was `programOf trip ⊢`).
- OPEN: (1) `linkSym _ _ L` (design §1.3) fails to unify — also with the turnstile and plain Π over nodes, so pre-existing (wildcard metas typed `⇑?G.node` vs atom unification); goldens write the nodes. (2) instance of a functor still prints `programOf fast { node = ⟨city⟩, … } ⊢` unless a `tc G ⊢` judgment named the functor first (pre-existing). (3) programOf of a body reading a member instance's relation (`v.vertex` in rtc) is E0942 (P7a), so `weak.reach` can't be judged; only `weak.v.vertex` tested.
- (P9b, CI fix) Two causes. (1) JVM `Impossible: projection .vars of Obj(Wild)`: pre-pass `familyArity` instantiated dependent Π codomains with `Val.Wild` (std/certify `(c : crule) -> env c.vars -> Type`); now fresh locals + catch Impossible, shape filter before inspecting args; regression tests/pos/p9b_dependent_family. (2) Browser OOM: `MetaTooling.elaborated` evaluated EVERY typed term (to detect judgments for hovers) → p4_decide's proofs ran in JS; now only terms headed by `derives` are evaluated. Also: owner lookup unfolds only record-typed globals / functors returning records; coercion fully off without std/semantics (dropped the "load std/semantics" E0960 help). js-golden: all passed, 54 s.

## P9c (agent)

- Addendum (proofs-level35 §6.3.1): stratum-local rule names write one premise per atom, negated atom and aggregate, in body order; comparisons not written. Patterns bind the negated premise as `absent …` and the aggregate witness as is (no view patterns; Agda pattern synonyms). Expressions: a negated atom without local variables takes a refutation `P ⊢ q t̄ -> empty`, wrapped by the elaborator with `absentOf k j tt` (or the raw premise); with locals, the raw premise (prior art: Lean/Rocq `¬ q x` premises over earlier-defined q; DatalogCert).
- `upTo p k d = [a] layers p (take k p.strata) (inputs p d) a` exactly as designed (a lambda, so peeled `ngiven` premises convert by η); `judged p k d` names the judgment; elaboration emits `nderives (layer p sₖ) (upTo p k d) a` with sₖ a literal.
- k = last stratum whose layer has a rule with a head of r; 0 for relations without rules.
- Adequacy proved in full, no postulate: `adequate k (tt : so (lastIn p r p.strata k)) : iff (perfect p d a) (judged p k d a)`, for any k with no later rule head of r (decided by `freeAfter`/`diffRef` + `diffSound` via `apart`). Also `lower`/`raise`/`absentOf`/`refuted` between strata.
- `given` at a stratum: input relation → ngiven chain to the input facts (`{fst = tt, snd = I}`; a pattern binds the record); relation with rules → lifts a lower/equal stratum's judgment (expression), pattern at own stratum reaches input facts so `I.fst` refutes.
- New E0948 sub-case "fires in a later stratum" (problem LaterStratum); no new codes. E0961 kept only for a judgment over a negation/aggregate program in a file without std/strata (message/explanation/registry updated).
- `decide` NOT connected to the notation: judgment database arbitrary, perfectHolds decides only at `memOf ins`, perfect not monotone. Added `judgedHolds` in std/certify (perfectHolds + adequate) for `judged p k (memOf ins) a`; tested in p8b_certify.
- Display: `layer`/`upTo` of std/strata stay folded in normal forms (GlobalEntry.judgmentPart), printer shows `P ⊢[d] r t̄` for nderives/layer/upTo and `judged`. Open: peeled premise types print as nderives chains.
- Cost: std/strata +174 lines; elaboration 2992 → 3081 ms (min of 6, --stats), kept as one module.

## P9g (agent)

- C3 is P9b's coercion with `Owner.Here`: in a scope's program-dependent declarations (`ProgramOf.ambient`), an own relation written alone, or a body context variable's relation `x.r`, becomes the Judgment tree `here ⊢ r t̄` (prefix form). Elsewhere (non-deferred declarations, a file relation inside a body, under `⇑`) it stays E0960 (note text updated).
- Unqualified ownership is limited to relations and structs (decl type ends in `rel`, or a struct decl), not constructors, matching E0960's scope.
- ProgramPhase trigger `usesOwn`: syntactic type positions (declared/param/binder types, arrows, field types, arguments of any application in a type position as a superset, def value when declared `Type`), plus an unapplied own relation as such an argument (η form). Skips quotes, `⇑`, rules, judgment atoms, inner bodies. Over-approximation only defers. Body parameter relations decided from the context variable's record type (`relationField`, fresh variables, no evaluation of values).
- Prefix `⊢[e] r t̄`: a `Judgment` with program `Ident("here")` of empty span (`TreeOps.isPrefixJudgment`), printed `⊢ r t̄`; `⊢` starts an expression; the `here` text gate also accepts `⊢`/`|-`.
- Member access without instance: only for a functor whose definition term is syntactically `[x̄] {…}` (read from the Tm, never evaluated). `ModuleBody.free` (new field) = greatest set of meta members whose resolved local names (tracked per member via Names.resolve) avoid object members, transitively. Read = member term in the body's env at the args, needed members let-bound, others `Tm.Fresh`. Non-free meta member at args mentioning variables: E0107 (`NeedsInstance`, note + help); closed args keep today's instance.
- `%opaque` in bodies: directives taken out of the body's object items; lifted member functions made opaque via `opaqueLifted`/`opaqueHere`; member definitions lifted to opaque globals; non-member name E0701.
- Pre-pass for the anonymous db also reads a member's type at an application head (body-local functions such as `placed`).
- No ambiguity negative test: own names resolve as everywhere (a member shadows opened names); nothing ambiguous arises.

### L32 — P9g regression: `(f G).m` with a variable argument (user caught it)
The P9g agent made reading a member without an instance replace the old path, instead of extending it. As a result
`pathOf G = (tc3 G).relation.` became E0107, but it compiles and runs on base 5985321 (verified: `out berlin paris`).
It was also documented as intended behaviour in docs/errors/E0107.md. Decision: the instance-free reading is
an extension only, and no program accepted on base may be rejected. The E0107 section is removed and a regression test
is added (tests/run/p9g_functor_member). Process gap: no existing test covered a functor member with a variable
argument in a function body. Any new rejection of previously accepted code goes to the user before it ships.
- CORRECTION (coordinator): the first version made `(f ā).m` an E0107 for a meta member that mentions an object constant when `ā` has variables. That rejected programs base accepts (`pathOf G = (tc3 G).relation`, used by `%emit (pathOf {…})`, which creates an instance per call with closed arguments). Cause: no existing test covered `(f G).m` with a variable `G` in a function body. Fixed: the instance-free reading is an extension only (free members); every other `(f ā).m` keeps base's reading exactly; E0107 section removed; regression test run/p9g_functor_member (plus the variant through a definition with a record parameter).
- η-form trigger restricted after js-golden caught `link : quoted node -> quoted node -> quoted edge` (tf_typed_atoms) being deferred: an unapplied own relation counts only as an argument where a function of the scope (syntactically) or, for bodies, a global/enclosing function (by its elaborated type) takes a family `… -> Type` at that position.

### L33: P9g, a lemma access no longer creates an instance (user confirmed)
`(f closedArgs).m`, where m mentions no object constant, no longer creates the fresh unnamed instance that base created.
What can be observed: that instance's facts are not printed, its rules do not run, the per-instance checks (termination,
completeness) are skipped for those arguments, and `programOf here` no longer contains its relations. Nothing could refer
to that instance, because instances are generative. The user confirmed this is fine.
