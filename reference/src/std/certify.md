# `std/certify`

The module `std/certify` is the checker of *certified runs*. With the option `--certify`, `hugin run`
reifies the program it ran, its input facts and its output with a derivation of every fact, and
evaluates this checker on them. An accepted run reports exactly the least model of a positive program,
or the perfect model of a stratified one ([`std/strata`](strata.md)), from its input facts: every fact it
prints is derived, and every derived fact is printed. The guarantee does not rest on the engine, only on
the reification and on the checker, whose correctness is proved in this module against `derives` of
[`std/semantics`](semantics.md) and `nderives` and `perfect` of [`std/strata`](strata.md). The module
also decides membership in the perfect model by evaluation, both ways. A program that is run with
`--certify` writes `%use "std/certify".`; it loads `std/semantics` and `std/strata` itself.

| declaration | meaning |
|---|---|
| `uterm`, `uatom`, `ulit`, `urule`, `uprogram` | programs as `--certify` reifies them: rules over untyped terms |
| `typeProgram : uprogram -> option program.` | the `program` of `std/semantics` that a reified program denotes |
| `cfact : Type.`, `cf : gatom -> list nat -> cfact.` | a derived fact of a certificate, with the positions of its premises |
| `failure : Type.` | why a certificate is rejected: `badProgram`, `badShape`, `badInput a`, `badFact a`, `notClosed k` |
| `pfact : db -> Type.` | a fact with its proof in a database |
| `level : db -> Type.` | a list of facts with their proofs that holds all facts of the database |
| `checkPositive : (p : program) -> (ins : list gatom) -> list cfact -> either failure (level (derives p (memOf ins))).` | the checker of a positive program |
| `checkStrata : (p : program) -> (ins : list gatom) -> list (list cfact) -> either failure (level (perfect p (memOf ins))).` | the checker of a stratified program, stratum by stratum |
| `certifyPositive`, `certifyStrata`, `verdict`, `accepted`, `rejected` | the checkers on a reified program, as `--certify` calls them |
| `memOf : list gatom -> db.` | the facts of a list as a database |
| `agree`, `cands`, `candsOk` | candidate valuations of a body, and their completeness |
| `rulesIn` | the model check of a list of rules |
| `perfectFacts : nat -> (p : program) -> (ins : list gatom) -> either failure (level (perfect p (memOf ins))).` | the perfect model by evaluation |
| `decidePerfect : nat -> (p : program) -> (ins : list gatom) -> (a : gatom) -> option (dec (perfect p (memOf ins) a)).` | membership in the perfect model, decided |
| `perfectHolds`, `perfectRefutes` | deciders for `decide` of [`std/decide`](decide.md): a fact is in the perfect model, or it is not |

## Certified runs

```text
$ hugin run --certify --facts roads.facts reach.hgn
reach berlin paris.
...
certified: the 11 facts of the run are the least model of the program (3 rules, 3 strata) from its 3 input facts
```

The verdict is printed on the error output. A run that cannot be certified is an error: the program does
not load `std/certify` ([E0955](../errors/E0955.md)), a rule or a value of the run is outside the
certified fragment ([E0956](../errors/E0956.md)), or the checker rejects the run
([E0957](../errors/E0957.md)).

The *certified fragment* is that of the [proof export](../object/io.md#proof-export): rules whose atoms
have variables and constants as arguments, with negated atoms and comparisons, without aggregates,
disjunctions, `as` and bound columns. The values of the facts are literals and constants. The run is
reified as follows.

- The *program* is the rules that the engine evaluated, one rule for each head of each rule, as the proof
  export exports them. Its relations are those of the rules and of the facts, `own i` in the order of the
  compiler's relations; the input relations are the relations declared `%input` or `%open`, and the
  strata are the engine's components. A rule's variables are numbered heads first, in order of
  occurrence, the local variables of a negated atom before the rule's, as
  [`programOf`](quote.md#programs-as-values) numbers them, and each is typed by the column of its first
  occurrence in a positive atom, as the values of the facts are typed by their columns.
- The *input facts* `ins` are the facts of the input relations that no rule derives; the database is
  `memOf ins`.
- The *certificate* lists the derived facts in an order in which every fact comes after its premises, the
  order in which the proof export settles its proofs, each with the positions of the facts of its positive
  premises among the facts before it. A stratified program's certificate has one list per stratum.

`typeProgram` types the reified program: a variable is its position, a constant its value, and the two
sides of a comparison must have the same type. The checkers are certifying ([McConnell et al.
2011](../notation.md#references)): for each fact of the certificate they look up its premises, find the
valuations of a rule's body by matching it against them, check the body with proofs, and build the fact's
derivation (`fire` of `derives`, or `nfire` of `nderives`), as [`holds`](semantics.md#proof-by-evaluation)
builds the derivations of the facts it finds. So every accepted fact carries its derivation, and the
soundness of the checker is its type.

## The model check

After the facts, the checker shows that they are closed under the rules: for each rule, every valuation
whose positive atoms are facts of the list and whose body holds derives facts of the list. The
valuations are the *candidates* of the body: its positive atoms matched against the facts, one after
another (`cands`). `candsOk` proves that every valuation whose positive atoms are facts agrees with a
candidate, so it suffices to check the candidates: each must be complete, and either its heads are facts
of the list, or its body is refuted (a comparison that fails, or a negated atom matched by a fact of the
strata below). The list is then a model (`model`, `nmodel`), and by `least` (`nleast`) every derived fact
is in it. For a stratified program, the check of each stratum makes its facts complete, so the negations
of the strata above are decided by the facts below: a negated atom holds if no fact of the strata below
matches it, which the completeness of matching proves.

Matching compares values with `eqValue`, which decides closed code. The completeness proof needs that a
value compares equal to itself; the checker checks it once for every fact it accepts (`selfG`), so no
assumption about the comparison is needed.

## Deciding the perfect model

`perfectFacts n p ins` computes the perfect model by `n` rounds of naive evaluation in each stratum, with
the negations decided by the facts below, followed by the model check of the stratum. Its facts are then
all of the perfect model, so `decidePerfect` decides membership both ways: `yes` with the derivation of a
fact found, `no` with the refutation that the model check gives for a fact not found. This is the
`holds` of stratified programs.

```hugin,ignore
romeSink : perfect sinks (memOf edges) (s (<rome>)) = (perfectHolds 2 sinks edges).sound (s (<rome>)) tt.
parisNot : perfect sinks (memOf edges) (s (<paris>)) -> empty = (perfectRefutes 2 sinks edges).sound (s (<paris>)) tt.
```

## Limits

The checker runs in the meta evaluator after the run. Checking the derivations costs, per fact, the
lookup of its premises (linear in the number of facts before it) and the matching of the rules against
them; the model check is a naive join of each rule's body over all facts. Both grow quadratically with the
number of facts: the transitive closure of a chain of 20 nodes (209 facts) takes a few seconds to check,
one of 40 nodes (819 facts) about a minute. A certified run is therefore a mode for tests and audits of
small and medium runs, not the default.

> **Rationale.** Checking each run instead of verifying the engine follows the certificates of
> [Tantow et al. 2025](../notation.md#references): proof trees give soundness, and a one-round model
> check gives completeness. The checker is written and proved in Hugin, against the semantics that
> theorems about programs use, as translation validation checks each run of a compiler instead of the
> compiler (CompCert's validated passes). A verified engine, as in [Benzaken et al.
> 2017](../notation.md#references), would make every run slow; a certified run costs only when asked
> for.
