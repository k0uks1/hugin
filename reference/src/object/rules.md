# Rules

A *rule* derives facts from facts. It has one or more *heads*, which are atoms, and an optional *body*,
which is a formula. For every valuation of its variables that satisfies the body, the rule derives its
heads. A rule without a body states its heads as facts.

## Syntax

```text
Rule      ::= RULE_NAME? Head ("," Head)* (":-" Formula)? "."
Head      ::= Atom
Atom      ::= QualifiedName Arg*
            | QualifiedName "{" FieldPattern ("," FieldPattern)* "}"
Arg       ::= Term
QualifiedName ::= NAME ("." NAME)*
```

The relation of a head is a relation, struct or constructor in scope, also through a module path such as
`m.path`. A head is parsed above the comparison level: the commas between heads separate heads.

The following program has a rule with two heads: every edge of `link` is an edge in both directions.

```hugin,run
link : int -> int -> rel.
link 1 2.
edge : int -> int -> rel.
edge X Y, edge Y X :- link X Y.
%output edge.
```

```output
edge 1 2.
edge 2 1.
```

## Formulas

```text
Formula   ::= Formula ";" Formula                     (disjunction)
            | Formula "," Formula                     (conjunction)
            | "not" Atom                              (negation)
            | Term CmpOp Term                         (comparison)
            | VAR "=" AggOp "{" Term "|" Formula "}"   (aggregate)
            | Atom
            | "(" Atom "as" VAR ")"
            | "(" Formula ")"
CmpOp     ::= "=" | "<>" | "<" | "<=" | ">" | ">="
```

A *formula* is a condition on the variables of a rule. The forms are:

- An *atom* `r t₁ … tₙ` holds if `r v₁ … vₙ` is a fact, where `vᵢ` matches `tᵢ`. A term in an argument is
  a pattern ([Facts and identity](facts.md#bodies-never-create-facts)). An atom of a formula function is
  replaced by the function's formula ([Staging](../meta/staging.md#formula-functions)).
- A *comparison* compares two terms ([Arithmetic and comparisons](arithmetic.md)). An equation `X = t`
  whose left side is not bound yet binds `X`.
- `φ, ψ` holds if both hold; `φ ; ψ` holds if one of them holds. `,` binds tighter than `;`.
- `not r t̄` holds if no fact matches `r t̄` ([Negation and stratification](negation.md)). It is an error
  ([E0202](../errors/E0202.md)) if `not` is applied to anything but an atom.
- An *aggregate* binds a variable to a count, sum, minimum or maximum ([Aggregates](aggregates.md)).

### Constants as formulas

A constant without arguments, such as `no : flag.` or the constants `true` and `false` of the shared type
`bool` ([`std/reflect`](../std/reflect.md#lists-options-and-booleans)), is a term. Used as a formula, it
is an atom of its constructor: it holds if the constant is a fact. A constant is a fact once a head or an
input file builds it ([Facts and identity](facts.md)), also inside another fact. So the formula does not
test a value. `blocked :- false.` derives `blocked` as soon as any fact contains `false`. The compiler
warns about every such formula ([W0008](../errors/W0008.md), lint `constant_formulas`, on by default).

```hugin,run
check : (id : int) -> (ok : bool) -> rel.
check 1 true. check 2 false.
blocked : rel.
blocked :- false.
failed : int -> rel.
failed I :- check I false.
?- blocked.
?- failed I.
```

```output
?- blocked.
yes.
?- failed I.
I = 2.
```

A rule whose body is false is not written, and a fact is written without a body. The match of a value in
an atom, as `check I false` above, is what tests a boolean column.

## Variables

The variables of a rule are its *object variables*: the uppercase identifiers in its heads and body.
All occurrences of a variable in a rule denote the same value. Each wildcard `_` is a variable of its
own. A variable that occurs only once in a rule constrains nothing; the compiler warns about it
([W0002](../errors/W0002.md), lint `singleton_variables`) unless its name starts with `_`.

A variable that occurs only inside a negation, or only inside an aggregate, is local to it. In `not
parent X _` the wildcard is local, and the formula holds if `X` has no child.

## Range restriction

Rules are evaluated bottom-up, so every variable must get its value from the body. A body *binds* a
variable in these ways:

- a positive atom binds all the variables of its arguments, except those under arithmetic, projections
  and updates, which must be bound already;
- an equation `t = u` binds the variables of `t` if `u` is bound and `t` is a variable or a constructor
  pattern, and symmetrically;
- an aggregate binds its result variable;
- a disjunction binds the variables that every alternative binds.

A comparison other than a binding equation, a negation, the term of an aggregate and arithmetic need
their variables bound. The body is *range-restricted* if its formulas can be ordered so that each formula
finds the variables it needs bound by the formulas before it, and the heads' variables are bound at the
end. The compiler evaluates the body in such an order, the *canonical order*: it picks the leftmost
formula that can be evaluated, repeatedly. It is an error ([E0501](../errors/E0501.md)) if a rule or
query is not range-restricted.

The following rule is rejected, since nothing binds `Y`.

```hugin,compile_fail,E0501
edge : int -> int -> rel.
free : int -> int -> rel.
free X Y :- edge X _.
```

## Semantics

A *valuation* of a rule maps each of its variables to a value. A database *satisfies* a formula under a
valuation as the forms above say. A rule *derives* the facts of its heads, with their nested facts
([Facts and identity](facts.md#constructor-terms-in-heads)), under every valuation whose body is
satisfied. A disjunction in a body is the same as one rule per alternative; a rule with several heads is
the same as one rule per head.

## Named rules

A rule may have a name `@r`. The name is used by [`%derivations`](io.md#derivation-facts) and in
diagnostics. Several rules may have the same name.

## Records

Columns with labels can be addressed by name.

```text
FieldPattern ::= NAME "=" Term | ".."
Projection   ::= VAR "." NAME
Update       ::= "(" VAR "with" "{" NAME "=" Term ("," NAME "=" Term)* "}" ")"
```

A *named pattern* `r { l₁ = t₁, …, lₖ = tₖ }` is the atom of `r` with `tᵢ` in the column labelled `lᵢ`.
It must name every column, or end with `..`, which fills the columns it does not name with wildcards. It
is an error to omit a label without `..` ([E0301](../errors/E0301.md)), to use `..` in a head
([E0302](../errors/E0302.md)) or to name a label the relation does not have
([E0306](../errors/E0306.md)). A record value `{ l = t, … }` as the argument of a struct is the same as a
named pattern.

A *projection* `X.l` is the value in the column labelled `l` of the fact `X`. An *update*
`(X with { l = t })` is the fact like `X` but with `t` in the column `l`; in a head it derives that fact.
Both apply to variables whose type is closed; it is an error ([E0303](../errors/E0303.md)) to apply them
to another term. At a meta position, the same syntax updates a meta record
([Records](../meta/records.md#update)). If the type of `X` is a union, the rule stands for one rule
per member, and every member must have the label ([E0303](../errors/E0303.md),
[E0304](../errors/E0304.md)). The type of `X.l` over a union is the *join* of the column types, their
least common supertype. It is an error ([E0305](../errors/E0305.md)) if they have none.

The following program uses each form over a union of two relations: a named pattern in a body, a
projection in a head and an update in a head.

```hugin,run
name : type = string.
span : type = { file : string, line : int }.
var : (loc : span) -> (name : name) -> rel.
abs : (loc : span) -> (name : name) -> (body : term) -> rel.
term : type = var | abs.
unbound : term -> rel.
unbound (var (span "a.hgn" 3) "x").
unbound (abs (span "a.hgn" 7) "y" (var (span "a.hgn" 8) "y")).
binder : name -> rel.
binder N :- abs { name = N, .. }.
report : span -> rel.
report (E.loc) :- unbound E.
moved : term -> rel.
moved (E with { loc = span "b.hgn" 1 }) :- unbound E.
%output binder. %output report. %output moved.
```

```output
binder "y".
moved (abs (span "b.hgn" 1) "y" (var (span "a.hgn" 8) "y")).
moved (var (span "b.hgn" 1) "x").
report (span "a.hgn" 3).
report (span "a.hgn" 7).
```
