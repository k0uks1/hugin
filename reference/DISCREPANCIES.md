# Discrepancies found while writing the reference

This file records, for the language designer, where the implementation (the code at the head of
`feat/d-reference`) and the design documents (`docs/REDESIGN.md`, `docs/NOTES.md`, `README.md`) disagree,
and gaps where the implementation accepts something the documents do not mention. The reference
describes the implementation. Each entry says what the reference says now.

## Implementation versus design documents

1. **Relation facts have identities.** `docs/REDESIGN.md` §3.2 says "Relations `r : τ̄ -> rel` have facts
   without a result identity". In the implementation every relation (and struct) is also a fact type:
   `(edge 1 _ as E)` binds the identity of an `edge` fact, a column of type `edge` holds such facts, and
   a head `seen (edge 5 6)` asserts the fact `edge 5 6`. The reference ("Facts and identity", "Facts as
   values") describes the implementation.

   *Decided (#74): keep the implementation.* REDESIGN §3.2 is annotated.

2. **No `bool` values at the object level.** REDESIGN §3.2 lists `bool` among the literal types. The
   lexer has no boolean literals and the object level has no `bool` type; `bool` is a meta type of the
   prelude (`true`, `false`). The reference lists `int`, `float`, `string`.

   *Decided (#74): keep the implementation* (truth is the presence of a fact). REDESIGN §3.2 is annotated.

3. **No `mod` operator.** REDESIGN §5.1 lists `+ - * / mod`. The implementation has `+ - * /` and the
   string concatenation `^`, and no `mod`. The reference describes these.

   *Decided (#74): keep the implementation; `mod` is dropped.* REDESIGN §5.1 is annotated.

4. **`%complete` is not a directive.** REDESIGN §7.2 lists `%complete r.` among the primitive
   directives. It is accepted only as a requirement inside a signature; elsewhere it is E0004. The
   reference says so (Directives, Modules).

   *Decided (#74): keep the implementation.* REDESIGN §7.2 is annotated.

5. **`fib` of §8.2 terminates by descent, not by guarded induction.** REDESIGN §8.2 (and the inline
   comment `(* (B) on n *)` in `tests/run/rd_fib.hgn`) say `fib` is accepted by (B). The check tries (A)
   first, and `--explain-termination` reports `{fib}: terminates by descent along derivations (A)`, read
   upwards (`N` is larger than `A`, bounded by the finite source `need`). The header comment of the test
   already says so; only the inline comment is out of date.

   *Resolved:* the inline comment now says (A), and REDESIGN §8.2 is annotated.

6. **Quoted patterns cannot bind a variable's name.** REDESIGN §6.9 says that `$X` in a variable
   position binds the variable's name as a value of a type `Var`. There is no `Var` type: object
   variables are `tvar string` data, a plain uppercase variable in a quoted pattern matches any object
   variable, and `$X` in a term position binds the whole term. NOTES (C1) records the decision; the
   reference describes it.

   *Resolved:* REDESIGN §6.9 is annotated (no `Var`; variables are `tvar string`).

7. **Named patterns in quoted syntax.** `docs/errors/E0917.md` says that named patterns have no
   reflective representation (E0917). Since C3 they are quoted as positional atoms
   (`(p X :- item { name = X, .. })` reifies to `p X :- item X _`, and runs; since #76 written
   `'( p X :- item { name = X, .. } )`). The reference (Reflection, "Quotes") describes the
   implementation; the explanation of E0917 should drop "named patterns" from its list.

   *Resolved:* E0917's explanation no longer lists named patterns.

8. **Module-wide directives see the whole file.** `docs/NOTES.md` (C2) and the doc comment of
   `ModuleDirectives` say that a module-wide directive "replaces all data so far". The expansion
   (`ModuleDirectives.expandModule`) gives it every rule, query and `$e.` item of the file, also those
   after it in the source, plus the items of additive and module-wide directives before it; only the
   items of additive directives after it are not seen. (This is what lets `%demand r` stand before the
   rules of `r`.) The reference describes the implementation.

   *Resolved:* NOTES (C2) and the doc comment of `ModuleDirectives` now describe the expansion as above.

9. **Base types are built-in names, not prelude declarations.** `CONTRIBUTING.md` (line 199, from the
   former README) says the prelude declares the base types (`int : type = %builtin int.`). The prelude
   does not; `int`, `float` and `string` are built-in names that are in scope when the prelude is
   included (`core/elab/Names.scala`, `builtinTypes`). `docs/LIBRARIES.md` already says so.

   *Resolved:* CONTRIBUTING.md now says that the base types are built-in names.

10. **REDESIGN §6.9 `Term`/`Formula`/`List`, §7.1 `Decl -> Decl`, §7.4 `Modes r`.** The implementation
    uses lowercase names (`term`, `formula`, `seq`), standalone local directives of type `decl` (not
    `Decl -> Decl`), and `modes (labels r)`. NOTES records these decisions; listed here only because
    REDESIGN is not annotated at those places.

    *Resolved:* REDESIGN §6.9, §7.1 and §7.4 are annotated.

## Gaps and possible bugs found while writing examples

11. **Implicit binders in `f (x : A) : B = e.`** NOTES (B1) says free uppercase variables of a
    declaration are implicit binders, and they are for `x : A.`, `x : A = e.` and `f (x : A) = e.`
    (no result type). But `ident (x : A) : A = x.` reports E0101 "unresolved name `A`" (also
    `apply (f : A -> A) (a : A) : A = f a.`). The reference (Functions, "Implicit arguments") states only
    the forms that work.

    *Resolved:* the free uppercase variables of such a header are implicit binders; the reference
    (Functions, "Implicit arguments") states the form.

12. **Duplicate column labels are accepted.** `r : (a : int) -> (a : int) -> rel.` compiles without a
    diagnostic; a named pattern `r { a = … }` then refers to the first column. E0307 covers duplicate
    labels of record values only. The reference does not mention duplicate column labels.

    *Resolved:* duplicate column labels are E0307 (Object declarations, "Columns and labels").

13. **Aggregates count wildcards as local variables.** `count { I | sale S I _ }` counts sales, not
    distinct items: the wildcard is a local variable of the aggregate. This follows Definition 8.4 of
    the definition draft but may surprise; the reference states it explicitly (Aggregates).

    *Decided (#74): keep the implementation* (the standard Datalog semantics, as in Soufflé); the
    reference (Aggregates) has a Note.

14. **Constructors into a struct type.** `s : type = { x : int }. c : int -> s.` is accepted and `c 1`
    is a value of type `s`, although a constructor's result is meant to be an open type (REDESIGN §3.2,
    `ObjectDecls.objectDecl`, which rejects other object types such as refinements with E0103). The
    struct `s` in a type position is its fact type, which the classification does not catch. The
    reference says only that a refinement is rejected.

    *Resolved:* a constructor into the fact type of a struct or relation is E0103, like a refinement
    (Object declarations, "Constructors").

15. **Reflection by expected type (#76).** REDESIGN §6.9 reifies unmarked object syntax wherever a
    reflective type is expected, and writes rules as data `(h :- b)` (`(h :-)` without body). This made
    syntactic categories ambiguous and collided with staging (`$[$(flip (edge a b))].` was elaborated as
    a staged list). Reflection now has explicit quotes `'( … )` whose category is the expected type's;
    holes exist only inside them, and `(h :- b)` is a syntax error.

    *Decided (#76):* REDESIGN §6.9 is annotated; the reference (Reflection, "Quotes") defines the quotes,
    and the arguments of directives are quoted implicitly (Directives, "Resolution and arguments").
