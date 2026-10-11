# Consistency

The meta level is a dependently typed language whose types can state properties and whose functions can
prove them. A proof is only worth something if the logic is *consistent*: if no closed term has an empty
type. This chapter lists the rules that keep the meta level consistent, the one construct that can
break it on purpose, the postulate, and how a program shows what it rests on.

## Syntax

```text
Assumptions ::= "%assumptions" NAME "."
```

## What makes the meta level consistent

Every meta function is total, and every type is predicative. The rules that guarantee it are defined in
the other chapters of the meta level:

| rule | chapter | error |
|---|---|---|
| universes form a hierarchy; `Type : Type` is rejected | [Universes](universes.md) | [E0904](../errors/E0904.md) |
| a family occurs only strictly positively in its constructors | [Inductive families](families.md#strict-positivity) | [E0913](../errors/E0913.md) |
| the arguments of a constructor live in its family's universe, except the implicit arguments at its [parameters](families.md#parameters) | [Inductive families](families.md#universe-levels) | [E0914](../errors/E0914.md), [E0904](../errors/E0904.md) |
| the clauses of a function cover all its arguments; a function without clauses covers them only if an argument has an empty type | [Coverage](coverage.md#missing-cases) | [E0911](../errors/E0911.md) |
| a recursive function decreases along every cycle of calls; the arguments of a constructor at its family's parameters are not its subterms | [Termination](termination.md) | [E0912](../errors/E0912.md) |
| a typed hole is an error, not an assumption | [Functions](functions.md#typed-holes) | [E0924](../errors/E0924.md) |

A program with an error is not compiled, so a proof that relies on an unchecked part cannot be used.
Index unification has the rule K: two proofs of the same equation of constructor terms are equal, which
is consistent with these rules (uniqueness of identity proofs). Object code cannot be inspected by meta
code (`⇑A` has no eliminator), so the facts that the object level derives never reach the meta logic.

A constructor whose large argument is exempt from predicativity only because an index of its result
determines it, together with recursion on such forced arguments, is inconsistent (Agda's issue 6654).
Hugin exempts only the implicit arguments at a family's parameters, as Lean does, so the combination
does not arise.

## Postulates

A [postulate](functions.md#postulates) `x : A = %postulate.` is a constant without a value: it assumes
that `A` has an element, and nothing checks it. A postulate of a false statement makes the logic
inconsistent: with `empty : Type.` a family without constructors, `boom : empty = %postulate.` proves
anything. A postulate is therefore always written as such. A meta declaration without a value is an
inductive family, a constructor or a function; a function without clauses is an error unless an
argument has an empty type ([E0911](../errors/E0911.md)). The following declaration is rejected.

```hugin,compile_fail,E0911
boom : (A : Type) -> A.
```

The abstract members of a signature and the parameters of a functor are not postulates: they are bound
to values where the signature is ascribed or the functor applied ([Modules](../modules.md)). The
declarations of an imported file are elaborated in that file, with the same rules.

The option `--safe` of `hugin check` and `hugin run`, and the setting `hugin.safe` of the language
server, reject every postulate of the program and of the files it imports
([E0925](../errors/E0925.md)). The standard library has no postulates.

## Assumptions

The *assumptions* of a constant are the postulates and the trusted primitives that it depends on: those
that its type, its value or its clauses mention, and, transitively, those of every constant that they
mention. The *trusted primitives* are code of the compiler that the meta level relies on without a
proof: the primitive operations `x : A = %builtin p.` of the standard library (`same`, `labels`,
`derive`, `derived`, `qatom`), and the functions of [`std/nat`](../std/nat.md#native-arithmetic) that
compute natively, whose native operation is checked against their clauses when the library is
elaborated. The arithmetic of the meta type `int` and the evaluator are part of the language, not
assumptions.

The directive `%assumptions f.` prints the assumptions of the constant `f` in scope when the program is
compiled, as Lean's `#print axioms` and Rocq's `Print Assumptions` do. It is an
item of a file, not of a module body ([E0907](../errors/E0907.md)), and it is an error
([E0101](../errors/E0101.md)) if no `f` is in scope. The option `--print-assumptions f` of `hugin
check` and `hugin run` prints the same for the constant `f` of the program (or else of an imported file);
it may be given several times. Each line names an assumption with its type and says what it is.

```hugin,run
eqn : nat -> nat -> Type.
refl : eqn N N.
plus : nat -> nat -> nat.
plus 0 N = N.
plus (M + 1) N = plus M N + 1.
plusZero : (n : nat) -> eqn (plus n 0) n = %postulate.
lemma : eqn (plus 2 0) 2 = plusZero 2.
proved : eqn (plus 0 2) 2 = refl.
%assumptions lemma.
%assumptions proved.
ok : int -> rel.
ok 1.
```

```output
ok 1.
```

Compiled as `unit.hgn`, the program prints:

```text
note: assumptions of `lemma`:
  plusZero : (n : nat) -> eqn (plus n 0) n  (postulate at unit.hgn:6:1)
note: assumptions of `proved`: none
```

and `hugin check --safe unit.hgn` reports E0925 for `plusZero`. A line for a trusted primitive ends in
`(trusted primitive %builtin same)` with the primitive's name, and a line for a native function of
`std/nat` in `(trusted native operation add)` with the operation's name.

## Trusted base

Hugin has no separate kernel: the elaborator, the evaluator, the coverage and termination checks and the
native arithmetic are trusted, as in Agda. The engine that computes the facts of the object level is
trusted as well.
