# Hugin

[![CI](https://github.com/k0uks1/hugin/actions/workflows/ci.yml/badge.svg)](https://github.com/k0uks1/hugin/actions/workflows/ci.yml)
[![Site](https://github.com/k0uks1/hugin/actions/workflows/reference.yml/badge.svg)](https://k0uks1.github.io/hugin/)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Hugin is a typed Datalog with first-class facts at the object level and a total, dependently typed meta
level that computes object programs at compile time. This repository holds its language reference and
its reference implementation, written in Scala 3.

```
%use "std/reflect".
%use "std/graph".

person : type.
ann : person. bob : person. cid : person. dan : person.

knows : person -> person -> rel.
knows ann bob.
knows bob cid.
knows dan ann.

(* a directive is a meta function; this one returns rules *)
symmetric : (r : ⇑(A -> A -> rel)) -> list item.
symmetric R = '( R Y X :- R X Y. ).
%symmetric knows.

(* `tc` is a functor from std/graph: transitive closure of a graph *)
reach = tc { node = person, edge = knows }.

?- reach.path cid P, P <> cid.
```

```
$ hugin run people.hgn
?- reach.path cid P, P <> cid.
P = ann.
P = bob.
P = dan.
```

## Key ideas

- Hugin has two levels. The object level is Datalog∃!, evaluated bottom-up to a least fixed point. The
  meta level is a two-level type theory with dependent types, inductive families, functions defined by
  clauses, modules and functors. Meta code runs during compilation and produces object rules.
- Constructors build facts. Every constructor term built in a rule head is a fact, whose identity is
  determined by its content, and the constructor is also the relation of its facts. Bodies only match
  existing facts.
- Every accepted program terminates. Recursion that builds terms or computes numbers must pass a
  size-change check; there is no limit on evaluation rounds. Meta functions are checked for coverage and
  termination as well.
- The last column of a relation can be a bound column, `min τ` or `max τ`, as in Limit Datalog. The
  relation keeps the best value per key, so recursion such as shortest paths terminates.
- Directives are meta functions. `%input`, `%output` and `%demand` are defined in the prelude, written in
  Hugin over a reflected representation of object syntax. Programs can define their own.

## Status

Hugin is a research language. This is its reference implementation: it follows the language reference
closely and favours clear diagnostics over speed. The evaluator is a semi-naive interpreter; an efficient
Datalog engine is out of scope. The language changes without regard for compatibility.

## Getting started

Requirements: JDK 17 or later and [sbt](https://www.scala-sbt.org/) 1.10.

```
git clone https://github.com/k0uks1/hugin && cd hugin
sbt stage                                    # builds the launcher target/universal/stage/bin/hugin
bin/hugin run examples/graphs.hgn            # compile and evaluate a program
bin/hugin check examples/typechecker.hgn     # compile only and report diagnostics
bin/hugin repl examples/graphs.hgn           # an interactive session
bin/hugin explain E0603                      # explain a diagnostic code
```

`bin/hugin` stages the launcher on first use. `hugin lsp` is a language server for any LSP client;
[`editors/vscode`](editors/vscode) contains a VS Code extension with syntax highlighting. `hugin --help`
lists all commands and options.

## Documentation

- [The website](https://k0uks1.github.io/hugin/), with a [playground](https://k0uks1.github.io/hugin/play/)
  that compiles and runs programs in the browser.
- [The Hugin language reference](https://k0uks1.github.io/hugin/reference/): the definition of the
  language, with checked examples.
- [Error index](https://k0uks1.github.io/hugin/reference/errors/index.html): every diagnostic code with
  an explanation, also printed by `hugin explain <code>`.
- [`examples/`](examples): small programs (graphs, records, lists, formula functions, a type checker).
- [`CONTRIBUTING.md`](CONTRIBUTING.md): the developer guide (architecture, tests, tooling).
- [`docs/`](docs): design notes and the record of the redesign. They are historical; the reference is
  the specification.

## Background

Hugin builds on the following work. The reference lists all cited works in
[Notation](https://k0uks1.github.io/hugin/reference/notation.html#references).

- T. Gilray, A. Sahebolamri, Y. Sun, S. Kunapaneni, S. Kumar, K. Micinski. *Datalog with First-Class
  Facts.* PVLDB 18(3), 2024. [arXiv:2411.14330](https://arxiv.org/abs/2411.14330). The object level is
  based on its language DL∃!.
- A. Kovács. *Staged Compilation with Two-Level Type Theory.* ICFP 2022.
  [doi:10.1145/3547641](https://doi.org/10.1145/3547641). The design of the meta level and its
  elaborator.
- M. Kaminski, B. Cuenca Grau, E. V. Kostylev, B. Motik, I. Horrocks. *Foundations of Declarative Data
  Analysis Using Limit Datalog Programs.* IJCAI 2017. [arXiv:1705.06927](https://arxiv.org/abs/1705.06927).
  Bound columns.
- C. S. Lee, N. D. Jones, A. M. Ben-Amram. *The Size-Change Principle for Program Termination.* POPL 2001.
  The termination checks.
- *Hugin: A Two-Level Typed Datalog with First-Class Facts. Formal Language Definition*, draft revision 7.
  The definition the implementation started from; the reference supersedes it.

## Contributing

Bug reports and pull requests are welcome. [`CONTRIBUTING.md`](CONTRIBUTING.md) describes how to build and
test the implementation and how the compiler is organised.

## License

Hugin is licensed under the [Apache License, Version 2.0](LICENSE).
