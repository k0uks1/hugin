# Introduction

This is the reference for **Hugin**, a two-level typed Datalog: an object level, Datalog∃!, whose
programs are evaluated to a least fixed point, and a total, dependently typed meta level (two-level type
theory) that computes object-level programs at compile time.

The reference is **normative**. It defines the language that the reference implementation accepts: when
the implementation and this reference disagree, one of them has a bug. Every Hugin example in it is
compiled, and run where its output is shown, in the continuous integration of the implementation.

The design notes in the repository (`docs/NOTES.md`, `docs/REDESIGN.md` and the other files under
`docs/`) are **historical**: they record how and why the language came to be as it is, including
alternatives that were rejected. They are not a specification; where they differ from this reference,
this reference applies.

The [error index](errors/index.md) lists every diagnostic code of the compiler with an explanation and
examples. It is the same text that `hugin explain <code>` prints.

> **Status.** The chapters are being written (redesign Phase D). A chapter that only states its scope
> is not yet normative.
