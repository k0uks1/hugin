# Termination

> **Scope.** Why every accepted program terminates: descent along derivations, guarded induction, and the errors for programs that cannot be shown to terminate.

*To be written in redesign Phase D.*

A recursive rule that creates new values needs a termination argument; without one the program is rejected
with [E0603](../errors/E0603.md):

```hugin,compile_fail,E0603
nat : int -> rel.
nat 0.
nat M :- nat N, M = N + 1.
```

With a guard the recursion is bounded and the program is accepted:

```hugin
nat : int -> rel.
nat 0.
nat M :- nat N, N < 100, M = N + 1.
```
