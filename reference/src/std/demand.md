# `std/demand`

The module `std/demand` defines the directive `%demand` ([Directives](../directives.md#demand)). Its
[export signature](../modules.md#export-signatures) has one field:

```hugin,ignore
%export { demand : (r : sym) -> modes (labels r) -> module -> module }.
```

`demand` is a module-wide directive written in Hugin with quoted patterns. Its helper functions, the
transformation step by step and the binding analysis of the prefixes of demand rules, are declarations of
the module that its signature leaves out, so they are not fields of `std/demand`. The
[prelude](../prelude.md) opens `demand`, so `%demand` is available in every program.
