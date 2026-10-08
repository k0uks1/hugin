package hugin.core

import hugin.util.Span

/** What one item of a module elaborated to. Object items are kept as elaborated (with the meta code they
 *  splice); the handover to the object level stages them ([[hugin.core.handover]]). */
enum CoreItem:
  case GlobalItem(id: Int)

  /** An object rule: its variables (with their object types, possibly unsolved metas) bind in the heads
   *  and the body. A `generic` rule has unsolved object types among the implicit arguments of the
   *  families it uses (`len nil 0.`): it is a family of rules, instantiated at every instance of its
   *  head's family ([[handover.Generics]]). */
  case RuleItem(name: Option[Name], vars: List[(Name, Tm)], heads: List[Tm], body: Option[Tm], span: Span, generic: Boolean = false)
  case QueryItem(vars: List[(Name, Tm)], body: Tm, span: Span)

  /** `τ <: a.`: closed object types. */
  case EdgeItem(sub: Tm, sup: Tm, span: Span)

  /** A directive about the relation `target` (closed object code), or `%derivations @r` (no target). */
  case DirectiveItem(directive: CoreDirective, target: Option[Tm], span: Span)

/** The directives of the object level (REDESIGN §7.2); they become `obj.Directive`s. */
enum CoreDirective:
  case Input, Output, Open, Derivations
  case DerivationsRule(rule: Name)
  case Mode(inputs: List[(Boolean, Option[Name], Span)])
  case TerminatesLabel(labels: List[Name])

  /** `%terminates X̄ (r t̄)`: the measure variables and the call pattern, whose variables `vars` bind in
   *  `args`. */
  case TerminatesVar(measure: List[Name], vars: List[(Name, Tm)], args: List[Tm])
  case NameHint(variable: Name)
