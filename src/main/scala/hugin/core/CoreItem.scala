package hugin.core

import hugin.util.Span

/** What one item of a module elaborated to. */
enum CoreItem:
  case GlobalItem(id: Int)

  /** An object rule: its variables (with their object types, possibly unsolved metas) bind in the heads
   *  and the body. */
  case RuleItem(name: Option[Name], vars: List[(Name, Tm)], heads: List[Tm], body: Option[Tm], span: Span)
  case QueryItem(vars: List[(Name, Tm)], body: Tm, span: Span)
