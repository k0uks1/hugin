package hugin.obj

/** Probe semantics: values versus facts. A constructed term is a *value* (interned, with an identity);
 *  it is a *fact* only if it is asserted. Values built in ordinary rule heads are asserted together with
 *  the values nested in them (subfact closure), so created facts trigger rules. Values built as the inputs
 *  of moded calls are *probes*: interned, so that the called relation can inspect them, but not asserted,
 *  so that `%mode` never adds facts to relations other than the moded relation and its demand relations.
 *  Nested patterns match values structurally; only top-level atoms read facts. */
object Probes:
  /** The head columns of `r` whose constructed values are probes: all columns of a demand rule (it builds
   *  the inputs of a call), and in a rule of a moded relation guarded by the demand of mode `m`, the inputs
   *  of `m` (it rebuilds the inputs it was called with). */
  def columns(r: Rule): Set[Int] =
    r.heads.headOption match
      case Some(Term.App(RelRef.Sym(h), _)) =>
        h.kind match
          case RelKind.Demand(_, _) => h.cols.indices.toSet
          case _ =>
            r.body
              .collectFirst { case Formula.Atom(RelRef.Sym(d), _, _) if d.kind.isInstanceOf[RelKind.Demand] => d.kind }
              .collect { case RelKind.Demand(`h`, m) => m.inputs.zipWithIndex.collect { case (true, i) => i }.toSet }
              .getOrElse(Set.empty)
      case _ => Set.empty
