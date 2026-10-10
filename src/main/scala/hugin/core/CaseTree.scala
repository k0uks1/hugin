package hugin.core

/** The compiled pattern match of a meta function defined by clauses (reference: meta/clauses).
 *
 *  It works on a growing vector of variables, by level: first the function's arguments (implicit ones
 *  included), then the arguments of each constructor matched so far. A [[CaseTree.Split]] inspects one
 *  variable, which must evaluate to a constructor application, and appends its arguments; a
 *  [[CaseTree.Leaf]] evaluates the right-hand side of a clause, elaborated once in the clause's own
 *  context, at an instance of that context. Impossible constructors (ruled out by index unification)
 *  have no branch. */
enum CaseTree:
  /** Clause `clause` applies: `body` (its right-hand side, shared by all its leaves) lives in the clause's
   *  context, and `subst` gives a term for each variable of that context (in its telescope order) over
   *  the leaf's `size` variables (by de Bruijn index, the last variable innermost): the matching
   *  substitution `σ` from the clause's context to the leaf's case. */
  case Leaf(body: Tm, size: Int, subst: Vector[Tm], clause: Int)
  case Split(level: Int, branches: List[CaseBranch])

  /** A split on a variable of a type with decidable equality but no constructors (the references to
   *  object constants `Sym`, meta literals in quoted patterns): a branch per value the clauses name
   *  (`value` is closed and normal), and `default` for every other value. */
  case SplitAtom(level: Int, branches: List[(Tm, CaseTree)], default: CaseTree)

final case class CaseBranch(ctor: Int, arity: Int, tree: CaseTree)

/** A clause of a function as elaborated, in its own context: the context's variables (in telescope order)
 *  are named `names`, `patterns` are the function's explicit arguments as patterns over them, and `body`
 *  is the right-hand side; an absurd clause (`f ().`) has none. */
final case class ClauseBody(body: Option[Tm], names: Vector[Name], patterns: List[Tm])

/** The case tree of a function and its clauses, as written (for display: `--print-after`, hover). */
final case class FunctionBody(tree: CaseTree, clauses: Vector[ClauseBody])
