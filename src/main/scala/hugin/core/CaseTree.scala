package hugin.core

/** The compiled pattern match of a meta function defined by clauses (REDESIGN §6.4).
 *
 *  It works on a growing vector of variables, by level: first the function's arguments (implicit ones
 *  included), then the arguments of each constructor matched so far. A [[CaseTree.Split]] inspects one
 *  variable, which must evaluate to a constructor application, and appends its arguments; a
 *  [[CaseTree.Leaf]] evaluates the body in the vector. Impossible constructors (ruled out by index
 *  unification) have no branch. */
enum CaseTree:
  /** `body` lives in a context of the variables `order` (levels into the `size` variables, in an order in
   *  which their types form a telescope; variables solved by matching are left out). For display, `names`
   *  names them and `patterns` are the function's explicit arguments as patterns (in the same context). */
  case Leaf(body: Tm, size: Int, order: Vector[Int], names: Vector[Name], patterns: List[Tm])
  case Split(level: Int, branches: List[CaseBranch])

  /** A split on a variable of a type with decidable equality but no constructors (the references to
   *  object constants `Sym`, meta literals in quoted patterns): a branch per value the clauses name
   *  (`value` is closed and normal), and `default` for every other value. */
  case SplitAtom(level: Int, branches: List[(Tm, CaseTree)], default: CaseTree)

final case class CaseBranch(ctor: Int, arity: Int, tree: CaseTree)
