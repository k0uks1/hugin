package hugin.core
package elab

import hugin.util.*

/** Lambda lifting of functions defined by clauses inside a context: the local functions of `where` blocks
 *  ([[Where]], reference: meta/where) and the member functions of module bodies ([[ModuleBodies]],
 *  reference: modules). A function lifted from a context `c` is a hidden global function whose type
 *  abstracts over `c` (Π for the bound variables, let for the defined ones); in `c`, the function is
 *  that global applied to the bound variables of `c`. Its clauses are padded with a wildcard per bound
 *  variable, and [[prelude]] gives the names of `c` at each leaf. The leading arguments are *hidden*
 *  ([[GlobalEntry.hidden]]): coverage messages and printing leave them out. */
trait Lifting:
  self: Elaborator =>
  import core.*

  /** The bound (not defined) variables of a context, as values, outermost first. */
  def boundVars(c: Cxt): List[Val] =
    c.binders.reverse.zipWithIndex.collect { case (b, l) if b.defn.isEmpty => Val.local(l) }

  /** Abstracts a type in context `c` over the context: Π for bound variables, let for defined ones. */
  private def closeOver(c: Cxt, a: Tm): Tm =
    c.binders.foldLeft(a) { (acc, b) =>
      b.defn match
        case Some(d) => Tm.Let(b.name, b.tyTm, d, acc)
        case None => Tm.Pi(b.name, Icit.Expl, b.tyTm, acc)
    }

  /** A hidden global function `name` of type `closeOver(c, a)`, and its value in `c`: the global applied
   *  to the bound variables of `c`. */
  def liftedFunction(c: Cxt, name: Name, a: Tm, span: Span, declSpan: Span = Span.NoSpan): (Int, Val) =
    val closed = closeOver(c, a)
    val bound = boundVars(c)
    val entry = GlobalEntry(name, eval(Nil, closed), closed, Stage.S1, GlobalKind.Function(-1, None), span, declSpan, hidden = bound.length)
    val id = addGlobal(entry)
    (id, bound.foldLeft(globalValue(id))((f, v) => app(f, v, Icit.Expl)))

  /** The clauses of a function lifted from `c`, with a wildcard for each hidden argument. */
  def padded(c: Cxt, clauses: List[SurfaceClause]): List[SurfaceClause] =
    val k = boundVars(c).length
    clauses.map(cl => cl.copy(pats = List.fill(k)(hugin.syntax.Trees.Wildcard()(cl.span)) ++ cl.pats))

  /** The names of `c` re-expressed over the arguments of a function lifted from `c` (its first arguments
   *  are the bound variables of `c`, whose values at a leaf are `args`). */
  def prelude(c: Cxt)(args: Vector[Val]): List[(Name, Val, Val)] =
    var env = List.empty[Val]
    var next = 0
    for b <- c.binders.reverse do
      b.defn match
        case Some(d) => env = eval(env, d) :: env
        case None =>
          env = args(next) :: env
          next += 1
    val byLevel = env.reverse.toVector
    c.scope.toList.sortBy(_._2).map { (n, l) =>
      val ty = eval(env.drop(c.lvl - l), c.binder(l).tyTm)
      (n, ty, byLevel(l))
    }

  /** Wraps the definitions bound after level `base` around `body` as lets. The names of a lifted
   *  function's prelude (levels `base` to `preludeEnd`) that the leaf does not use are left out: lets are
   *  evaluated when the leaf is, and a definition of a module body may call the function itself
   *  (`limit = bound 2` next to `bound`, [[MemberFunctions]]). */
  def letBound(c: Cxt, base: Int, preludeEnd: Int, body: Tm): Tm =
    c.binders.take(c.lvl - base).zipWithIndex.foldLeft(body) { case (acc, (b, k)) =>
      val level = c.lvl - 1 - k
      if level < preludeEnd && !occurs(0, acc) && !hasUnknowns(acc) then Tm.shift(acc, -1, 1)
      else Tm.Let(b.name, b.tyTm, b.defn.getOrElse(throw Impossible("a pattern binder without definition")), acc)
    }

  private def hasUnknowns(t: Tm): Boolean = Tm.exists(t) {
    case Tm.Meta(_) | Tm.AppPruning(_, _) => true
    case _ => false
  }
