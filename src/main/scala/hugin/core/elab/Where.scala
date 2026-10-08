package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** `where` blocks of clauses: local definitions, Haskell-style (designer addition to REDESIGN §6.4).
 *
 *  The bindings of a block are elaborated in order in the context of the clause's right-hand side (its
 *  pattern variables and the earlier bindings), and the right-hand side sees all of them. No new core
 *  form is needed:
 *
 *  - `x = e.` and `x : A = e.` are let-bound definitions (`Let` in the leaf's body);
 *  - `f : A.` followed by clauses `f p̄ = e.` is a local function: it is *lambda-lifted* to a hidden
 *    global function abstracting over the bound variables of the context (defined ones are let-bound in
 *    its type and re-defined in its clauses), elaborated by the clause compiler with coverage, and
 *    checked for termination with the other functions;
 *  - `c x̄ = e.` with a constructor `c` is an irrefutable pattern binding: each bound name is a
 *    lifted selector function with one clause `sel (c x̄) = xᵢ`, so coverage rejects refutable patterns.
 */
trait Where:
  self: Elaborator =>
  import core.*

  /** Extends the context of a right-hand side with a `where` block. */
  def elabWhere(c: Cxt, owner: Name, items: List[Item]): Cxt =
    var cc = c
    var rest = items
    while rest.nonEmpty do
      val (next, more) = binding(cc, owner, rest)
      cc = next
      rest = more
    cc

  /** Elaborates the first binding of `items` (a signature takes its clauses along). */
  private def binding(c: Cxt, owner: Name, items: List[Item]): (Cxt, List[Item]) = items.head match
    case Decl(name, Nil, tpe, None, Some(e)) =>
      val a = checkType(c, tpe, Stage.S1)
      val av = ev(c, a)
      (define(c, name.name, av, ev(c, check(c, e, av, Stage.S1))), items.tail)
    case Def(name, Nil, rhs) =>
      val (t, ty) = inferS(c, rhs, Stage.S1)
      (define(c, name.name, ty, ev(c, t)), items.tail)
    case d @ Decl(name, Nil, tpe, None, None) =>
      val (clauses, rest) = items.tail.span(isClauseOf(name.name))
      if clauses.isEmpty then fail(ClauseProblem.LocalWithoutClauses(name.name, d.span))
      (localFunction(c, owner, name, tpe, clauses.flatMap(localClause), d.span), rest)
    case cl @ Clause(lhs, rhs, Nil) if constructorHead(lhs) =>
      (patternBinding(c, owner, lhs, rhs, cl.span), items.tail)
    case other =>
      fail(ClauseProblem.InvalidLocal(other.span))

  private def isClauseOf(n: Name)(item: Item): Boolean = item match
    case Clause(lhs, _, _) => TreeOps.headName(lhs).exists(_.name == n)
    case d: Def => d.name.name == n
    case _ => false

  private def localClause(item: Item): Option[SurfaceClause] = item match
    case Clause(lhs, rhs, wh) =>
      val (f, args) = TreeOps.flattenApp(lhs)
      Some(SurfaceClause(f.asInstanceOf[Ident], args, rhs, item.span, wh))
    case d: Def => Some(SurfaceClause(d.name, d.params.map(p => VarRef(p.nameString)(p.span)), d.rhs, d.span, Nil))
    case _ => None

  private def constructorHead(lhs: Tree): Boolean = TreeOps.headName(lhs).exists(n => scope.get(n.name).exists(isConstructor))

  /** The bound (not defined) variables of a context, as values, outermost first. */
  private def boundVars(c: Cxt): List[Val] =
    c.binders.reverse.zipWithIndex.collect { case (b, l) if b.defn.isEmpty => Val.local(l) }

  /** Abstracts a type in context `c` over the context: Π for bound variables, let for defined ones. */
  private def closeOver(c: Cxt, a: Tm): Tm =
    c.binders.foldLeft(a) { (acc, b) =>
      b.defn match
        case Some(d) => Tm.Let(b.name, b.tyTm, d, acc)
        case None => Tm.Pi(b.name, Icit.Expl, b.tyTm, acc)
    }

  /** A hidden global function of type `closeOver(c, a)`, and `c` extended by `name` defined as it applied
   *  to the bound variables. */
  private def lift(c: Cxt, owner: Name, name: Name, a: Tm, span: Span): (Int, Cxt) =
    val closed = closeOver(c, a)
    val id = addGlobal(GlobalEntry(s"$owner.$name", eval(Nil, closed), closed, Stage.S1, GlobalKind.Function(-1, None), span))
    val value = boundVars(c).foldLeft(globalValue(id))((f, v) => app(f, v, Icit.Expl))
    (id, define(c, name, ev(c, a), value))

  /** The names of `c` re-expressed over the arguments of a function lifted from `c` (its first arguments
   *  are the bound variables of `c`, whose values at a leaf are `args`). */
  private def prelude(c: Cxt)(args: Vector[Val]): List[(Name, Val, Val)] =
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

  private def localFunction(c: Cxt, owner: Name, name: Ident, tpe: Tree, clauses: List[SurfaceClause], span: Span): Cxt =
    val a = checkType(c, tpe, Stage.S1)
    val (id, c2) = lift(c, owner, name.name, a, span)
    val k = boundVars(c).length
    val padded = clauses.map(cl => cl.copy(pats = List.fill(k)(Wildcard()(cl.span)) ++ cl.pats))
    elabFunction(id, padded, prelude(c2))
    c2

  /** `c x̄ = e.`: a selector function per bound name. */
  private def patternBinding(c: Cxt, owner: Name, lhs: Tree, rhs: Tree, span: Span): Cxt =
    val (et, ety) = inferS(c, rhs, Stage.S1)
    val (head, args) = TreeOps.flattenApp(lhs)
    val names = args.map {
      case Ident(n) => Some(n)
      case VarRef(n) => Some(n)
      case Wildcard() => None
      case other => fail(ClauseProblem.BindingNotName(other.span))
    }
    val fieldTypes = constructorFieldTypes(c, head.asInstanceOf[Ident], ety, args.length, span)
    names.zip(fieldTypes).zipWithIndex.foldLeft(c) {
      case (cc, ((Some(n), fty), i)) =>
        val selTy = Tm.Pi("_", Icit.Expl, quote(c.lvl, ety), Tm.shift(fty, 1))
        val (id, _) = lift(c, owner, s"$n", selTy, span)
        val k = boundVars(c).length
        val pat = TreeOps.flattenApp(lhs) match
          case (h, as) => as.zipWithIndex.foldLeft(h)((f, ai) =>
              Apply(f, if ai._2 == i then VarRef("$sel")(ai._1.span) else Wildcard()(ai._1.span))(span)
            )
        val sel = SurfaceClause(Ident(s"(binding of `$n`)")(span), List.fill(k)(Wildcard()(span)) :+ pat, VarRef("$sel")(span), span, Nil)
        elabFunction(id, List(sel), prelude(c))
        val value = app(boundVars(c).foldLeft(globalValue(id))((f, v) => app(f, v, Icit.Expl)), ev(c, et), Icit.Expl)
        define(cc, n, ev(c, fty), value)
      case (cc, ((None, _), _)) => cc
    }

  /** The types (in context `c`) of the explicit fields of constructor `ctor` at type `ty`; they must not
   *  depend on each other. */
  private def constructorFieldTypes(c: Cxt, ctor: Ident, ty: Val, n: Int, span: Span): List[Tm] =
    val id = scope(ctor.name)
    var cty = globals(id).ty
    val fields = scala.collection.mutable.ListBuffer.empty[Val]
    var more = true
    while more do
      force(cty) match
        case Val.Pi(x, i, a, cl) =>
          val m = ev(c, freshMeta(c, a, Stage.S1, ctor.span, s"the argument `$x` of `${ctor.name}`", allowUnsolved = i == Icit.Expl))
          if i == Icit.Expl then fields += a
          cty = inst(cl, m)
        case _ => more = false
    unifyAt(c, span, ty, cty)
    if fields.length != n then fail(ClauseProblem.BindingArity(ctor.name, fields.length, n, span))
    fields.toList.map { f =>
      val t = quote(c.lvl, f)
      if containsMeta(t) then fail(ClauseProblem.DependentBinding(span))
      t
    }

  private def containsMeta(t: Tm): Boolean = Tm.exists(t) {
    case Tm.Meta(_) | Tm.AppPruning(_, _) => true
    case _ => false
  }
