package hugin.core
package elab

import hugin.syntax.{Printer, Tree, TreeOps}
import hugin.syntax.Trees.{Ident, NamedArg, Select, VarRef}

/** A member of a functor applied, read without an instance (reference: modules, "Members without an
 *  instance"; #186 P9g, the locale-style proofs of level 3.5). Selecting a member of an application
 *  `f ā` evaluates the application, and a module body is generative: the evaluation creates an instance,
 *  with fresh object constants. A meta member that mentions no object constant of the body, directly or
 *  through other members ([[hugin.core.ModuleBody.free]]), does not need one: `(f ā).m` is the member's
 *  definition at the arguments, read from the functor's body without evaluating it, as Isabelle reads a
 *  locale's theorem `tc.lemma` at the locale's parameters. A lemma about the body's own relations is such a
 *  member, since a judgment names the relations by their positions (`own i`), not by their constants.
 *
 *  The member's definition is in the context of the body's environment and the members before it; the
 *  members it mentions are let-bound, and the others (object constants included, which member functions
 *  are lifted over without using them) are bound to fresh object variables, which nothing reads. A meta
 *  member that mentions an object constant needs an instance: at closed arguments it is read through one,
 *  as before; at arguments with variables there is none (E0107). */
trait LocaleMembers:
  self: Elaborator =>
  import core.*

  /** `sel` = `(f ā).m`, read without an instance if `f` is a functor whose value is a module body and `m` a
   *  meta member of it that mentions no object constant; `None` if it is another form. */
  def memberWithoutInstance(c: Cxt, sel: Select): Option[(Tm, Val, Stage)] =
    TreeOps.flattenApp(sel.qual) match
        case (head @ Ident(f), args)
            if args.nonEmpty && !args.exists(_.isInstanceOf[NamedArg]) && !c.scope.contains(f) && !state.bodyDeclared(f) =>
          lookupGlobal(f).filter(globals(_).stage == Stage.S1).flatMap(id => functorBody(id, args.length)).flatMap { (body, env) =>
            val i = body.members.indexWhere(_.name == sel.name)
            if i < 0 then None
            else
              body.members(i).kind match
                case MemberKind.Object(_) => None
                case MemberKind.Defined(value) =>
                  body.free.get(sel.name) match
                    case Some(needed) => Some(atStage(Stage.S1)(read(c, head, args, body, env, i, value, needed)))
                    case None if args.exists(mentionsLocal(c, _)) =>
                      val objects = body.members.collect { case m if m.kind.isInstanceOf[MemberKind.Object] => m.name }
                      fail(ElabProblem.NeedsInstance(Printer.show(sel.qual), sel.name, objects, sel.span))
                    case None => None
          }
        case _ => None

  /** The body of a functor `id` of `k` explicit parameters whose definition is a module body,
   *  `[x̄] { … }`, with the body's environment (terms over the parameters). Read from the definition's
   *  term, without evaluating it. */
  private def functorBody(id: Int, k: Int): Option[(ModuleBody, List[Tm])] =
    def under(t: Tm, n: Int): Option[(ModuleBody, List[Tm])] = t match
      case Tm.Lam(_, Icit.Expl, b) if n > 0 => under(b, n - 1)
      case Tm.Module(body, env) if n == 0 => Some((body, env))
      case _ => None
    globals(id).kind match
      case GlobalKind.Definition(tm, _) => under(tm, k)
      case _ => None

  /** Whether `t` mentions a variable of `c` (by name: the arguments of an application in a function or
   *  a declaration's type, where no instance exists). */
  private def mentionsLocal(c: Cxt, t: Tree): Boolean =
    TreeOps.nodes(t).exists {
      case Ident(n) => c.scope.contains(n)
      case VarRef(n) => c.scope.contains(n)
      case _ => false
    }

  /** The member `i` of `body` (its definition `value`) at the arguments `args` of the functor `head`, with
   *  the members `needed` let-bound. */
  private def read(c: Cxt, head: Tree, args: List[Tree], body: ModuleBody, env: List[Tm], i: Int, value: Tm, needed: Set[Name])
      : (Tm, Val, Stage) =
    // the functor and its arguments, checked against its parameters (its use is recorded)
    val (hTm, hTy, _) = infer(c, head)
    var ty = hTy
    val argTms = args.map { a =>
      force(ty) match
        case Val.Pi(_, Icit.Expl, d, cl) =>
          val tm = check(c, a, d, Stage.S1)
          ty = inst(cl, ev(c, tm))
          tm
        case other => throw Impossible(s"a functor's parameter: $other")
    }
    val m = body.members(i)
    // the members before `m`: the needed ones let-bound, the others fresh (nothing reads them)
    def inBody(t: Tm): Tm =
      val inner = body.members.take(i).foldRight(t) { (mj, acc) =>
        mj.kind match
          case MemberKind.Defined(d) if needed(mj.name) => Tm.Let(mj.name, mj.ty, d, acc)
          case _ => Tm.Fresh(List(mj.name), acc)
      }
      val k = argTms.length
      val n = env.length
      val atEnv = Tm.apps(lams(n, inner), env.reverse.map((_, Icit.Expl)))
      Tm.apps(lams(k, atEnv), argTms.map((_, Icit.Expl)))
    val _ = hTm
    val tyTm = inBody(m.ty)
    (inBody(value), ev(c, tyTm), Stage.S1)

  private def lams(n: Int, body: Tm): Tm = (0 until n).foldLeft(body)((acc, i) => Tm.Lam(s"x$i", Icit.Expl, acc))
