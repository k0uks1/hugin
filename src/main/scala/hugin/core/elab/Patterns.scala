package hugin.core
package elab

import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Patterns of clauses: uppercase variables, `_`, constructors applied to patterns, nat literals. */
enum Pat:
  /** A pattern variable; `implicitBinder` for the name of an implicit binder of the function's type,
   *  which is in scope unless a pattern variable shadows it. */
  case PVar(name: Name, span: Span, implicitBinder: Boolean = false)
  case PWild(span: Span)
  case PCon(ctor: Int, args: List[Pat], span: Span)
  case PLit(n: Long, span: Span)

/** One clause `f p̄ = e.` (or a definition `f X̄ = e.` of a declared function), with its `where` block. */
final case class SurfaceClause(name: Ident, pats: List[Tree], rhs: Tree, span: Span, where: List[Item] = Nil)

trait Patterns:
  self: Elaborator =>
  import core.*

  /** The clause of an item, if it is one: `f p̄ = e.`, or `f X̄ = e.` for a declared meta constant. */
  def surfaceClause(item: Item): Option[SurfaceClause] = item match
    case Clause(lhs, rhs, where) =>
      TreeOps.flattenApp(lhs) match
        case (f: Ident, args) => Some(SurfaceClause(f, args, rhs, item.span, where))
        case (other, _) => error("E0915", "a clause must start with the name of a function", other.span, "expected a name")
    case d: Def if state.functionNames(d.name.name) =>
      val pats = d.params.map {
        case Param.VarParam(v) => v
        case Param.Typed(_, _, sp) => error("E0915", "patterns cannot have type annotations", sp, "type annotation")
      }
      Some(SurfaceClause(d.name, pats, d.rhs, d.span))
    case _ => None

  /** A surface pattern. */
  def pattern(t: Tree): Pat = t match
    case Parens(i) => pattern(i)
    case VarRef(n) => Pat.PVar(n, t.span)
    case Wildcard() => Pat.PWild(t.span)
    case Lit(Literal.IntL(n)) if n >= 0 => Pat.PLit(n, t.span)
    case _ =>
      TreeOps.flattenApp(t) match
        case (id @ Ident(n), args) =>
          val c = constructorNamed(n, id.span)
          val explicit = telescope(globals(c).ty)._1.count(_._2 == Icit.Expl)
          if explicit != args.length then
            error("E0915", s"`$n` expects $explicit argument(s) in a pattern, found ${args.length}", t.span, "wrong number of arguments")
          Pat.PCon(c, args.map(pattern), t.span)
        case _ =>
          fail(
            Diagnostic.error("E0915", "invalid pattern", t.span, "not a pattern")
              .withNote("patterns are uppercase variables, `_`, constructors applied to patterns and natural-number literals")
          )

  private def constructorNamed(n: Name, span: Span): Int =
    scope.get(n).filter(isConstructor) match
      case Some(c) => c
      case None =>
        val what = scope.get(n).map(id => s"`$n` is not a constructor").getOrElse(s"unresolved name `$n`")
        fail(
          Diagnostic.error("E0915", s"$what in a pattern", span, "expected a constructor")
            .withNote("pattern variables are uppercase; lowercase names in patterns are constructors")
        )
