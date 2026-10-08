package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.Code as DiagCode

/** Name resolution: bound variables, top-level names, builtin base types; implicitly bound variables. */
trait Names:
  self: Elaborator =>
  import core.*

  val builtinTypes: Map[String, BaseType] =
    Map("int" -> BaseType.IntT, "float" -> BaseType.FloatT, "string" -> BaseType.StringT)

  private def lookupGlobal(n: Name): Option[Int] = scope.get(n).orElse(file.parent.get(n))

  def resolve(c: Cxt, n: Name, span: Span): (Tm, Val, Stage) =
    c.scope.get(n) match
      case Some(l) =>
        val b = c.binder(l)
        (Tm.Var(c.lvl - l - 1), b.ty, b.stage)
      case None =>
        lookupGlobal(n) match
          case Some(id) =>
            state.used += id
            val g = globals(id)
            (Tm.Global(id), if state.typePosition then g.ty else termType(g), g.stage)
          case None =>
            builtinTypes.get(n) match
              case Some(b) => (Tm.Base(b, Stage.S0), Val.U0, Stage.S0)
              case None => unresolved(c, n, span)

  /** E0101, with the most similar name in scope (same case of the first letter, edit distance at most
   *  a third of the name's length). */
  private def unresolved(c: Cxt, n: Name, span: Span): Nothing =
    val candidates = (c.scope.keys ++ scope.keys ++ file.parent.keys).toList.distinct
      .filter(k => k != n && k.headOption.map(_.isUpper) == n.headOption.map(_.isUpper))
    val distance = org.apache.commons.text.similarity.LevenshteinDistance.getDefaultInstance
    val similar =
      candidates.map(k => (distance.apply(k, n).intValue, k)).filter(_._1 <= (n.length / 3).max(1)).sortBy(_._1).headOption.map(_._2)
    throw ElabError(ElabProblem.UnresolvedName(n, span, similar, span.text == n).toDiagnostic, unresolved = Some(n))

  def paramName(p: Tree): Name = p match
    case VarRef(n) => n
    case Ident(n) => n
    case Wildcard() => "_"
    case other => error(DiagCode.E0001, "expected a parameter name", other.span)

  def nameOf(t: Tree): Name = t match
    case Ident(n) => n
    case VarRef(n) => n
    case _ => "_"

  /** The names bound by a binder `(x : A)` or `(A B : T)`: the part before the colon, if it is names. */
  def boundNames(t: Tree): Option[List[Tree]] =
    val (h, args) = TreeOps.flattenApp(t)
    Option.when((h :: args).forall(x => x.isInstanceOf[VarRef] || x.isInstanceOf[Ident]))(h :: args)

  /** Free uppercase variables of a type or term, in order of occurrence (the implicit binders of a
   *  declaration, the variables of a rule). Variables bound by Π binders and lambdas are not free. */
  def freeVars(t: Tree, bound: Set[Name]): List[VarRef] = freeVarsIn(t, bound).distinctBy(_.name)

  private def freeVarsIn(t: Any, bound: Set[Name]): List[VarRef] = t match
    case v: VarRef => if bound(v.name) || v.name == "Type" || v.name == "_" then Nil else List(v)
    case ImplicitPi(ns, d, c) => freeVarsIn(d, bound) ++ freeVarsIn(c, bound ++ ns.map(nameOf))
    case Arrow(None, Ascribe(ns, a), c) if boundNames(ns).isDefined =>
      freeVarsIn(a, bound) ++ freeVarsIn(c, bound ++ boundNames(ns).get.map(nameOf))
    case Lambda(p, ann, b) => freeVarsIn(ann, bound) ++ freeVarsIn(b, bound + nameOf(p))
    case p: Product => p.productIterator.toList.flatMap(freeVarsIn(_, bound))
    case it: Iterable[?] => it.toList.flatMap(freeVarsIn(_, bound))
    case _ => Nil

  /** The type of a global used in a term: a struct family takes its type arguments implicitly there
   *  (`pair 1 "x"` for `pair A B : type = { … }.`). */
  private def termType(g: GlobalEntry): Val = g.kind match
    case GlobalKind.Family(ObjDecl.Struct(_), _) => core.eval(Nil, implicitBinders(g.tyTm))
    case _ => g.ty

  private def implicitBinders(t: Tm): Tm = t match
    case Tm.Pi(x, _, a, b) => Tm.Pi(x, Icit.Impl, a, implicitBinders(b))
    case other => other
