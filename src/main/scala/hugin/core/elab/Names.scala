package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Name resolution: bound variables, top-level names, builtin base types; implicitly bound variables. */
trait Names:
  self: Elaborator =>
  import core.*

  val builtinTypes: Map[String, BaseType] =
    Map("int" -> BaseType.IntT, "float" -> BaseType.FloatT, "string" -> BaseType.StringT)

  /** A top-level name: the file's, or the enclosing scope's (the prelude's) unless the file declares the
   *  name (also later in the file: a declaration shadows the prelude's in the whole file). */
  def lookupGlobal(n: Name): Option[Int] =
    scope.get(n).orElse(
      if state.declaredHere(n) then None
      else openedGlobal(n).getOrElse(file.parent.get(n)) // the names opened by `%use` ([[Uses]])
    )

  def resolve(c: Cxt, n: Name, span: Span): (Tm, Val, Stage) =
    c.scope.get(n) match
      case Some(l) =>
        val b = c.binder(l)
        recordParamUse(c, span, b)
        (Tm.Var(c.lvl - l - 1), b.ty, b.stage)
      case None =>
        lookupGlobal(n) match
          case Some(id) if state.unelaborated(n) && scope.get(n).contains(id) =>
            // a function whose clauses have a syntax error: its uses are not elaborated
            state.used += id
            throw ElabError(ElabProblem.UnresolvedName(n, span, None, false).toDiagnostic, silent = true)
          case Some(found) =>
            val id = sharedAt(found, state.stage)
            state.used += found
            recordUse(span, id)
            globalRef(id)
          case None =>
            builtinTypes.get(n).filter(_ => file.builtinNames) match
              case Some(b) => (Tm.Base(b, Stage.S0), Val.U0, Stage.S0)
              case None => unresolved(c, n, span)

  /** A global, already resolved. */
  def globalRef(id: Int): (Tm, Val, Stage) =
    val g = globals(id)
    (Tm.Global(id), if state.typePosition then g.ty else termType(g), g.stage)

  /** E0101, with the most similar name in scope (same case of the first letter, edit distance at most
   *  a third of the name's length). */
  private def unresolved(c: Cxt, n: Name, span: Span): Nothing =
    checkAmbiguous(n, span)
    if state.erroneous(n) then throw ElabError(ElabProblem.UnresolvedName(n, span, None, false).toDiagnostic, silent = true)
    val candidates = (c.scope.keys ++ scope.keys ++ state.opened.keys ++ file.parent.keys).toList.distinct
      .filter(k => k.headOption.map(_.isUpper) == n.headOption.map(_.isUpper))
    val similar = similarName(n, candidates)
    throw ElabError(ElabProblem.UnresolvedName(n, span, similar, span.text == n).toDiagnostic, unresolved = Some(n))

  /** The candidate most similar to `n` (edit distance at most a third of its length), if any. */
  def similarName(n: Name, candidates: List[Name]): Option[Name] =
    val distance = org.apache.commons.text.similarity.LevenshteinDistance.getDefaultInstance
    candidates.filter(_ != n).map(k => (distance.apply(k, n).intValue, k)).filter(_._1 <= (n.length / 3).max(1)).sortBy(_._1)
      .headOption.map(_._2)

  def paramName(p: Tree): Name = p match
    case VarRef(n) => n
    case Ident(n) => n
    case Wildcard() => "_"
    case other => fail(TypeProblem.NotAParameterName(other.span))

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
    case GlobalKind.Family(ObjDecl.Struct, _) => core.eval(Nil, implicitBinders(g.tyTm))
    case _ => g.ty

  private def implicitBinders(t: Tm): Tm = t match
    case Tm.Pi(x, _, a, b) => Tm.Pi(x, Icit.Impl, a, implicitBinders(b))
    case other => other
