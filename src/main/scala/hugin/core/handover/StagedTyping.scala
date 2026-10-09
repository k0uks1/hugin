package hugin.core
package handover

import hugin.core.objtype.*
import hugin.obj
import hugin.obj.{Formula, OType, Term}
import hugin.util.*

/** Object typing of staged items (reference: object/types): the check of the closed object code an item
 *  stages to, by the same object type system as the elaboration ([[elab.ObjectTyping]]). It gives every
 *  item the types of its variables (which the object level's transformations use), and reports problems
 *  only for items whose code came from meta code: what the elaboration could not see (the meet of a
 *  variable that meta code uses at a narrower type, the instances of a generic rule or a functor body). An
 *  item without meta code was checked as it is by its elaboration. */
final class StagedTyping(core: Core, symbols: ObjectSymbols, reporter: Reporter, index: hugin.compiler.SemanticIndex):
  private val env = ObjEnv(core)
  private var current: Option[ObjTypes] = None
  private def types: ObjTypes =
    if current.isEmpty then current = Some(ObjTypes(env))
    current.get

  /** Checks a staged item over the variables `names` (innermost first); reports its problems if `report`.
   *  `None` if it has a problem that is reported. */
  def check(
      names: List[Name],
      heads: List[Tm],
      body: List[Tm],
      origin: Origin,
      report: Boolean,
      item: (Span, String)
  ): Option[Map[String, OType]] =
    val walk = ObjWalk(env, ObjWalk.staged(names, Nil))
    val hs = walk.headTerms(heads)
    val fs = body.flatMap(walk.formulas)
    val (problems, gamma) = ObjCheck(types, hs, fs, walk.constructing).run()
    if report && problems.nonEmpty then
      problems.foreach { p =>
        val d = p.toDiagnostic
        // code that meta code generated elsewhere: the note names the item it was staged for
        val (span, what) = item
        val at = d.primarySpan
        val outside = at.exists && span.exists && !(at.source == span.source && at.start >= span.start && at.end <= span.end)
        val frame = Option.when(outside && origin.frames.isEmpty)(TraceFrame(s"in the code staged for this $what", span))
        reporter.report(d.withOrigin(Origin(frame.toList ++ d.origin.frames ++ origin.frames)))
      }
      None
    else Some(gamma.map((x, t) => x -> otype(t)))

  /** An edge of a module instance, once staged: in scope for the items checked after it. */
  def addEdge(sub: Val, sup: Int): Unit =
    core.objEdges = (sub, sup) :: core.objEdges
    current = None

  private def otype(t: OTy): OType = t match
    case OTy.Base(b) => OType.Base(b)
    case OTy.Con(OHead.G(id), Nil) => symbols.typeSym(id).map(OType.Con(_, Nil)).getOrElse(OType.Err)
    case OTy.Fact(OHead.G(id), Nil) => symbols.relSym(id).map(OType.Fact(_, Nil)).getOrElse(OType.Err)
    case OTy.RelTop => OType.RelTop
    case OTy.Union(ms) => OType.union(ms.map(otype))
    case _ => OType.Err

  /** Records the type of every object variable occurrence of an item in the semantic index. */
  def recordVariables(item: Span, heads: List[Term], body: List[Formula], g: Map[String, OType]): Unit =
    def note(span: Span, n: String) = g.get(n).foreach(tp => index.variable(span, n, obj.Var.display(n), tp.show, item))
    def term(t: Term): Unit = t match
      case v @ Term.Var(n) if !obj.Var.isWild(n) => note(v.span, n)
      case Term.App(_, as) => as.foreach(term)
      case a @ Term.As(x, v) =>
        term(x)
        note(a.span, v)
      case Term.Ascr(x, _) => term(x)
      case Term.Proj(v, _) => term(v)
      case Term.With(v, fs) =>
        term(v)
        fs.foreach(f => term(f._2))
      case Term.Arith(_, l, r) =>
        term(l)
        term(r)
      case Term.Neg(x) => term(x)
      case _ =>
    def formula(f: Formula): Unit = f match
      case Formula.Atom(_, as, _) => as.foreach(term)
      case Formula.Cmp(_, l, r) =>
        term(l)
        term(r)
      case Formula.Not(a) => formula(a)
      case Formula.Agg(_, _, t, b) =>
        term(t)
        b.foreach(formula)
      case Formula.Disj(alts) => alts.flatten.foreach(formula)
    heads.foreach(term)
    body.foreach(formula)
