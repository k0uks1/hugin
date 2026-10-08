package hugin.core
package handover

import hugin.core.elab.ObjectProblem
import hugin.obj
import hugin.util.*
import scala.collection.mutable

/** Generic rules (REDESIGN §6.7): a rule over the instances of families whose type arguments nothing
 *  determines (`len nil 0.`, `len (cons _ L) M :- len L N, …`) is a family of rules. It is staged at
 *  every instance of its head's family that the staged program uses, by solving its unknowns so that its
 *  head is that instance (by unification, then undone), until no new instances are used. This replaces
 *  the worklist of the old monomorphization phase.
 *
 *  Polymorphic recursion is rejected: an instance of a rule of family `f` at `ā` that uses `f` at other
 *  arguments would create ever larger instances. */
final class Generics(core: Core, symbols: ObjectSymbols, reporter: Reporter, handover: Handover):
  import core.*

  private final case class Generic(rule: CoreItem.RuleItem, index: Int, family: Int, args: List[Val])

  def rules(items: List[CoreItem.RuleItem]): List[obj.Rule] =
    val (withHead, without) = items.zipWithIndex.partitionMap((r, i) => headFamily(r).map((f, as) => Generic(r, i, f, as)).toLeft(r))
    without.flatMap(handover.rule(_)) ++ worklist(withHead)

  private def worklist(generics: List[Generic]): List[obj.Rule] =
    val done = mutable.HashSet.empty[(Int, Int)]
    val rejected = mutable.HashSet.empty[Int]
    val out = mutable.ListBuffer.empty[obj.Rule]
    var changed = true
    while changed do
      changed = false
      for
        inst <- symbols.instanceIds
        g <- generics if globals(inst).instanceOf.exists(_._1 == g.family) && !rejected(g.index) && done.add((g.index, inst))
      do
        changed = true
        instantiate(g, inst) match
          case Right(r) => out ++= r
          case Left(p) =>
            rejected += g.index
            reporter.report(p.toDiagnostic)
    out.toList

  /** The family of a rule's head and the head's arguments of the family (values over the rule's
   *  variables). */
  private def headFamily(r: CoreItem.RuleItem): Option[(Int, List[Val])] =
    val env = locals(r.vars.length)
    r.heads.headOption.flatMap { h =>
      force(Val.unloc(eval(env, h))) match
        case Val.Rigid(Head.Glob(f), sp) if globals(f).kind.isInstanceOf[GlobalKind.Family] =>
          Some((f, sp.reverse.takeWhile(_.isInstanceOf[Elim.EApp]).collect { case Elim.EApp(a, _) => a }))
        case _ => None
    }

  private def locals(n: Int): List[Val] = (0 until n).reverse.map(Val.local).toList

  private def instantiate(g: Generic, inst: Int): Either[ObjectProblem, Option[obj.Rule]] = tentatively {
    val key = globals(inst).instanceOf.get._2
    val n = g.rule.vars.length
    val unified =
      try
        g.args.zip(key).foreach((a, k) => unify(n, a, eval(Nil, k)))
        true
      catch case _: UnifyError => false
    if !unified then Right(None)
    else
      polymorphicUse(g, key) match
        case Some(p) => Left(p)
        case None => Right(handover.rule(g.rule))
  }

  /** A use of the rule's family at other arguments than the instance's (`nest X :- nest (put X).`). */
  private def polymorphicUse(g: Generic, key: List[Tm]): Option[ObjectProblem] =
    val env = locals(g.rule.vars.length)
    val names = g.rule.vars.map(_._1).reverse
    def uses(t: Tm, span: Span): List[(Int, Span)] = t match
      case Tm.Obj(ObjForm.Loc(sp), List(u)) => uses(u, sp)
      case Tm.Global(id) => List((id, span))
      case other => Tm.children(other).flatMap(uses(_, span))
    g.rule.body.toList.flatMap(b => uses(nf(env, b), g.rule.span)).collectFirst {
      case (id, span) if globals(id).instanceOf.exists((f, as) => f == g.family && as != key) =>
        val fam = globals(g.family).name
        def show(as: List[Tm]) = as.map(a => showTm(names, a match { case Tm.Quote(u) => u; case u => u })).mkString("[", ", ", "]")
        ObjectProblem.PolymorphicRecursion(fam, show(globals(id).instanceOf.get._2), show(key), span)
    }
