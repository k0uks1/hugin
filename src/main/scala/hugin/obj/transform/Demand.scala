package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

import hugin.obj.typing.Moding

/** Section 7.3: demand transformation (magic sets) for relations with declared modes. */
final class DemandPhase extends Phase:
  def phaseName = "demand"
  def description = "demand transformation for moded relations (Section 7.3)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val demandRels = mutable.LinkedHashMap.empty[(RelSym, Mode), RelSym]
    def demand(c: RelSym, m: Mode): RelSym =
      demandRels.getOrElseUpdate(
        (c, m), {
          val d = RelSym(s"${c.name}^d[${m.show}]", RelKind.Demand(c, m), c.span, c.origin)
          d.cols = c.cols.zip(m.inputs).filter(_._2).map(_._1)
          d
        }
      )
    def inputs(args: List[Term], m: Mode): List[Term] = args.zip(m.inputs).filter(_._2).map(_._1)

    // 1. guarding
    val guarded = p.rules.flatMap { r =>
      r.heads match
        case List(h @ Term.App(RelRef.Sym(c), args)) if c.hasModes =>
          c.modes.map { (m, _) =>
            val g = Formula.Atom(RelRef.Sym(demand(c, m)), inputs(args, m), None)(h.span)
            val nr = r.withParts(body = g :: r.body)
            val gt = ctx.unit.varTypes.get(r)
            if gt != null then ctx.unit.varTypes.put(nr, gt)
            nr
          }
        case _ => List(r)
    }
    // 2. propagation
    val seen = mutable.HashSet.empty[String]
    val propagation = mutable.ArrayBuffer.empty[Rule]
    def propagate(body: List[Formula], span: Span, origin: Origin, expansions: List[Expansion], name: Option[String]): Unit =
      Moding.canonical(body, Set.empty) match
        case Left(_) => // reported by `moding`
        case Right((ordered, _)) =>
          def walk(prefix: List[Formula], fs: List[Formula], b: Set[String]): Unit = fs match
            case Nil =>
            case f :: rest =>
              def call(a: Formula.Atom): Unit =
                val c = a.rel.sym
                if c.hasModes then
                  Moding.firstApplicable(c, a.args, b).foreach { m =>
                    val head = Term.App(RelRef.Sym(demand(c, m)), inputs(a.args, m))(a.span)
                    val r = Rule(name.map(n => s"$n^d"), List(head), prefix)(span, origin, expansions)
                    if seen.add(ObjPrinter.rule(r)) then propagation += r
                  }
              f match
                case a: Formula.Atom => call(a)
                case Formula.Not(a) => call(a)
                case Formula.Agg(_, _, _, ib) =>
                  Moding.canonical(ib, b) match
                    case Right((iordered, _)) => walk(prefix, iordered, b)
                    case Left(_) =>
                case _ =>
              val b2 = Moding.step(f, b).getOrElse(b)
              walk(prefix :+ f, rest, b2)
          walk(Nil, ordered, Set.empty)
    for r <- guarded do propagate(r.body, r.span, r.origin, r.expansions, r.name)
    for q <- p.queries do
      q.body match
        case List(Formula.Disj(alts)) => alts.foreach(a => propagate(a, q.span, q.origin, q.expansions, None))
        case b => propagate(b, q.span, q.origin, q.expansions, None)
    p.rules = guarded ++ propagation
    p.rels = p.rels ++ demandRels.values

  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)
