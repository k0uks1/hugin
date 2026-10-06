package hugin.obj
package transform

import hugin.compiler.*
import scala.collection.mutable

/** Section 7.4: derivation relations for rules under `%derivations`. */
final class DerivationsPhase extends ObjProgramPhase:
  def phaseName = "derivations"
  def description = "introduce derivation relations (Section 7.4)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val names = ctx.unit.derivationRules
    val facts = ctx.unit.facts
    def baseName(n: String): String = n.indexOf('[') match
      case -1 => n
      case i => n.substring(0, i)
    def wanted(r: Rule): Boolean = r.name.exists { n =>
      !n.endsWith("^d") && (names.contains(baseName(n)) || r.heads.exists {
        case Term.App(RelRef.Sym(c), _) => facts(c).derivations || c.instanceOf.exists(i => facts(i._1).derivations)
        case _ => false
      })
    }
    val groups = p.rules.filter(wanted).groupBy(_.name.get)
    if groups.isEmpty then return
    val replaced = mutable.HashMap.empty[Rule, List[Rule]]
    val newRels = mutable.ArrayBuffer.empty[RelSym]
    for (name, rs) <- groups.toList.sortBy(_._1); (r, i) <- rs.zipWithIndex do
      val rn = if rs.length == 1 then s"@$name" else s"@$name#${i + 1}"
      val head = r.heads.head
      val Term.App(RelRef.Sym(c), _) = head: @unchecked
      var k = 0
      val atoms = mutable.ListBuffer.empty[(RelSym, String)]
      val body = r.body.map {
        case a @ Formula.Atom(RelRef.Sym(rel), args, as) =>
          k += 1
          val v = as.getOrElse(s"I#$k")
          atoms += ((rel, v))
          Formula.Atom(RelRef.Sym(rel), args, Some(v))(a.span)
        case other => other
      }
      val d = RelSym(rn, RelKind.Derivation(name), r.span, r.origin)
      d.cols = (Column(None, OType.Fact(c, Nil)) :: atoms.toList.map((rel, _) => Column(None, OType.Fact(rel, Nil)))).toVector
      ctx.unit.facts = ctx.unit.facts.updated(d)(_.copy(output = true))
      newRels += d
      val r1 = r.withParts(body = body)
      val dh = Term.App(RelRef.Sym(d), head :: atoms.toList.map((_, v) => Term.Var(v)(r.span)))(r.span)
      val r2 = Rule(Some(rn), List(dh), body)(r.span, r.origin, r.expansions)
      replaced(r) = List(r1, r2)
    p.rules = p.rules.flatMap(r => replaced.getOrElse(r, List(r)))
    p.rels = p.rels ++ newRels
