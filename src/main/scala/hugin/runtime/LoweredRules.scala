package hugin.runtime

import hugin.ir.{CompiledRule, CoreProgram}
import hugin.obj.{ObjProgram, RelSym, TypeSym}
import hugin.obj.typing.TypeOps

/** What evaluating a compiled program over facts files reads of it, apart from its queries: the relations
 *  (names, kinds, columns with their types, directives), the subtyping of the object types (for the types
 *  of input facts), the components and the lowered rules. Equal values have the same fixpoint over the
 *  same facts, with the same relation tags, so a fixpoint computed for one answers the queries of the
 *  other (the REPL: a query adds items to the program without changing its rules, `hugin.query.Fixpoint`).
 *
 *  Equality compares `shape`, a structural copy in which relation and type symbols, which compare by
 *  identity and are created afresh by every compilation, are replaced by their indexes in the program,
 *  and arrays by vectors. Anything else that is not a value (a symbol not in the program, an object with
 *  identity equality) is kept as it is, so it compares by identity: such programs are never taken as
 *  equal, which costs an evaluation but cannot give a wrong answer. Spans and the source trees of rules
 *  are left out (evaluation does not read them), and so are the indexes of the core program (they speed
 *  up evaluation without changing its result; a missing one is built on demand, [[Relation.index]]). */
final class LoweredRules(val prog: CoreProgram, val ops: TypeOps, val shape: Vector[Any]):
  override def equals(that: Any): Boolean = that match
    case l: LoweredRules => shape == l.shape
    case _ => false
  override def hashCode: Int = shape.hashCode

object LoweredRules:
  def of(prog: CoreProgram, obj: ObjProgram): LoweredRules =
    val canon = Canonical(prog.rels.zipWithIndex.toMap, obj.types.zipWithIndex.toMap)
    val rels = prog.rels.zipWithIndex.map { (r, tag) =>
      val d = prog.directives(tag)
      Vector(r.name, r.displayName, canon(r.kind), canon(r.cols), canon(r.result), (d.open, d.input, d.output))
    }
    val types = obj.types.map(t => Vector(t.name, t.displayName, canon(t.kind)))
    val edges = obj.edges.map(e => (canon(e.sub), canon(e.sup)))
    val rules = prog.rules.map(rule(canon, _))
    LoweredRules(prog, TypeOps(obj), Vector(rels, types, edges, prog.components, rules))

  private def rule(canon: Canonical, r: CompiledRule): Vector[Any] =
    Vector(r.nregs, canon(r.body), r.headRel, canon(r.headArgs), r.recursiveAtoms, canon(r.limitRegs))

  /** A relation or type symbol of the program, by its index. */
  private final case class RelRef(tag: Int)
  private final case class TypeRef(index: Int)

  /** A node of a structural copy: the class of a case class (or enum case with fields) and its fields. */
  private final case class Node(cls: Class[?], fields: Vector[Any])

  private final class Canonical(rels: Map[RelSym, Int], types: Map[TypeSym, Int]):
    def apply(x: Any): Any = x match
      case r: RelSym => rels.get(r).fold[Any](r)(RelRef(_))
      case t: TypeSym => types.get(t).fold[Any](t)(TypeRef(_))
      case a: Array[?] => a.toVector.map(apply)
      case s: Set[?] => s.map(apply)
      case m: Map[?, ?] => m.map((k, v) => apply(k) -> apply(v))
      case s: Seq[?] => s.map(apply)
      case p: Product if p.productArity > 0 => Node(p.getClass, p.productIterator.map(apply).toVector)
      case other => other
