package hugin.runtime

import hugin.ir.{BodyOp, CompiledRule, CoreProgram, Expr, Id}
import hugin.obj.{ObjProgram, RelSym, TypeSym}
import scala.collection.mutable

/** Comparable keys for the steps of an evaluation (issue #126, PR 4, [[Reuse]]): loading the facts files,
 *  then each component in the order of evaluation. Relations are named by the index of their first
 *  occurrence along the steps (tags differ between programs), and the key of a step carries the shapes of
 *  the relations and types it names for the first time. So two evaluations whose first `k` keys are equal
 *  have, after `k` steps, the same relations with the same facts in the same order (evaluation and fact
 *  loading being deterministic functions of what the keys hold), relation `i` of one being relation `i`
 *  of the other ([[tagOf]]).
 *
 *  A value without structural equality (a symbol not in the program) stays as itself in a key, so it never
 *  matches a key of another program: a miss costs an evaluation, never a wrong fixpoint. */
final class ComponentKeys(prog: CoreProgram, obj: ObjProgram):
  private val tags = prog.rels.zipWithIndex.toMap
  private val indexOfTag = mutable.HashMap.empty[Int, Int]
  private val tagOfIndex = mutable.ArrayBuffer.empty[Int]
  private val typeIndex = mutable.HashMap.empty[TypeSym, Int]
  private val typeOfIndex = mutable.ArrayBuffer.empty[TypeSym]
  private val rulesByComp = prog.rules.groupBy(r => prog.components.indexWhere(_.contains(r.headRel)))

  /** The tag, in this program, of the relation with index `i`. */
  def tagOf(i: Int): Int = tagOfIndex(i)

  /** The number of relations named so far. */
  def named: Int = tagOfIndex.length

  /** The key of loading facts files whose texts are `texts` and that mention the names `names`: the
   *  object types with their subtyping (the types of input facts), and the relations whose display name
   *  is mentioned ([[FactLoader]] resolves names among them). */
  def facts(texts: List[String], names: Set[String]): Vector[Any] = step {
    val types = obj.types.map(canon)
    val edges = obj.edges.map(e => (canon(e.sub), canon(e.sup)))
    val rels = prog.rels.indices.filter(t => names(prog.rels(t).displayName)).map(rel)
    Vector(texts, types, edges, rels)
  }

  /** The members of a component, in order. */
  private def members(ci: Int): Vector[Int] = prog.components(ci).map(rel)

  /** The key of one rule of the program. */
  private def rule(r: CompiledRule): Vector[Any] =
    Vector(r.nregs, r.body.toVector.map(op), rel(r.headRel), r.headArgs.toVector.map(expr), r.recursiveAtoms, r.limitRegs.toVector)

  /** The rules of a component. */
  def rules(ci: Int): Vector[CompiledRule] = rulesByComp.getOrElse(ci, Vector.empty)

  /** The key of evaluating the component `ci`. */
  def component(ci: Int): Vector[Any] = step(Vector(members(ci), rules(ci).map(rule)))

  /** `key` followed by the shapes of the relations and types first named while computing it. */
  private def step(key: => Vector[Any]): Vector[Any] =
    val (rels, types) = (tagOfIndex.length, typeOfIndex.length)
    val k = key
    val relShapes = mutable.ArrayBuffer.empty[Any]
    val typeShapes = mutable.ArrayBuffer.empty[Any]
    // a shape may name further relations and types
    while rels + relShapes.length < tagOfIndex.length || types + typeShapes.length < typeOfIndex.length do
      while rels + relShapes.length < tagOfIndex.length do relShapes += relShape(tagOfIndex(rels + relShapes.length))
      while types + typeShapes.length < typeOfIndex.length do
        val t = typeOfIndex(types + typeShapes.length)
        typeShapes += Vector(t.name, t.displayName, canon(t.kind), canon(t.instanceOf))
    Vector(k, relShapes.toVector, typeShapes.toVector)

  private def relShape(t: Int): Vector[Any] =
    val r = prog.rels(t)
    val d = prog.directives(t)
    Vector(r.name, r.displayName, canon(r.kind), canon(r.cols), canon(r.result), canon(r.instanceOf), (d.open, d.input, d.output))

  private def rel(t: Int): Int = indexOfTag.getOrElseUpdate(t, { tagOfIndex += t; tagOfIndex.length - 1 })

  private def op(o: BodyOp): Any = o match
    case BodyOp.Scan(r, recIdx, asReg, binds, checks) =>
      ("scan", rel(r), recIdx, asReg, binds.toVector, checks.toVector.map((c, e) => (c, expr(e))))
    case BodyOp.Deref(src, r, binds, checks) => ("deref", src, rel(r), binds.toVector, checks.toVector.map((c, e) => (c, expr(e))))
    case BodyOp.Tag(src, ts) => ("tag", src, ts.map(rel))
    case BodyOp.Eval(dst, e) => ("eval", dst, expr(e))
    case BodyOp.Test(cmp, a, b) => ("test", cmp, expr(a), expr(b))
    case BodyOp.Lookup(dst, r, recIdx, args) => ("lookup", dst, rel(r), recIdx, args.toVector.map(expr))
    case BodyOp.NotIn(ops) => ("not", ops.toVector.map(op))
    case BodyOp.Agg(dst, kind, term, locals, ops) => ("agg", dst, kind, expr(term), locals.toVector, ops.toVector.map(op))

  private def expr(e: Expr): Any = e match
    case Expr.Reg(r) => ("reg", r)
    case Expr.Const(w) => ("const", word(w))
    case Expr.Arith(o, l, r) => ("arith", o, expr(l), expr(r))
    case Expr.Neg(x) => ("neg", expr(x))
    case Expr.Make(r, args) => ("make", rel(r), args.toVector.map(expr))

  private def word(w: Any): Any = w match
    case Id(r, n) => ("id", rel(r), n)
    case other => other

  /** A structural copy with relation and type symbols replaced by their indexes. */
  private def canon(x: Any): Any = x match
    case r: RelSym => tags.get(r).fold[Any](r)(t => ("rel", rel(t)))
    case t: TypeSym => ("type", typeIndex.getOrElseUpdate(t, { typeOfIndex += t; typeOfIndex.length - 1 }))
    case s: Set[?] => s.map(canon)
    case m: Map[?, ?] => m.map((k, v) => canon(k) -> canon(v))
    case s: Seq[?] => s.map(canon)
    case p: Product if p.productArity > 0 => (p.getClass, p.productIterator.map(canon).toVector)
    case other => other
