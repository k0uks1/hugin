package hugin.runtime

import hugin.obj.{ArithOp, CmpOp, Rule, Query, RelSym}
import hugin.syntax.AggKind

/** Words (Section 9.1): literals (java.lang.Long, java.lang.Double, String) or identities. */
final case class Id(rel: Int, n: Int)

/** Which part of a relation a scan reads (Section 9.5). */
enum Version:
  case Full, Old, Delta

/** Expressions over registers. */
enum Expr:
  case Reg(r: Int)
  case Const(w: Any)
  case Arith(op: ArithOp, l: Expr, r: Expr)
  case Neg(e: Expr)
  /** Head construction of a nested fact (Make), possibly nested. */
  case Make(rel: Int, args: Array[Expr])

/** Body operations of the core IR (Section 9.3). Registers are slots of a per-rule register file. */
enum BodyOp:
  /** Iterate facts of `rel` (`recIdx` ≥ 0 for atoms of the current component, which get versions). */
  case Scan(rel: Int, recIdx: Int, asReg: Int, binds: Array[(Int, Int)], checks: Array[(Int, Expr)])
  /** `src` holds an identity: look up its tuple. */
  case Deref(src: Int, rel: Int, binds: Array[(Int, Int)], checks: Array[(Int, Expr)])
  case Tag(src: Int, tags: Set[Int])
  case Eval(dst: Int, e: Expr)
  case Test(op: CmpOp, a: Expr, b: Expr)
  /** Look up the identity of an existing fact (no interning). */
  case Lookup(dst: Int, rel: Int, args: Array[Expr])
  case NotIn(ops: Array[BodyOp])
  case Agg(dst: Int, kind: AggKind, term: Expr, locals: Array[Int], ops: Array[BodyOp])

/** A compiled rule: body operations followed by the head (Insert). */
final class CompiledRule(
    val source: Rule,
    val nregs: Int,
    val body: Array[BodyOp],
    val headRel: Int,
    val headArgs: Array[Expr],
    val recursiveAtoms: Int
)

final class CompiledQuery(
    val source: Query,
    val nregs: Int,
    /** One plan per alternative (projection expansion / disjunction). */
    val alternatives: Array[Array[BodyOp]],
    /** User variables and their register in each alternative. */
    val vars: List[String],
    val regs: Array[Array[Int]]
)

final class CoreProgram(
    val rels: Vector[RelSym],
    /** Components in evaluation order, as relation tags. */
    val components: Vector[Vector[Int]],
    val rules: Vector[CompiledRule],
    val queries: Vector[CompiledQuery],
    /** Bound-column sets per relation that need an index. */
    val indexes: Map[Int, Set[Vector[Int]]]
)

object CorePrinter:
  def expr(e: Expr, p: CoreProgram): String = e match
    case Expr.Reg(r) => s"r$r"
    case Expr.Const(w) => word(w)
    case Expr.Arith(op, l, r) => s"(${expr(l, p)} ${op.show} ${expr(r, p)})"
    case Expr.Neg(x) => s"-${expr(x, p)}"
    case Expr.Make(rel, as) => s"${p.rels(rel).name}(${as.map(expr(_, p)).mkString(", ")})"

  def word(w: Any): String = w match
    case s: String => hugin.syntax.Literal.quote(s)
    case d: java.lang.Double => hugin.syntax.Literal.showDouble(d)
    case other => other.toString

  def op(o: BodyOp, p: CoreProgram, ind: String): String = o match
    case BodyOp.Scan(rel, ri, asReg, binds, checks) =>
      val v = if ri >= 0 then s"<rec $ri>" else ""
      s"${ind}Scan ${if asReg >= 0 then s"r$asReg := " else ""}${p.rels(rel).name}$v${binds.map((k, r) => s" [$k := r$r]").mkString}${checks.map((k, e) => s" [$k == ${expr(e, p)}]").mkString}"
    case BodyOp.Deref(src, rel, binds, checks) =>
      s"${ind}Deref r$src ${p.rels(rel).name}${binds.map((k, r) => s" [$k := r$r]").mkString}${checks.map((k, e) => s" [$k == ${expr(e, p)}]").mkString}"
    case BodyOp.Tag(src, tags) => s"${ind}Tag r$src in {${tags.toList.sorted.map(p.rels(_).name).mkString(", ")}}"
    case BodyOp.Eval(dst, e) => s"${ind}Eval r$dst := ${expr(e, p)}"
    case BodyOp.Test(o, a, b) => s"${ind}Test ${expr(a, p)} ${o.show} ${expr(b, p)}"
    case BodyOp.Lookup(dst, rel, as) => s"${ind}Lookup r$dst := ${p.rels(rel).name}(${as.map(expr(_, p)).mkString(", ")})"
    case BodyOp.NotIn(ops) => s"${ind}NotIn {\n${ops.map(this.op(_, p, ind + "  ")).mkString("\n")}\n$ind}"
    case BodyOp.Agg(dst, k, t, _, ops) => s"${ind}Agg r$dst := ${k.show} { ${expr(t, p)} |\n${ops.map(this.op(_, p, ind + "  ")).mkString("\n")}\n$ind}"

  def show(p: CoreProgram): String =
    val sb = new StringBuilder
    sb ++= "(* components in evaluation order *)\n"
    for (c, i) <- p.components.zipWithIndex do sb ++= s"(* $i: ${c.map(p.rels(_).name).mkString(", ")} *)\n"
    for r <- p.rules do
      sb ++= s"rule ${r.source.name.map("@" + _).getOrElse("")} ${hugin.obj.ObjPrinter.rule(r.source)}\n"
      r.body.foreach(o => sb ++= op(o, p, "  ") += '\n')
      sb ++= s"  Insert ${p.rels(r.headRel).name}(${r.headArgs.map(expr(_, p)).mkString(", ")})\n"
    for q <- p.queries; (alt, i) <- q.alternatives.zipWithIndex do
      sb ++= s"query ${hugin.obj.ObjPrinter.query(q.source)}${if q.alternatives.length > 1 then s" (alternative ${i + 1})" else ""}\n"
      alt.foreach(o => sb ++= op(o, p, "  ") += '\n')
      sb ++= s"  Answer ${q.vars.zip(q.regs(i)).map((v, r) => s"$v = r$r").mkString(", ")}\n"
    sb.toString
