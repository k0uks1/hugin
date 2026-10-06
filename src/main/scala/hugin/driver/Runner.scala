package hugin.driver

import hugin.util.*
import hugin.core.*
import hugin.runtime.*
import hugin.obj.{TypeOps, RelKind}

/** Runs a compiled program: loads input facts, evaluates, prints outputs and query answers. */
object Runner:
  final case class Result(output: List[String], truncated: Boolean, stats: List[ComponentStats])

  def run(c: Context, factFiles: List[SourceFile], budget: Option[Int], allRelations: Boolean = false): Option[Result] =
    val core = c.unit.core
    if core == null then return None
    val prog = core.nn
    val engine = Engine(prog, budget)
    val loader = FactLoader(engine, prog, TypeOps(c.unit.prog.nn), c.reporter)
    factFiles.foreach(loader.load)
    if c.reporter.hasErrors then return None
    engine.run()
    val out = List.newBuilder[String]
    if engine.truncated then
      val cut = engine.stats.filter(_.truncated).map(s => s"{${s.rels.mkString(", ")}}").mkString(", ")
      out += s"(* truncated: the round budget was exhausted in $cut; results are a subset *)"
    val explicit = prog.rels.filter(_.isOutput)
    val shown =
      if allRelations then prog.rels
      else if explicit.nonEmpty then explicit
      else if prog.queries.nonEmpty then Vector.empty
      else prog.rels.filter(r => r.kind == RelKind.Plain && !r.isInput)
    out ++= shown.flatMap(r => engine.facts(r.tag)).sorted
    for q <- prog.queries do
      out += (if q.source.span.exists then q.source.span.text.replaceAll("\\s+", " ") else hugin.obj.ObjPrinter.query(q.source))
      val as = engine.answers(q)
      if q.vars.isEmpty then out += (if as.nonEmpty then "yes." else "no.")
      else if as.isEmpty then out += "no."
      else
        out ++= as.map(a => q.vars.zip(a).map((v, w) => s"$v = ${engine.show(w)}").mkString(", ") + ".").sorted
    Some(Result(out.result(), engine.truncated, engine.stats.toList))
