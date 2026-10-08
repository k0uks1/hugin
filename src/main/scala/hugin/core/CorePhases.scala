package hugin.core

import hugin.compiler.*
import hugin.util.Reporter

/** Phase: elaborate the program with the meta level (REDESIGN §6): names, types, stages, implicit
 *  arguments, totality of meta functions; with the prelude and the imported files (loaded here, in
 *  dependency order; missing and cyclic imports are E0108). */
final class ElaboratePhase extends Phase:
  def phaseName = "elaborate"
  def description = "load the prelude and imported files; elaborate the meta level: types, stages, implicit arguments"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val reporter = Reporter()
    val root = u.source.path
    val program = u.untpd.nn
    val graph = ctx.libraries.graph(root, program, ctx.settings.prelude)
    graph.diagnostics.foreach(ctx.report)
    u.missingImports ++= graph.missing
    graph.files.foreach(p => u.libraries(p) = Library(p))
    val (preludes, imported) = graph.files.partition(_ == SourceLoader.PreludePath)
    val prelude = preludes.headOption.map(p => SourceItems(p, "", items(p)))
    val libraries = qualified(imported).map((path, q) => SourceItems(path, q, items(path)))
    val builtinNames = ctx.settings.prelude
    u.elaborated = MetaLevel.elaborate(SourceItems(root, "", program.items), prelude, libraries, reporter, builtinNames, u.index)
    reporter.diagnostics.foreach(ctx.report)

  /** The files with the qualifiers of their object constants: their names, numbered where they clash. */
  private def qualified(files: List[String]): List[(String, String)] =
    val taken = scala.collection.mutable.HashSet("", "prelude")
    files.map { path =>
      val base = Library.moduleName(path)
      path -> Iterator.from(1).map(k => if k == 1 then base else s"$base$k").find(taken.add).get
    }

  private def items(path: String)(using Context): List[hugin.syntax.Trees.Item] =
    ctx.libraries.load(path).fold(Nil)(_.program.items)

  override def show(using Context): String =
    Option(ctx.unit.elaborated).fold("")(_.nn.render(Reporter()).mkString("\n"))

/** Phase: stage the object items and hand the object program over to the object level. */
final class StagePhase extends ObjProgramPhase:
  def phaseName = "stage"
  def description = "stage the object items (run the meta code they splice) and emit the object program"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.elaborated == null then return
    val reporter = Reporter()
    val e = u.elaborated.nn
    val h = handover.Handover(e.core, reporter, u.index)
    u.prog = h.program(e.items)
    u.requirements = h.requirements
    reporter.diagnostics.foreach(ctx.report)
