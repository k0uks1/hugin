package hugin.core

import hugin.compiler.*
import hugin.util.Reporter

/** Phase: elaborate the program with the new meta level (REDESIGN §6): names, types, stages, implicit
 *  arguments, totality of meta functions; with the prelude and the imported files. */
final class ElaboratePhase extends Phase:
  def phaseName = "elaborate"
  def description = "elaborate the meta level: types, stages, implicit arguments, totality"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val reporter = Reporter()
    val root = u.source.path
    val program = u.untpd.nn
    val graph = ctx.libraries.graph(root, program, prelude = false)
    graph.diagnostics.foreach(ctx.report)
    u.missingImports ++= graph.missing
    val prelude = Option.when(ctx.settings.prelude)(Prelude.items(reporter)).flatten
    val libraries = qualified(graph.files).map((path, q) => SourceItems(path, q, parse(path, reporter)))
    u.elaborated = NewMeta.elaborate(SourceItems(root, "", program.items), prelude, libraries, reporter)
    reporter.diagnostics.foreach(ctx.report)

  /** The files with the qualifiers of their object constants: their names, numbered where they clash. */
  private def qualified(files: List[String]): List[(String, String)] =
    val taken = scala.collection.mutable.HashSet("", "prelude")
    files.map { path =>
      val base = Library.moduleName(path)
      path -> Iterator.from(1).map(k => if k == 1 then base else s"$base$k").find(taken.add).get
    }

  private def parse(path: String, reporter: Reporter)(using Context): List[hugin.syntax.Trees.Item] =
    ctx.libraries.load(path).fold(Nil)(p => hugin.syntax.Parser.parseMeta2(p.source, reporter).items)

  override def show(using Context): String =
    Option(ctx.unit.elaborated).fold("")(_.nn.render(Reporter()).mkString("\n"))

/** The prelude of the new meta level (`<stdlib>/prelude-core.hgn`, in its syntax). */
object Prelude:
  val path: String = SourceLoader.StdlibPrefix + "prelude-core.hgn"

  def items(reporter: Reporter): Option[SourceItems] =
    SourceLoader.stdlib(path).map { text =>
      SourceItems(path, "", hugin.syntax.Parser.parseMeta2(hugin.util.SourceFile.virtual(path, text), reporter).items)
    }

/** Phase: stage the object items and hand the object program over to the object level. */
final class StagePhase extends ObjProgramPhase:
  def phaseName = "stage"
  def description = "stage the object items (run the meta code they splice) and emit the object program"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.elaborated == null then return
    val reporter = Reporter()
    val e = u.elaborated.nn
    u.prog = handover.Handover(e.core, reporter).program(e.items)
    reporter.diagnostics.foreach(ctx.report)
