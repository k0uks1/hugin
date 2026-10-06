package hugin
import hugin.util.*
import hugin.core.*
object Main:
  def main(args: Array[String]): Unit =
    val src = SourceFile.fromPath(java.nio.file.Path.of(args(0)))
    val c = driver.Compiler.compile(src, Settings(printAfter = args.drop(1).toSet), println)
    val rr = DiagnosticRenderer(false)
    c.reporter.sorted.foreach(d => println(rr.render(d)))
