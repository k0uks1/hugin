package hugin.compiler

import hugin.cli.Main
import hugin.query.{Database, EagerStdlib, ProgramKey, SourceText, StdChain}
import hugin.syntax.Program
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The lazy re-export of the prelude ([[LazyStdlib]], issue #61): which files of the prelude's chain a
 *  program elaborates, the check that a lazy file declares no object constants, and a differential test
 *  of lazy against eager compilation. */
class LazyStdlibSuite extends munit.FunSuite:
  private val Demand = SourceLoader.StdlibPrefix + "std/demand.hgn"
  private val Reflect = SourceLoader.StdlibPrefix + "std/reflect.hgn"

  private def program(text: String, path: String = "p.hgn"): (String, Program) =
    path -> Parsed(hugin.util.SourceFile.virtual(path, text)).program

  private def chain(texts: String*): List[String] =
    val others = texts.toList.zipWithIndex.map((t, i) => program(t, s"f$i.hgn"))
    LazyStdlib.chain(StdlibCache.bundledChain(), others, builtinNames = true).map(_.source.path)

  test("a program that does not use `demand` leaves out `std/demand`") {
    assertEquals(chain("edge : int -> int -> rel.\nedge 1 2."), List(Reflect, SourceLoader.PreludePath))
  }

  test("a program that may use `demand` elaborates `std/demand`") {
    val uses = List(
      "p : int -> rel.\n%demand p +.", // the directive
      "d = demand.", // the name
      "p : int -> rel.\n%demnd p +.", // a name the unknown name's diagnostic suggests it for
      "m = %import \"std/demand\".", // an import of the file
      "%use \"std/demand\"."
    )
    for text <- uses do assertEquals(chain(text), List(Reflect, Demand, SourceLoader.PreludePath), text)
    assertEquals(chain("p : int -> rel.", "q : int -> rel.\n%demand q +."), List(Reflect, Demand, SourceLoader.PreludePath))
  }

  test("a name that is not similar enough does not count") {
    assertEquals(chain("dem : int -> rel.\nDemand : int -> rel."), List(Reflect, SourceLoader.PreludePath))
  }

  test("a file is lazy only if the prelude opens it selectively, and nothing else imports it") {
    val text = SourceLoader.stdlib(SourceLoader.PreludePath).get.replace("%use \"std/demand\" (demand).", "%use \"std/demand\".")
    val std = StdlibCache.bundledChain(text)
    assertEquals(LazyStdlib.chain(std, List(program("p : int -> rel.")), builtinNames = true), std)
  }

  test("`std/demand` declares no object constants; `std/reflect` does (shared data)") {
    val std = StdlibCache.bundledChain()
    assert(!StdlibCache.declaresObjects(std.take(1), std(1), builtinNames = true))
    assert(StdlibCache.declaresObjects(Nil, std.head, builtinNames = true))
  }

  test("object constants, rules and module instances make a file eager") {
    val std = StdlibCache.bundledChain()
    def declares(text: String) =
      StdlibCache.declaresObjects(std.take(1), Parsed(hugin.util.SourceFile.virtual("<stdlib>/std/t.hgn", text)), builtinNames = true)
    assert(!declares("%use \"std/reflect\".\nf : int -> int.\nf X = X + 1.\nl : list int = [1].\n"))
    assert(declares("node : type.\n"))
    assert(declares("edge : int -> int -> rel.\n"))
    assert(declares("p : int -> rel.\np 1.\n"))
    assert(declares("m : { x : int } = { x = 1 }.\n"))
    assert(declares("m = { x = 1 }.\n"))
    assert(declares("f : int -> int.\nf X = X.\n%f 1.\n"))
    assert(declares("f : int -> unknown_type.\n")) // an error: elaborated eagerly, so that it is reported
  }

  test("the query database leaves `std/demand` out until the program uses it, and keeps it when eager") {
    given db: Database = Database()
    val key = ProgramKey("p.hgn", prelude = true)
    db.set(SourceText, "p.hgn", "p : int -> rel.\np 1.\n")
    assertEquals(db(StdChain, key), List(Reflect, SourceLoader.PreludePath))
    db.set(SourceText, "p.hgn", "p : int -> rel.\np 1.\n%demand p +.\n")
    assertEquals(db(StdChain, key), List(Reflect, Demand, SourceLoader.PreludePath))
    db.set(SourceText, "p.hgn", "p : int -> rel.\np 1.\n")
    db.set(EagerStdlib, (), true)
    assertEquals(db(StdChain, key), List(Reflect, Demand, SourceLoader.PreludePath))
  }

  private def goldens: List[Path] =
    List("run", "neg").flatMap { d =>
      Files.list(Path.of("tests", d)).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList
    }.sortBy(_.toString)

  /** Exit code, standard output and diagnostics of `hugin run`, lazily or eagerly. */
  private def run(p: Path, lazily: Boolean): (Int, String, String) =
    val facts = Path.of(p.toString.stripSuffix(".hgn") + ".facts")
    val flags = Path.of(p.toString.stripSuffix(".hgn") + ".flags")
    val extra = if Files.exists(flags) then Files.readString(flags).trim.split("\\s+").filter(_.nonEmpty).toList else Nil
    val args = List("run", p.toString) ++ (if Files.exists(facts) then List("--facts", facts.toString) else Nil) ++ extra :+ "--no-color"
    val before = LazyStdlib.enabled
    LazyStdlib.enabled = lazily
    try
      val out = StringBuilder()
      val err = StringBuilder()
      val code = Main.run(args, s => out ++= s += '\n', s => err ++= s += '\n')
      (code, out.toString, err.toString)
    finally LazyStdlib.enabled = before

  test("lazy compilations give exactly the output of eager ones") {
    // every 5th golden program, and every one that mentions `demand`
    val sample = goldens.zipWithIndex.collect { case (p, i) if i % 5 == 0 || Files.readString(p).contains("demand") => p }
    for p <- sample do assertEquals(run(p, lazily = true), run(p, lazily = false), p.toString)
  }
