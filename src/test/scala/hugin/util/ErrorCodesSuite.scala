package hugin.util

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The catalog of `hugin explain` lists exactly the codes the compiler can emit. */
class ErrorCodesSuite extends munit.FunSuite:
  private val codePattern = "\"([EW]\\d{4})\"".r

  private def emitted: Set[String] =
    val sources = Files.walk(Path.of("src/main/scala")).iterator.asScala
      .filter(p => p.toString.endsWith(".scala") && !p.endsWith("ErrorCodes.scala"))
    sources.flatMap(p => codePattern.findAllMatchIn(Files.readString(p)).map(_.group(1))).toSet

  test("every emitted code is explained, and every explained code is emitted") {
    val catalog = ErrorCodes.all.map(_._1).toSet
    assertEquals(emitted -- catalog, Set.empty[String], "emitted but not in the catalog")
    assertEquals(catalog -- emitted, Set.empty[String], "in the catalog but never emitted")
  }

  test("codes are unique and sorted by phase") {
    val codes = ErrorCodes.all.map(_._1)
    assertEquals(codes.distinct, codes)
    assertEquals(codes.filter(_.startsWith("E")), codes.filter(_.startsWith("E")).sorted)
  }
