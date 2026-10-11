package hugin.cli

import hugin.cli.Highlight.{Run, Snippet}
import hugin.query.Database
import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets.UTF_8

/** `hugin highlight`: the runs of a snippet cover its text, carry the language server's semantic tokens
 *  and lexical classes for the rest, also when the snippet does not compile. */
class HighlightSuite extends munit.FunSuite:
  private def runs(code: String, prelude: Boolean = true): List[Run] =
    given Database = Database()
    Highlight.runs(Snippet(code, prelude))

  /** The classes of the first run with this text. */
  private def classes(rs: List[Run], text: String): List[String] =
    rs.find(_.text == text).map(_.classes).getOrElse(fail(s"no run `$text` in $rs"))

  private val program =
    """(* roads *)
      |city : type.
      |berlin : city.
      |road : city -> city -> rel.
      |road X Y :- road Y X.
      |label : city -> string -> int -> rel.
      |label berlin "a" 42.
      |?- road berlin C.
      |""".stripMargin

  test("the runs cover the text exactly") {
    val rs = runs(program)
    assertEquals(rs.map(_.text).mkString, program)
  }

  test("semantic tokens: declarations, references, variables, by level") {
    val rs = runs(program)
    assertEquals(classes(rs, "city"), List("type", "declaration", "object"))
    assertEquals(
      rs.filter(_.text == "road").map(_.classes).distinct.sortBy(_.size),
      List(List("function", "object"), List("function", "declaration", "object"))
    )
    assertEquals(classes(rs, "X"), List("variable", "object"))
    assertEquals(classes(rs, "berlin"), List("enumMember", "declaration", "object"))
  }

  test("library names carry defaultLibrary") {
    val rs = runs("p : int -> rel.\np 1.\n")
    assertEquals(classes(rs, "int"), List("type", "object", "defaultLibrary"))
  }

  test("lexical classes: comments, strings, numbers, keywords, operators") {
    val rs = runs(program)
    assertEquals(classes(rs, "(* roads *)"), List("comment"))
    assertEquals(classes(rs, "\"a\""), List("string"))
    assertEquals(classes(rs, "42"), List("number"))
    assertEquals(classes(rs, "type"), List("keyword"))
    assertEquals(classes(rs, ":-"), List("operator"))
    assertEquals(classes(rs, "->"), List("operator"))
  }

  test("a snippet that does not compile keeps its lexical classes and the semantic tokens recovered") {
    val code = "city : type.\nroad : city -> town -> rel.\nroad X Y :- road X Y Z.\n"
    val rs = runs(code)
    assertEquals(rs.map(_.text).mkString, code)
    assertEquals(classes(rs, "city"), List("type", "declaration", "object"))
    assert(classes(rs, "X").startsWith(List("variable")))
    // a fragment: no declarations at all
    val fragment = runs("p X :- q X, not r X.")
    assertEquals(classes(fragment, "not"), List("keyword"))
    assertEquals(classes(fragment, "X"), List("variable"))
  }

  test("the command reads snippets from stdin and writes their runs as JSON") {
    val out = StringBuilder()
    val in = ByteArrayInputStream("""[{"code": "x : type.\n"}, {"code": "%builtin int.", "prelude": false}]""".getBytes(UTF_8))
    assertEquals(Main.run(List("highlight"), out ++= _, _ => (), in), ExitCode.Ok)
    val json = out.toString
    assert(json.startsWith("[[[\"x\",[\"type\",\"declaration\",\"object\"]]"), json)
    assert(json.contains("[\"%builtin\",[\"decorator\",\"meta\"]]"), json)
    val bad = ByteArrayInputStream("{}".getBytes(UTF_8))
    assertEquals(Main.run(List("highlight"), _ => (), _ => (), bad), ExitCode.Usage)
  }

  test("--info: each snippet's runs with their names, the names' hovers, groups and definitions") {
    val code = "%use \"std/graph\".\ncity : type.\nroad : city -> city -> rel.\n%input road.\nroads = tc { node = city, edge = road }.\n"
    val snippets = s"""[{"code": ${com.google.gson.JsonPrimitive(code)}}, {"code": "p X :- q X, not r X."}]"""
    val out = StringBuilder()
    assertEquals(Main.run(List("highlight", "--info"), out ++= _, _ => (), ByteArrayInputStream(snippets.getBytes(UTF_8))), ExitCode.Ok)
    val all = com.google.gson.JsonParser.parseString(out.toString).getAsJsonArray
    assertEquals(all.size, 2)
    val first = all.get(0).getAsJsonObject
    val runs = first.getAsJsonArray("runs").asList.toArray.toList.map(_.asInstanceOf[com.google.gson.JsonArray])
    assertEquals(runs.map(_.get(0).getAsString).mkString, code)
    val names = first.getAsJsonArray("names")
    val hovers = first.getAsJsonArray("hovers")
    def name(text: String, n: Int = 0) =
      names.get(runs.filter(r => r.get(0).getAsString == text && r.size == 3)(n).get(2).getAsInt).getAsJsonObject
    // a use of `road`: the declaration's offset, the declaration's group, a hover with the signature
    val decl = name("road")
    val use = name("road", 2)
    assert(decl.get("decl").getAsBoolean)
    assert(!use.get("decl").getAsBoolean)
    assertEquals(use.get("group"), decl.get("group"))
    assertEquals(use.get("target").getAsInt, code.indexOf("road :"))
    assertEquals(hovers.get(use.get("hover").getAsInt).getAsJsonArray.get(0).getAsString, "relation road : city -> city -> rel")
    // a library name: module and name
    assertEquals(name("tc").get("target").toString, "[\"std/graph\",\"tc\"]")
    // a fragment that does not compile: its runs, no names
    val fragment = all.get(1).getAsJsonObject
    assertEquals(fragment.getAsJsonArray("names").size, 0)
    assert(fragment.getAsJsonArray("runs").size > 0)
  }

  test("highlight is not listed in the usage") {
    assert(!CommandLine.usage.contains("highlight"), CommandLine.usage)
    assert(!CommandLine.usage.contains("--info"), CommandLine.usage)
  }
