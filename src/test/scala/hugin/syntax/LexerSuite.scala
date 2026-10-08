package hugin.syntax

import hugin.util.*

class LexerSuite extends munit.FunSuite:
  private def kinds(s: String): List[Tok] =
    Lexer(SourceFile.virtual("t", s), Reporter()).tokenize().map(_.kind).toList.dropRight(1)

  private def errors(s: String): List[String] =
    val r = Reporter()
    Lexer(SourceFile.virtual("t", s), r).tokenize()
    r.diagnostics.flatMap(_.code).map(_.id)

  test("a period after an identifier followed by a lowercase name is a selector") {
    assertEquals(kinds("g.edge"), List(Tok.Name, Tok.Select, Tok.Name))
    assertEquals(kinds("X.loc"), List(Tok.Var, Tok.Select, Tok.Name))
  }

  test("a period followed by whitespace or uppercase terminates the item") {
    assertEquals(kinds("p X."), List(Tok.Name, Tok.Var, Tok.Period))
    assertEquals(kinds("a. b"), List(Tok.Name, Tok.Period, Tok.Name))
    assertEquals(kinds("a.B"), List(Tok.Name, Tok.Period, Tok.Var))
  }

  test("`..` and floats") {
    assertEquals(kinds("{ .. }"), List(Tok.LBrace, Tok.DotDot, Tok.RBrace))
    assertEquals(kinds("1.5e3"), List(Tok.FloatLit))
    assertEquals(kinds("1."), List(Tok.IntLit, Tok.Period))
  }

  test("comments nest and count as whitespace") {
    assertEquals(kinds("a (* x (* y *) z *) b"), List(Tok.Name, Tok.Name))
    assertEquals(errors("a (* (* *)"), List("E0002"))
  }

  test("keywords, directives, rule names and multi-character symbols") {
    assertEquals(kinds("type not count"), List(Tok.KwType, Tok.KwNot, Tok.KwCount))
    assertEquals(kinds("%mode @r1"), List(Tok.Directive, Tok.RuleName))
    assertEquals(kinds(":- ?- -> <: <> <= >="), List(Tok.Turnstile, Tok.Query, Tok.Arrow, Tok.SubT, Tok.Neq, Tok.Le, Tok.Ge))
  }

  test("string escapes are decoded") {
    val t = Lexer(SourceFile.virtual("t", "\"a\\tb\\u{1F600}\\\"\""), Reporter()).tokenize().head
    assertEquals(t.value, "a\tb\uD83D\uDE00\"")
  }

  test("invalid escapes and unterminated strings are reported") {
    assertEquals(errors("\"\\q\""), List("E0003"))
    assertEquals(errors("\"abc"), List("E0002"))
    assertEquals(errors("\"\\u{D800}\""), List("E0003"))
  }
