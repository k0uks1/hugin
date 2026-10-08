package hugin.util.diagnostics

import com.google.gson.JsonParser
import hugin.util.{DiagnosticRenderer, SourceFile, Span}

/** The JSON writer and the encoding of diagnostics (`--error-format=json`); `tests/json` has the goldens. */
class JsonDiagnosticsSuite extends munit.FunSuite:
  test("strings are escaped so that any JSON parser reads them back") {
    val s = "quote \" backslash \\ newline \n tab \t bell \u0007 ü"
    val parsed = JsonParser.parseString(Json.obj("s" -> Json.str(s)).render).getAsJsonObject
    assertEquals(parsed.get("s").getAsString, s)
  }

  test("a diagnostic encodes code, level, 1-based spans, suggestions with applicability and the rendering") {
    val src = SourceFile.virtual("f.hgn", "p X :- q X Y.\n")
    val d = hugin.TestDiagnostics
      .warning(Code.W0002, "variable `Y` occurs only once in this rule", Span(src, 11, 12), "singleton variable")
      .withSuggestion("replace `Y` with `_`", Span(src, 11, 12), "_", Applicability.MachineApplicable)
    val rendered = DiagnosticRenderer(color = false).render(d)
    val o = JsonParser.parseString(JsonDiagnostics.encode(d, rendered).render).getAsJsonObject
    assertEquals(o.get("version").getAsInt, JsonDiagnostics.Version)
    assertEquals(o.getAsJsonObject("code").get("explanation").getAsString, "docs/errors/W0002.md")
    assertEquals(o.get("level").getAsString, "warning")
    val span = o.getAsJsonArray("spans").get(0).getAsJsonObject
    assertEquals((span.getAsJsonObject("start").get("line").getAsInt, span.getAsJsonObject("start").get("col").getAsInt), (1, 12))
    assertEquals(span.getAsJsonObject("end").get("col").getAsInt, 13)
    val s = o.getAsJsonArray("suggestions").get(0).getAsJsonObject
    assertEquals(s.get("applicability").getAsString, "MachineApplicable")
    assertEquals(o.get("rendered").getAsString, rendered)
  }
