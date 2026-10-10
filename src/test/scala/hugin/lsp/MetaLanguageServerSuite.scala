package hugin.lsp

import org.eclipse.lsp4j.*
import scala.jdk.CollectionConverters.*

/** The meta-level features of the server (issue #54) on in-memory documents: what the transcripts
 *  `tests/lsp/meta_*` show, asserted precisely, and their robustness in files with errors. */
class MetaLanguageServerSuite extends munit.FunSuite:
  private val uri = "untitled:m.hgn"

  private def pos(text: String, needle: String, shift: Int = 0): Position =
    Positions.position(hugin.util.SourceFile.virtual("", text), text.indexOf(needle) + shift)

  private def server(text: String, options: Object = null): (HuginLanguageServer, RecordingClient) =
    val s = HuginLanguageServer()
    val c = RecordingClient()
    s.connect(c)
    val init = InitializeParams()
    init.setInitializationOptions(options)
    s.initialize(init).get()
    s.getTextDocumentService.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "hugin", 1, text)))
    (s, c)

  private def hover(s: HuginLanguageServer, at: Position): String =
    Option(s.getTextDocumentService.hover(HoverParams(TextDocumentIdentifier(uri), at)).get()).fold("")(_.getContents.getRight.getValue)

  private def actions(s: HuginLanguageServer, at: Position, diagnostics: List[Diagnostic] = Nil): List[CodeAction] =
    s.getTextDocumentService
      .codeAction(CodeActionParams(TextDocumentIdentifier(uri), Range(at, at), CodeActionContext(diagnostics.asJava)))
      .get().asScala.map(_.getRight).toList

  private def edit(a: CodeAction): (Range, String) =
    val e = a.getEdit.getChanges.get(uri).asScala.loneElement
    (e.getRange, e.getNewText)

  private val nat = "nat : Type.\nzero : nat.\nsuc : nat -> nat.\n"

  test("hover: the type and stage of an expression, the elaborated term with its implicit arguments") {
    val text = "ident : A -> A = [x] x.\nthree : int = ident 3.\ncode : ⇑int = 4.\n"
    val (s, _) = server(text)
    assert(hover(s, pos(text, " 3", 1)).endsWith("`3` : `int`  \nstage: meta"))
    assertEquals(hover(s, pos(text, "4.")), "`4` : `⇑int`  \nstage: meta, object code `⇑int`\n\nelaborated: `⟨4⟩`")
    assert(hover(s, pos(text, "x] x", 3)).startsWith("```hugin\nparameter x : A\n```"))
  }

  test("hover on a typed hole: its goal and the variables in scope; the goal is the diagnostic's data") {
    val text = nat + "double : nat -> nat.\ndouble N = suc ?d.\n"
    val (s, c) = server(text)
    assertEquals(hover(s, pos(text, "?d")), "**goal** `?d` : `nat` (meta level)\n\n```hugin\nN : nat\n```")
    val d = c.published(uri).loneElement
    assertEquals(d.getCode.getLeft, "E0924")
    val data = d.getData.asInstanceOf[com.google.gson.JsonObject]
    assertEquals(data.get("goal").getAsString, "nat")
    assertEquals(data.getAsJsonArray("context").get(0).getAsJsonObject.get("name").getAsString, "N")
  }

  test("refine a hole with the constructors of its goal; hover on the head of an application") {
    val text = nat + "double : nat -> nat.\ndouble N = ?.\nident : A -> A = [x] x.\nthree : int = ident 3.\n"
    val (s, _) = server(text)
    val refine = actions(s, pos(text, "?")).filter(_.getTitle.startsWith("Refine")).map(a => (a.getTitle, edit(a)._2))
    assertEquals(refine, List(("Refine the hole with `zero`", "zero"), ("Refine the hole with `suc ?`", "(suc ?)")))
    assert(hover(s, pos(text, "ident 3")).contains("`ident` : `int -> int`  \nstage: meta\n\nelaborated: `ident {int}`"))
  }

  test("split a pattern variable: one clause per constructor, the variable replaced where it is used") {
    val text = nat + "double : nat -> nat.\ndouble N = suc (suc N).\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "N = suc")).find(_.getTitle == "Split on `N`").get
    assertEquals(split.getKind, CodeActionKind.RefactorRewrite)
    assertEquals(edit(split)._2, "double zero = suc (suc zero).\ndouble (suc N1) = suc (suc (suc N1)).")
  }

  test("split an indexed family: only the constructors whose indices unify") {
    val text = nat + "vec : Type -> nat -> Type.\nvnil : vec A zero.\nvcons : A -> vec A N -> vec A (suc N).\n" +
      "head : vec A (suc N) -> A.\nhead V = ?.\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "V = ?")).find(_.getTitle == "Split on `V`").get
    assertEquals(edit(split)._2, "head (vcons V1 V2) = ?.")
  }

  test("add the missing clauses: every case the coverage checker found, with holes") {
    val text = nat + "both : nat -> nat -> nat.\nboth (suc M) (suc N) = M.\n"
    val (s, c) = server(text)
    val d = c.published(uri).find(_.getCode.getLeft == "E0911").get
    val add = actions(s, d.getRange.getStart, List(d)).find(_.getTitle.startsWith("Add the")).get
    assert(add.getIsPreferred)
    assertEquals(edit(add), (Range(pos(text, "M.", 2), pos(text, "M.", 2)), "\nboth 0 _ = ?.\nboth (_ + 1) 0 = ?."))
    // the diagnostic itself is unchanged: the first missing case
    assert(d.getMessage.contains("missing: `both 0 _`"), d.getMessage)
  }

  test("start the clauses of a declared function") {
    val text = nat + "size : nat -> int.\n"
    val (s, _) = server(text)
    val start = actions(s, pos(text, "size")).find(_.getTitle == "Add a clause for `size`").get
    assertEquals(edit(start)._2, "\nsize N = ?.")
  }

  test("inlay hints follow the initialization options and the configuration") {
    val text = "ident : A -> A = [x] x.\nthree : int = ident 3.\nk : Type = int.\n"
    val (s, _) = server(text, com.google.gson.JsonParser.parseString("""{"inlayHints": {"levels": true}}"""))
    def labels() =
      s.getTextDocumentService.inlayHint(InlayHintParams(TextDocumentIdentifier(uri), Range(Position(0, 0), Position(9, 0))))
        .get().asScala.map(_.getLabel.getLeft).toList
    assertEquals(labels(), List("{int}", "₀"))
    val settings = com.google.gson.JsonParser.parseString("""{"hugin": {"inlayHints": {"implicits": false}}}""")
    s.getWorkspaceService.didChangeConfiguration(DidChangeConfigurationParams(settings))
    assertEquals(labels(), List("₀"))
  }

  test("completion: the candidates whose result fits the expected type first, with the variables in scope") {
    val text = nat + "size : nat -> int.\nsize zero = 0.\nsize (suc M) = 1.\nquad : nat -> nat.\nquad Nat = s.\n"
    val (s, _) = server(text)
    val items = s.getTextDocumentService.completion(CompletionParams(TextDocumentIdentifier(uri), pos(text, "= s.", 3)))
      .get().getLeft.asScala.toList
    val best = items.filter(i => Option(i.getPreselect).exists(_.booleanValue)).map(_.getLabel)
    assert(best.contains("suc"), best)
    assert(!best.contains("size"), best)
  }

  test("an error in one meta function does not stop hover, completion and tokens elsewhere") {
    val text = nat + "bad : nat -> nat.\nbad (suc N) = N.\nloop : nat -> nat.\nloop N = loop N.\n" +
      "broken : nat = suc (.\nfine : nat = suc zero.\n"
    val (s, c) = server(text)
    val codes = c.published(uri).map(_.getCode.getLeft).toSet
    assert(Set("E0911", "E0912").subsetOf(codes), codes)
    assert(hover(s, pos(text, "suc zero.")).contains("`suc` : `nat -> nat`"))
    val tokens = s.getTextDocumentService.semanticTokensFull(SemanticTokensParams(TextDocumentIdentifier(uri))).get().getData
    assert(tokens.size > 0)
  }

  extension [A](xs: Iterable[A])
    private def loneElement: A =
      assertEquals(xs.size, 1, xs)
      xs.head
