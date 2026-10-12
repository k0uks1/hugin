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
    s.idle().get()
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
    // the most general missing patterns, `_` first (reference: meta/coverage, "Missing cases")
    assertEquals(edit(add), (Range(pos(text, "M.", 2), pos(text, "M.", 2)), "\nboth _ 0 = ?.\nboth 0 _ = ?."))
    // the diagnostic shows the first of them and the number of the others
    assert(d.getMessage.contains("missing: `both _ 0` and 1 more"), d.getMessage)
  }

  test("#186 P3: split a pattern variable of a `match` branch: one branch per constructor") {
    val text = nat + "pred : nat -> nat.\npred M = match M with\n  | N => suc N.\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "N =>")).find(_.getTitle == "Split on `N`").get
    assertEquals(split.getKind, CodeActionKind.RefactorRewrite)
    assertEquals(edit(split), (Range(pos(text, "| N"), pos(text, "N.", 1)), "| zero => suc zero\n  | (suc N1) => suc (suc N1)"))
  }

  test("#186 P7b: split a derivation into the rules of its relation; the goal in the judgment notation") {
    val text = "%use \"std/graph\".\n%use \"std/semantics\".\n" +
      "toTc : {x y : G.node} -> tc G ⊢ path x y -> tc G ⊢ path x y.\ntoTc P = ?.\n" +
      "edgeIn : {x y : G.node} -> tc G ⊢ G.edge x y -> tc G ⊢ G.edge x y.\nedgeIn E = ?.\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "P = ?")).find(_.getTitle == "Split on `P`").get
    // the rules of `path` by their names, not `given` (`path` has rules); premises named by their relations
    assertEquals(edit(split)._2, "toTc (path.1 E) = ?.\ntoTc (path.2 E P) = ?.")
    // a relation without rules: only `given`
    val edge = actions(s, pos(text, "E = ?")).find(_.getTitle == "Split on `E`").get
    assertEquals(edit(edge)._2, "edgeIn (given I) = ?.")
    val goal = hover(s, pos(text, "?.\nedgeIn"))
    assert(goal.contains("`tc G ⊢ path x y`"), goal)
    // the declaration's anonymous database is not written (#186 P7c)
    assert(!goal.contains("⊢["), goal)
  }

  test("#186 P9b: a coerced atom shows its judgment in hovers and goals; a split below it offers the rules") {
    val text = "%use \"std/graph\".\n%use \"std/semantics\".\n" +
      "toTc : {x y : G.node} -> (tc G).path x y -> (tc G).path x y.\ntoTc P = ?.\n"
    val (s, _) = server(text)
    val atom = hover(s, pos(text, "(tc G).path x y ->"))
    assert(atom.contains("tc G ⊢ path x y"), atom)
    val goal = hover(s, pos(text, "?."))
    assert(goal.contains("`tc G ⊢ path x y`"), goal)
    val split = actions(s, pos(text, "P = ?")).find(_.getTitle == "Split on `P`").get
    assertEquals(edit(split)._2, "toTc (path.1 E) = ?.\ntoTc (path.2 E P) = ?.")
  }

  test("#186 P9d: a split offers every head of a rule: `edge.1`, `edge.2`; a label for its rule's one head") {
    val text = "%use \"std/graph\".\n%use \"std/semantics\".\n" +
      "both (g : graph) = {\n  edge : g.node -> g.node -> rel.\n  edge X Y, edge Y X :- g.edge X Y.\n}.\n" +
      "flip : {x y : G.node} -> both G ⊢ edge x y -> both G ⊢ edge y x.\nflip P = ?.\n" +
      "twice (g : graph) = {\n  from : g.node -> rel.\n  to : g.node -> rel.\n" +
      "  @ends from X, to Y :- g.edge X Y.\n  to Y :- from Y.\n}.\n" +
      "arrives : {y : G.node} -> twice G ⊢ to y -> twice G ⊢ to y.\narrives T = ?.\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "P = ?")).find(_.getTitle == "Split on `P`").get
    assertEquals(edit(split)._2, "flip (edge.1 E) = ?.\nflip (edge.2 E) = ?.")
    // `to`'s heads are numbered on their own; the label names the one head of `to` of its rule
    val to = actions(s, pos(text, "T = ?")).find(_.getTitle == "Split on `T`").get
    assertEquals(edit(to)._2, "arrives (ends E) = ?.\narrives (to.2 F) = ?.")
  }

  test("#186 P9c: a stratum-local split names the negated premise and offers `given`; the goal in the notation") {
    val text = "%use \"std/semantics\".\n%use \"std/strata\".\ncity : type. berlin, paris : city.\n" +
      "m = {\n  node : city -> rel.\n  bad : city -> rel.\n  node berlin. bad paris.\n  ok : city -> rel.\n" +
      "  ok X :- node X, not bad X.\n}.\n" +
      "same : {x : city} -> m ⊢ ok x -> m ⊢ ok x.\nsame P = ?.\n"
    val (s, _) = server(text)
    val split = actions(s, pos(text, "P = ?")).find(_.getTitle == "Split on `P`").get
    assertEquals(edit(split)._2, "same (ok.1 N N1) = ?.\nsame (given I) = ?.")
    val goal = hover(s, pos(text, "?."))
    assert(goal.contains("⊢ ok x`"), goal)
  }

  test("#186 P3: add the missing branches of a `match`, and hover in a branch") {
    val text = nat + "isZero : nat -> nat.\nisZero M = match M with\n  | zero => suc zero.\n"
    val (s, c) = server(text)
    val d = c.published(uri).find(_.getCode.getLeft == "E0911").get
    assert(d.getMessage.contains("missing: `_ + 1`"), d.getMessage)
    val add = actions(s, d.getRange.getStart, List(d)).find(_.getTitle.startsWith("Add the")).get
    assertEquals(edit(add), (Range(pos(text, "zero.", 4), pos(text, "zero.", 4)), "\n  | _ + 1 => ?"))
    assert(hover(s, pos(text, "suc zero.")).contains("`suc` : `nat -> nat`"), hover(s, pos(text, "suc zero.")))
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
    s.idle().get()
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
