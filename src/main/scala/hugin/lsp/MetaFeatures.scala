package hugin.lsp

import com.google.gson.{JsonArray, JsonElement, JsonObject}
import hugin.compiler.MetaIndex.HintKind
import hugin.query.{CompileKey, Database, Expansion, MetaIde, Parse}
import hugin.syntax.{Lexer, Tok}
import hugin.util.{Diagnostic as HDiagnostic, Reporter, SourceFile, Span}
import hugin.util.diagnostics.Code
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either as JEither
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** Which inlay hints the server sends (initialization option and setting `inlayHints`): the conversions
 *  stage inference inserted (`staging`), inferred implicit arguments (`implicits`) and universe levels
 *  (`levels`). */
final case class HintSettings(staging: Boolean = true, implicits: Boolean = true, levels: Boolean = false):
  def kinds: Set[HintKind] =
    Set(HintKind.Staging -> staging, HintKind.Implicit -> implicits, HintKind.Level -> levels).collect { case (k, true) => k }

object HintSettings:
  /** The settings in a JSON object `{ "inlayHints": { "staging": …, … } }` (the client's initialization
   *  options, or its configuration under `hugin`); missing entries keep `current`'s. */
  def from(options: Any, current: HintSettings): HintSettings = options match
    case o: JsonObject =>
      val section = Option(o.get("hugin")).collect { case h: JsonObject => h }.getOrElse(o)
      Option(section.get("inlayHints")).collect { case h: JsonObject => h }.fold(current) { h =>
        def flag(name: String, default: Boolean) = Try(h.get(name).getAsBoolean).getOrElse(default)
        HintSettings(flag("staging", current.staging), flag("implicits", current.implicits), flag("levels", current.levels))
      }
    case _ => current

/** The meta-level features of the server (issue #54), in terms of the protocol: inlay hints, hover on
 *  the meta level, the structured data of typed holes, and the code actions of interactive development
 *  (split a pattern variable, add the missing clauses, start the clauses of a declared function). */
final class MetaFeatures(using db: Database):
  var hintSettings: HintSettings = HintSettings()

  private def key(path: String) = CompileKey(path)
  private def source(path: String): SourceFile = db(Parse, path).source

  // ---------------------------------------------------------------------------------------------- hover

  /** What hover adds on the meta level at an offset (nothing between tokens). */
  def hover(path: String, offset: Int): List[String] =
    val text = source(path).content
    def onToken(i: Int) = i >= 0 && i < text.length && !text.charAt(i).isWhitespace
    if onToken(offset) || onToken(offset - 1) then MetaIde.hover(key(path), offset) else Nil

  // ---------------------------------------------------------------------------------------- inlay hints

  def inlayHints(path: String, range: Range): List[InlayHint] =
    val src = source(path)
    val (from, to) = (Positions.offset(src, range.getStart), Positions.offset(src, range.getEnd))
    MetaIde.hints(key(path), path, from, to, hintSettings.kinds).map { h =>
      val hint = InlayHint(Positions.position(h.at.source, h.at.start), JEither.forLeft(h.label))
      hint.setTooltip(JEither.forLeft[String, MarkupContent](h.tooltip))
      h.kind match
        case HintKind.Implicit =>
          hint.setKind(InlayHintKind.Type)
          hint.setPaddingLeft(true)
        case HintKind.Level => hint.setKind(InlayHintKind.Type)
        case HintKind.Staging =>
      hint
    }

  // -------------------------------------------------------------------------------------- typed holes

  /** The goal of a hole reported by `d` (E0924), as the LSP diagnostic's `data`: `{ "goal", "name",
   *  "stage", "context": [{ "name", "type" }] }`, from the compilation of the document at `path`. */
  def goalData(path: String, d: HDiagnostic): Option[JsonElement] =
    val sp = d.primarySpan
    Option.when(d.code == Code.E0924 && sp.exists)(()).flatMap(_ => MetaIde.goalAt(key(path), sp.start, Some(sp.source.path))).map { g =>
      val o = JsonObject()
      o.addProperty("goal", g.tpe)
      g.name.foreach(o.addProperty("name", _))
      o.addProperty("stage", g.stage)
      val ctx = JsonArray()
      for (x, t) <- g.context do
        val v = JsonObject()
        v.addProperty("name", x)
        v.addProperty("type", t)
        ctx.add(v)
      o.add("context", ctx)
      o
    }

  // ------------------------------------------------------------------------------------- code actions

  /** The code actions of interactive development at an offset: split the pattern variable there, start
   *  the clauses of the function declared there, add the clauses missing from a function whose coverage
   *  error (E0911) is among `diagnostics`. */
  def codeActions(uri: String, path: String, from: Int, to: Int, diagnostics: List[(HDiagnostic, Diagnostic)]): List[CodeAction] =
    val k = key(path)
    val split = MetaIde.splitAt(k, from).flatMap(s => splitAction(uri, s))
    val skeleton = MetaIde.skeletonAt(k, from).filter(s => s.decl.source.path == path).map { s =>
      action(s"Add a clause for `${s.fn}`", CodeActionKind.QuickFix, uri, s.decl.endPoint, "\n" + s.clause)
    }
    val missing =
      for
        (d, lsp) <- diagnostics if d.code == Code.E0911
        m <- MetaIde.missingAt(k, d.primarySpan).toList if m.after.source.path == path
      yield
        val n = m.clauses.length
        val a = action(
          if n == 1 then "Add the missing clause" else s"Add the $n missing clauses",
          CodeActionKind.QuickFix,
          uri,
          m.after.endPoint,
          m.clauses.map("\n" + _).mkString
        )
        a.setDiagnostics(List(lsp).asJava)
        a.setIsPreferred(true)
        a
    val refine = MetaIde.goalAt(k, from).filter(_.span.source.path == path).toList.flatMap { g =>
      g.refinements.map(r =>
        action(s"Refine the hole with `${r.stripPrefix("(").stripSuffix(")")}`", CodeActionKind.RefactorRewrite, uri, g.span, r)
      )
    }
    missing ++ split.toList ++ skeleton.toList ++ refine

  private def action(title: String, kind: String, uri: String, at: Span, text: String): CodeAction =
    val a = CodeAction(title)
    a.setKind(kind)
    a.setEdit(WorkspaceEdit(Map(uri -> List(TextEdit(Positions.range(at), text)).asJava).asJava))
    a

  /** Replaces the clause by one clause per constructor, the variable replaced by the constructor's
   *  pattern where it is bound and where it is used. */
  private def splitAction(uri: String, s: hugin.compiler.MetaIndex.Split): Option[CodeAction] =
    Option.when(s.patterns.nonEmpty && s.clause.exists)(()).map { _ =>
      val text = s.clause.text
      val occurrences = Lexer(SourceFile.virtual("clause", text), Reporter()).tokenize().filter(t => t.kind == Tok.Var && t.text == s.name)
      val indent = " " * (s.clause.start - s.clause.source.lineStart(s.clause.source.lineOf(s.clause.start)))
      val clauses = s.patterns.map { p =>
        occurrences.foldRight(text)((t, acc) => acc.substring(0, t.span.start) + p + acc.substring(t.span.end))
      }
      action(s"Split on `${s.name}`", CodeActionKind.RefactorRewrite, uri, s.clause, clauses.mkString("\n" + indent))
    }

  // ---------------------------------------------------------------------------------------- expansion

  /** The staged result of the meta code at an offset ([[Expansion]]), as Hugin text. */
  def expansion(path: String, offset: Int): Option[String] = Expansion.render(key(path), offset)

  /** A lens "Show expansion" on every directive or functor application of the file that produced object
   *  items; it runs the client command `hugin.showExpansion` with the URI and position, which asks the
   *  server for the text with the command [[MetaFeatures.ExpansionCommand]]. */
  def codeLenses(uri: String, path: String): List[CodeLens] =
    Expansion.sites(key(path), path).map { (frame, n) =>
      val at = Positions.position(frame.span.source, frame.span.start)
      val args = List[Object](uri, Int.box(at.getLine), Int.box(at.getCharacter))
      CodeLens(
        Positions.range(frame.span),
        Command(s"Show expansion (${if n == 1 then "1 item" else s"$n items"})", "hugin.showExpansion", args.asJava),
        null
      )
    }

  // --------------------------------------------------------------------------------------- completion

  /** Type-directed completion: whether a candidate's result fits the type expected at the identifier
   *  being typed (from `start` to `offset`), and the variables in scope there, if the elaborator saw it. */
  def expected(path: String, start: Int, offset: Int): Option[(String, List[(String, String)])] =
    MetaIde.expectedAt(key(path), path, start, offset)

object MetaFeatures:
  /** The command (`workspace/executeCommand`) that returns the expansion at a position, with the
   *  arguments `[uri, line, character]` (0-based) or `[{ "uri", "position" }]`: the text, or null. */
  val ExpansionCommand = "hugin.expansion"

  /** The URI and position of the arguments of [[ExpansionCommand]]. */
  def positionArgs(args: List[Any]): Option[(String, Position)] =
    def str(a: Any) = a match
      case p: com.google.gson.JsonPrimitive if p.isString => Some(p.getAsString)
      case s: String => Some(s)
      case _ => None
    def num(a: Any) = a match
      case p: com.google.gson.JsonPrimitive if p.isNumber => Some(p.getAsInt)
      case n: Number => Some(n.intValue)
      case _ => None
    args match
      case List(u, l, c) => for uri <- str(u); line <- num(l); char <- num(c) yield (uri, Position(line, char))
      case List(o: JsonObject) =>
        Try {
          val p = o.getAsJsonObject("position")
          (o.get("uri").getAsString, Position(p.get("line").getAsInt, p.get("character").getAsInt))
        }.toOption
      case _ => None

  /** Whether a completion candidate (by its kind) is object syntax, as written in a quote. */
  def isObjectKind(kind: String): Boolean =
    Set("relation", "constructor", "struct", "object type", "base type", "type definition", "variable", "label")(kind)

  /** If `offset` is inside a reflection quote `'( … )`: whether the name there follows `$` (a hole, a meta
   *  value). */
  def inQuote(text: String, offset: Int): Option[Boolean] =
    val toks =
      Lexer(SourceFile.virtual("", text.substring(0, offset.min(text.length))), Reporter()).tokenize().filter(_.kind != Tok.EOF).toVector
    // the parentheses open at `offset`, each marked if it opens a quote `'(`
    val parens = scala.collection.mutable.Stack.empty[Boolean]
    for (t, i) <- toks.zipWithIndex do
      t.kind match
        case Tok.LParen => parens.push(i > 0 && toks(i - 1).kind == Tok.Quote)
        case Tok.RParen => if parens.nonEmpty then parens.pop()
        case _ =>
    Option.when(parens.contains(true)) {
      // the token before the name being typed (if any): `$` or `$..`
      val typing = toks.lastOption.exists(t => t.span.end == offset && (t.kind == Tok.Var || t.kind == Tok.Name))
      val prev = if typing then toks.dropRight(1).lastOption else toks.lastOption
      prev.exists(p => p.kind == Tok.Dollar || p.kind == Tok.DotDot)
    }
