package hugin.lsp

import hugin.compiler.{SemanticIndex, Sym, SymKind}
import hugin.compiler.MetaIndex.Role
import hugin.syntax.{Lexer, Tok, Token}
import hugin.util.{Reporter, SourceFile, Span}
import org.eclipse.lsp4j.{SemanticTokenModifiers, SemanticTokenTypes, SemanticTokens}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** Semantic tokens: what the semantic index knows about names (declarations, references, object
 *  variables), classified by level, and the meta level's own syntax, from the tokens of the file:
 *  directives `%d`, the delimiters of reflection quotes `'{ … }`, splices and quote holes `$`, `$..`,
 *  lifts `⇑` and typed holes `?`.
 *
 *  Types tell what a name is (a relation, an object or meta constructor, a meta function, an inductive
 *  family, …); the modifiers `meta` and `object` tell its level, `declaration` its declaration and
 *  `defaultLibrary` a name of the prelude. */
object Tokens:
  /** Token types of the legend; a token's type is its index. The first eight are those of the first
   *  servers, in the same order. */
  val types: List[String] = List(
    SemanticTokenTypes.Namespace, // 0 modules, functors, signatures (meta)
    SemanticTokenTypes.Type, // 1 object types, type definitions, base types
    SemanticTokenTypes.Struct, // 2 structs
    SemanticTokenTypes.Function, // 3 relations
    SemanticTokenTypes.EnumMember, // 4 constructors (object or meta: see the modifiers)
    SemanticTokenTypes.Macro, // 5 formula functions (expanded hygienically)
    SemanticTokenTypes.Parameter, // 6 meta parameters and local meta variables
    SemanticTokenTypes.Variable, // 7 object variables, meta constants
    SemanticTokenTypes.Decorator, // 8 directives `%d`
    SemanticTokenTypes.Keyword, // 9 the delimiters of reflection quotes `'{` `}`
    SemanticTokenTypes.Operator, // 10 splices and quote holes `$`, `$..`, lifts `⇑`
    SemanticTokenTypes.Method, // 11 meta functions
    SemanticTokenTypes.Class, // 12 meta inductive families
    "label" // 13 typed holes `?`, `?name`
  )

  val modifiers: List[String] = List(SemanticTokenModifiers.Declaration, "meta", "object", SemanticTokenModifiers.DefaultLibrary)

  private val Declaration = 1
  private val Meta = 2
  private val Object = 4
  private val Library = 8

  /** The type and modifiers of a symbol (without `declaration`). */
  private def classify(ix: SemanticIndex, s: Sym): (Int, Int) =
    val lib = if s.span.exists && s.span.source.path.startsWith(hugin.compiler.SourceLoader.StdlibPrefix) then Library else 0
    val (tpe, level) = s.kind match
      case SymKind.ObjType | SymKind.TypeDef | SymKind.BaseType => (1, Object)
      case SymKind.Struct => (2, Object)
      case SymKind.Rel => (3, Object)
      case SymKind.Ctor => (4, Object)
      case SymKind.FormulaFn => (5, Meta)
      case SymKind.MetaParam => (6, Meta)
      case SymKind.MetaDef =>
        ix.meta.roleOf(s) match
          case Some(Role.Function) => (11, Meta)
          case Some(Role.Family) => (12, Meta)
          case Some(Role.Constructor) => (4, Meta)
          case Some(Role.Value) => (7, Meta)
          case Some(Role.Module) | None => (0, Meta)
    (tpe, level | lib)

  private final case class Tok_(span: Span, tpe: Int, mods: Int, priority: Int)

  /** The tokens of a program file, encoded relative to the previous token as the protocol requires. */
  def of(ix: SemanticIndex, source: SourceFile, path: String): SemanticTokens =
    def inFile(sp: Span) = sp.exists && sp.source.path == path
    val decls = ix.symbols.filter(s => inFile(s.span) && s.span.text == s.name).map { s =>
      val (t, m) = classify(ix, s)
      Tok_(s.span, t, m | Declaration, 1)
    }
    val uses = ix.references.filter(r => inFile(r.span) && r.span.text == r.sym.name).map { r =>
      val (t, m) = classify(ix, r.sym)
      Tok_(r.span, t, m, 0)
    }
    val vars = ix.variables.filter(v => inFile(v.span) && v.span.text == v.display).map(v => Tok_(v.span, 7, Object, 0))
    val tokens = (lexical(source) ++ decls ++ uses ++ vars).sortBy(t => (t.span.start, -t.priority, -(t.mods & Declaration)))
    val data = mutable.ArrayBuffer.empty[Integer]
    var prevLine = 0
    var prevChar = 0
    var prevEnd = -1
    for t <- tokens if t.span.start >= prevEnd && t.span.end > t.span.start do
      val pos = Positions.position(t.span.source, t.span.start)
      val line = pos.getLine
      val char = pos.getCharacter
      // a token does not span lines (`'{` and `$..` never do)
      val length = (t.span.end - t.span.start).min(t.span.source.lineText(line).length - char)
      data ++= List(line - prevLine, if line == prevLine then char - prevChar else char, length, t.tpe, t.mods).map(Int.box)
      prevLine = line
      prevChar = char
      prevEnd = t.span.end
    SemanticTokens(data.asJava)

  /** The meta level's syntax, from the tokens of the file: these come first at their positions. */
  private def lexical(source: SourceFile): List[Tok_] =
    val toks = Lexer(source, Reporter()).tokenize().toVector
    val out = mutable.ListBuffer.empty[Tok_]
    // the braces opened by `'{`, to find the `}` that closes each quote
    val braces = mutable.Stack.empty[Boolean]
    def next(i: Int): Option[Token] = toks.lift(i + 1)
    for (t, i) <- toks.zipWithIndex do
      t.kind match
        case Tok.Directive => out += Tok_(t.span, 8, Meta, 2)
        case Tok.Quote =>
          next(i).filter(_.kind == Tok.LBrace).foreach(b => out += Tok_(t.span.to(b.span), 9, Meta, 2))
        case Tok.LBrace => braces.push(i > 0 && toks(i - 1).kind == Tok.Quote)
        case Tok.RBrace => if braces.nonEmpty && braces.pop() then out += Tok_(t.span, 9, Meta, 2)
        case Tok.Dollar =>
          val span = next(i).filter(n => n.kind == Tok.DotDot && n.span.start == t.span.end).fold(t.span)(n => t.span.to(n.span))
          out += Tok_(span, 10, Meta, 2)
        case Tok.Up => out += Tok_(t.span, 10, Meta, 2)
        case Tok.Hole => out += Tok_(t.span, 13, Meta, 2)
        case _ =>
    out.toList
