package hugin.ide

import hugin.query.{CompileKey, CompletionItem, Database, Ide, MetaIde}
import hugin.syntax.{Lexer, Tok}
import hugin.util.{Reporter, SourceFile}

/** What a completion candidate is. */
enum CandidateKind:
  case Directive, Variable, MetaParameter, Label, Relation, Constructor, Struct, ObjectType, BaseType, TypeDefinition, FormulaFunction,
    MetaDefinition, Other

  /** Whether candidates of this kind are object syntax, as written in a reflection quote. */
  def isObject: Boolean = this match
    case Relation | Constructor | Struct | ObjectType | BaseType | TypeDefinition | Variable | Label => true
    case _ => false

object CandidateKind:
  /** The kind of a candidate of [[hugin.query.Ide.completions]], by its description. */
  def of(kind: String): CandidateKind = kind match
    case "directive" => Directive
    case "variable" => Variable
    case "meta parameter" => MetaParameter
    case "label" => Label
    case "relation" => Relation
    case "constructor" => Constructor
    case "struct" => Struct
    case "object type" => ObjectType
    case "base type" => BaseType
    case "type definition" => TypeDefinition
    case "formula function" => FormulaFunction
    case "meta definition" => MetaDefinition
    case _ => Other

/** A completion candidate: the text to insert, what it is, a description, and whether its result fits
 *  the type expected where it is inserted. */
final case class Candidate(label: String, kind: CandidateKind, detail: String, fits: Boolean)

/** The candidates at a position, replacing the text from `from` (the identifier being typed) to the
 *  position. If `ranked`, the type expected there is known, and the candidates that fit it come first. */
final case class Completions(from: Int, items: List[Candidate], ranked: Boolean)

/** Completion. */
object Completion:
  /** Characters after which an editor should ask for completions: module members, labels, directives. */
  val triggers: List[String] = List(".", "{", "%")

  /** The compiler's candidates ([[hugin.query.Ide.completions]]) at an offset of the program `key`,
   *  adapted on the meta level: inside a reflection quote `'( … )` only object syntax (or, after `$`,
   *  meta values) is offered; where the elaborator knew the type expected at the name being typed, the
   *  variables in scope there are added and the candidates whose result type fits are marked. */
  def at(key: CompileKey, offset: Int)(using Database): Completions =
    if Files.isFacts(key.path) then Completions(offset, Nil, ranked = false)
    else
      val text = Files.source(key.path).content
      val start =
        Iterator.iterate(offset)(_ - 1).find(i => i <= 0 || !(text.charAt(i - 1).isLetterOrDigit || "_'".contains(text.charAt(i - 1)))).get
      val prefix = text.substring(start, offset.min(text.length))
      val base = Ide.completions(key, offset)
      val expected = if start > 0 && ".%{".contains(text.charAt(start - 1)) then None else MetaIde.expectedAt(key, key.path, start, offset)
      val locals = expected.toList.flatMap(_._2).filter(_._1.startsWith(prefix)).map((x, t) => CompletionItem(x, "meta parameter", t))
      val candidates = inQuote(text, start) match
        case Some(afterDollar) => (locals ++ base).filter(c => CandidateKind.of(c.kind).isObject != afterDollar)
        case None => locals ++ base
      val heads = expected.map(_ => MetaIde.headsByName(key)).getOrElse(Map.empty)
      val items = candidates.distinctBy(_.label).map { c =>
        val fits = expected.exists((head, _) => heads.getOrElse(c.label, Set.empty)(head) || locals.exists(_.label == c.label))
        Candidate(c.label, CandidateKind.of(c.kind), c.detail, fits)
      }
      Completions(start, items, ranked = expected.isDefined)

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
