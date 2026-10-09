package hugin.syntax

import hugin.util.*

/** The hand-written recursive-descent parser of Hugin (reference: lexical-structure, and the grammar
 *  productions of the chapters), assembled from the parts of the grammar:
 *
 *  - [[ParserBase]]: the token cursor, the `%infix` operators, error reporting;
 *  - [[ItemSyntax]]: programs and items; [[DirectiveSyntax]]: directives;
 *  - [[ExprSyntax]]: expressions by precedence climbing; [[RecordSyntax]]: braces (records, signatures,
 *    module bodies, implicit binders); [[QuoteSyntax]]: reflection (holes, lists, rules as expressions).
 *
 *  `docs/PARSER.md` describes the design. */
final class Parser(src: SourceFile, reporter: Reporter, infix: Option[Map[String, (Parser.Assoc, Int)]] = None)
    extends ParserBase(src, reporter)
    with ExprSyntax
    with RecordSyntax
    with QuoteSyntax
    with DirectiveSyntax
    with ItemSyntax:
  // the operators of the whole file, when this is a slice of it
  infixOps ++= infix.getOrElse(Operators.declared(toks))

object Parser:
  enum Assoc:
    case Left, Right, NonAssoc

  // Precedence levels (reference: lexical-structure, operators), scaled by 10; an operator declared with
  // `%infix assoc p name` gets level `10*p + 5`: it binds tighter than builtin level p and looser than p+1.
  val LvlSemi = 10
  val LvlComma = 20
  val LvlArrow = 30
  val LvlBar = 40

  /** `::`, the meta level's list constructor (right associative). */
  val LvlCons = 45
  val LvlCmp = 50

  /** Items' heads: everything binding tighter than comparisons. */
  val LvlHead = 51
  val LvlAdd = 60
  val LvlMul = 70

  def parse(src: SourceFile, reporter: Reporter): Trees.Program = Parser(src, reporter).parseProgram()

  /** The `%infix` operators of a file, which every part of it is parsed with. */
  def infixOperators(src: SourceFile): Map[String, (Assoc, Int)] =
    Operators.declared(Lexer(src, Reporter()).tokenize())

  /** Parses a slice of a file (its text from the start of a top-level item to its end) with the file's
   *  `%infix` operators: the items, if it parses without diagnostics. */
  def parseSlice(src: SourceFile, infix: Map[String, (Assoc, Int)]): Option[List[Trees.Item]] =
    val reporter = Reporter()
    val program = Parser(src, reporter, Some(infix)).parseProgram()
    Option.when(reporter.diagnostics.isEmpty)(program.items)

/** The `%infix` operators declared in a file. They are in effect in the whole file, also before their
 *  directive (reference: lexical-structure, user-defined infix operators), so they are collected from
 *  the tokens before parsing: every `%infix assoc p name` (wherever it is written; a malformed one is
 *  reported when its item is parsed). */
object Operators:
  def declared(toks: Vector[Token]): Map[String, (Parser.Assoc, Int)] =
    // a loop over the directives, not a window per token: facts files have hundreds of thousands of
    // tokens (docs/PERFORMANCE.md, "After #80–#87")
    val out = Map.newBuilder[String, (Parser.Assoc, Int)]
    var i = 0
    while i + 3 < toks.length do
      val d = toks(i)
      if d.kind == Tok.Directive && d.text == "%infix" then
        val (a, p, n) = (toks(i + 1), toks(i + 2), toks(i + 3))
        if a.kind == Tok.Name && p.kind == Tok.IntLit && n.kind == Tok.Name then
          val assoc = a.text match
            case "left" => Some(Parser.Assoc.Left)
            case "right" => Some(Parser.Assoc.Right)
            case "none" => Some(Parser.Assoc.NonAssoc)
            case _ => None
          val prec = p.value match
            case l: Long => l.toInt
            case _ => 0
          assoc.foreach(as => out += n.text -> (as, prec * 10 + 5))
      i += 1
    out.result()
