package hugin.syntax

import hugin.util.*
import scala.collection.mutable

/** A reader for the common form of facts files (reference: object/io, "Input facts"): every item a fact
 *  `r a₁ … aₙ.` whose arguments are literals, names, parenthesised negative numbers and parenthesised
 *  constructor terms of the same form, with nothing else in the file but comments. It builds exactly the
 *  trees, with the same spans, that the program parser ([[Parser]]) builds for such a file, without its
 *  precedence climbing and recovery.
 *
 *  Anything else (a lexical error, another token, a token at the start of a line in column 0 inside an
 *  item, an integer out of range) makes it give up: [[read]] is `None` and the file is parsed by the
 *  program parser, which accepts the same language and reports its errors. So a facts file gets the
 *  diagnostics it always got, and the reader only decides how fast a well-formed one is read
 *  (docs/PERFORMANCE.md, "The rest of #60"). The two agree on every file the reader accepts:
 *  `FactReaderSuite` compares them on the facts files of the tests and the bench set and on mutated ones.
 *  (Soufflé likewise reads its input facts with a reader of their own, `ReadStreamCSV`, not with the
 *  Datalog parser; here the format stays Hugin's syntax, and the program parser stays the definition.) */
object FactReader:
  /** The items of `src`, if it is a facts file in the common form. */
  def read(src: SourceFile): Option[List[Trees.Item]] =
    val reporter = Reporter()
    val toks = Lexer(src, reporter).tokenize().toArray
    // (a slice's spans are not offsets into its content; facts files are never slices)
    if reporter.diagnostics.nonEmpty || src.isSlice then None else Reader(src, toks).items()

  /** Thrown when the file is not in the common form. */
  private final class GiveUp extends Exception(null, null, false, false)

  private final class Reader(src: SourceFile, toks: Array[Token]):
    private var i = 0

    /** Whether the token at `k` is the first of its line and in column 0 (`ParserBase.atColumn0`): it
     *  starts where a line starts (lines start after `\n`), and a token before it then lies on an earlier
     *  line. */
    private def atColumn0(k: Int): Boolean =
      val start = toks(k).span.start
      k > 0 && (start == 0 || src.content.charAt(start - 1) == '\n')

    private def giveUp(): Nothing = throw GiveUp()

    private def kind: Tok = toks(i).kind

    /** The next token, which must not start a line in column 0 (the program parser would end the item
     *  there and report it). */
    private def next(): Token =
      if atColumn0(i) then giveUp()
      val t = toks(i)
      i += 1
      t

    def items(): Option[List[Trees.Item]] =
      val out = mutable.ListBuffer.empty[Trees.Item]
      try
        while kind != Tok.EOF do out += fact()
        Some(out.toList)
      catch case _: GiveUp => None

    /** `r a₁ … aₙ.` */
    private def fact(): Trees.Item =
      val head = toks(i)
      if head.kind != Tok.Name then giveUp()
      i += 1
      val app = arguments(Trees.Ident(head.text)(head.span))
      if kind != Tok.Period then giveUp()
      val period = next()
      Trees.Rule(None, List(app), None)(Span(src, head.span.start, period.span.end))

    /** `f` applied to the arguments that follow. */
    private def arguments(f0: Tree): Tree =
      var f = f0
      while startsArgument do
        val a = argument()
        f = Trees.Apply(f, a)(f.span.to(a.span))
      f

    private def startsArgument: Boolean = kind match
      case Tok.IntLit | Tok.FloatLit | Tok.StrLit | Tok.Name | Tok.LParen => true
      case _ => false

    /** A literal, a name, `(-n)` or `(t a₁ … aₙ)`. */
    private def argument(): Tree =
      val t = next()
      t.kind match
        case Tok.LParen =>
          val inner =
            if kind == Tok.Minus then
              val minus = next()
              val lit = next()
              val negated = literal(lit) match
                case Literal.IntL(v) => Literal.IntL(-v)
                case Literal.FloatL(v) => Literal.FloatL(-v)
                case _ => giveUp()
              Trees.Lit(negated)(Span(src, minus.span.start, lit.span.end))
            else arguments(argument())
          if kind != Tok.RParen then giveUp()
          val close = next()
          Trees.Parens(inner)(Span(src, t.span.start, close.span.end))
        case Tok.Name => Trees.Ident(t.text)(t.span)
        case _ => Trees.Lit(literal(t))(t.span)

    private def literal(t: Token): Literal = (t.kind, t.value) match
      case (Tok.IntLit, v: Long) => Literal.IntL(v)
      case (Tok.FloatLit, v: Double) => Literal.FloatL(v)
      case (Tok.StrLit, v: String) => Literal.StrL(v)
      case _ => giveUp()
