package hugin.reference

/** The Hugin code blocks of a page of the language reference (`reference/src/**/*.md`).
 *
 *  A block is a fence whose info string starts with `hugin`, followed by attributes separated by commas
 *  or spaces (the conventions of rustdoc and mdBook):
 *
 *   - ` ```hugin ` compiles without errors;
 *   - ` ```hugin,ignore ` is not checked (fragments, syntax schemata);
 *   - ` ```hugin,compile_fail,E0603 ` reports `E0603` as its first error;
 *   - ` ```hugin,run ` compiles, runs and prints exactly the following ` ```output ` block.
 *
 *  A ` ```facts ` block right after a `hugin` block is loaded as its input facts (before the
 *  ` ```output ` block of a `run` example). See `reference/README.md`. */
object CodeBlocks:
  enum Mode:
    case Compile, Ignore, Run
    case CompileFail(code: String)

  /** A Hugin example at `line` (1-based) of its page. */
  final case class Example(line: Int, program: String, mode: Mode, facts: Option[String], output: Option[String])

  /** A fence: its info string, body and the line of its opening ` ``` `. */
  private final case class Fence(line: Int, info: String, body: String):
    def lang: String = words.headOption.getOrElse("")
    def words: List[String] = info.split("[,\\s]+").toList.filter(_.nonEmpty)

  private val fence = "(?ms)^```([^\\n]*)\\n(.*?)^```[ \\t]*$".r
  private val code = "[EW]\\d{4}".r

  private def fences(text: String): List[Fence] =
    fence.findAllMatchIn(text).toList.map { m =>
      Fence(text.substring(0, m.start).count(_ == '\n') + 1, m.group(1).trim, m.group(2))
    }

  /** The examples of a page, or the problems with their attributes. */
  def examples(text: String): Either[List[String], List[Example]] =
    val fs = fences(text)
    val results = fs.zipWithIndex.collect {
      case (f, i) if f.lang == "hugin" =>
        val following = fs.drop(i + 1).takeWhile(_.lang != "hugin")
        val facts = following.headOption.filter(_.lang == "facts").map(_.body)
        val output = following.take(2).find(_.lang == "output").map(_.body)
        mode(f).map(m => Example(f.line, f.body, m, facts, output)).flatMap { e =>
          if e.mode == Mode.Run && e.output.isEmpty then Left(s"line ${f.line}: `hugin,run` needs an ```output block after it")
          else Right(e)
        }
    }
    val problems = results.collect { case Left(p) => p }
    if problems.nonEmpty then Left(problems) else Right(results.collect { case Right(e) => e })

  private def mode(f: Fence): Either[String, Mode] =
    f.words.drop(1) match
      case Nil => Right(Mode.Compile)
      case List("ignore") => Right(Mode.Ignore)
      case List("run") => Right(Mode.Run)
      case List("compile_fail", c) if code.matches(c) => Right(Mode.CompileFail(c))
      case _ =>
        Left(s"line ${f.line}: unknown attributes `${f.info}` (expected hugin, hugin,ignore, hugin,run or hugin,compile_fail,<code>)")
