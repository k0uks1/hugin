package hugin.util.diagnostics

/** A segment of a message: prose, or program text (rendered in code style). */
enum Seg:
  case Text(s: String)

  /** Source code: names, directives, terms. Rendered in backticks (bold in a terminal). */
  case Code(s: String)

  /** A printed type. Rendered like code. */
  case Type(s: String)

/** Program text that is not a symbol, interpolated in code style: `msg"remove ${Src("%partial")}"`. */
final case class Src(text: String)

/** Prose computed at run time, interpolated as plain text. Interpolating a bare `String` does not compile,
 *  so every argument says whether it is code or prose. */
final case class Lit(text: String)

/** A structured message: what call sites build with `msg"…"` and what renderers turn into text.
 *  [[plain]] is the text form, with code in backticks. */
final case class Msg(segs: Vector[Seg]):
  def plain: String = segs.map {
    case Seg.Text(s) => s
    case Seg.Code(s) => s"`$s`"
    case Seg.Type(s) => s"`$s`"
  }.mkString

  def isEmpty: Boolean = segs.forall {
    case Seg.Text(s) => s.isEmpty
    case _ => false
  }
  def nonEmpty: Boolean = !isEmpty
  def ++(that: Msg): Msg = Msg(segs ++ that.segs)
  override def toString: String = plain

object Msg:
  val empty: Msg = Msg(Vector.empty)

  /** A value interpolated into `msg"…"`: anything with a [[DiagArg]] instance converts to it. (The
   *  conversion is found because `Msg` is the prefix of `Msg.Arg`, so its givens are in implicit scope.) */
  opaque type Arg = Vector[Seg]

  given [A](using d: DiagArg[A]): Conversion[A, Arg] = a => d.segs(a)
  extension (a: Arg) private[diagnostics] def segments: Vector[Seg] = a

  /** A message from text that may contain backticked code, split into segments (see [[parseText]]). */
  def text(s: String): Msg = Msg(parseText(s))

  /** The messages joined by `sep` (prose). */
  def join(ms: Iterable[Msg], sep: String): Msg =
    ms.foldLeft((empty, true)) { case ((acc, first), m) => (if first then m else acc ++ text(sep) ++ m, false) }._1

  /** Splits prose on backticks: text between a pair of backticks becomes a [[Seg.Code]]. A part with an
   *  odd number of backticks is kept as text, so [[Msg.plain]] always reproduces the input exactly. */
  def parseText(s: String): Vector[Seg] =
    if s.isEmpty then Vector.empty
    else if s.count(_ == '`') % 2 != 0 then Vector(Seg.Text(s))
    else
      s.split("`", -1).toVector.zipWithIndex.flatMap { (part, i) =>
        if i % 2 == 1 then Vector(Seg.Code(part)) else if part.isEmpty then Vector.empty else Vector(Seg.Text(part))
      }

/** How a value appears in a message. Instances for compiler types (symbols, types) live with those types'
 *  phases, so that this package does not depend on them. */
trait DiagArg[-A]:
  def segs(a: A): Vector[Seg]

object DiagArg:
  /** An instance rendering a value as one segment. */
  def apply[A](f: A => Seg): DiagArg[A] = a => Vector(f(a))

  given DiagArg[Int] = DiagArg(n => Seg.Text(n.toString))
  given DiagArg[Long] = DiagArg(n => Seg.Text(n.toString))
  given DiagArg[Src] = DiagArg(c => Seg.Code(c.text))
  given DiagArg[Lit] = DiagArg(l => Seg.Text(l.text))
  given DiagArg[Msg] = _.segs

extension (sc: StringContext)
  /** A structured message. Literal parts are prose in which backticked text is code; arguments render
   *  through their [[DiagArg]] instance, so a bare `String` does not compile. Escapes are processed as by
   *  `s"…"`.
   *
   *  Each argument is converted to [[Msg.Arg]] by a given `Conversion`, so a file interpolating arguments
   *  needs `import scala.language.implicitConversions` (Scala 3.3 has no `into` parameters yet); the
   *  `*Problems.scala` inventories import it. */
  def msg(args: Msg.Arg*): Msg =
    val parts = sc.parts.map(p => Msg.parseText(StringContext.processEscapes(p)))
    val segs = parts.head ++ args.zip(parts.tail).flatMap((a, p) => a.segments ++ p)
    Msg(segs.toVector)
