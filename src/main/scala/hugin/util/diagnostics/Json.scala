package hugin.util.diagnostics

/** A minimal JSON value with a compact, deterministic writer (fields keep their order). */
enum Json:
  case Obj(fields: List[(String, Json)])
  case Arr(items: List[Json])
  case Str(s: String)
  case Num(n: Long)
  case Bool(b: Boolean)
  case Null

  def render: String =
    val sb = StringBuilder()
    write(sb)
    sb.toString

  /** An indented rendering, also deterministic: an object or array that fits in `width` columns stays on
   *  one line (with a space after `:` and `,`), larger ones put each member on its own line. */
  def pretty(width: Int = 100): String =
    val sb = StringBuilder()
    writePretty(sb, 0, width)
    sb.toString

  private def writePretty(sb: StringBuilder, indent: Int, width: Int): Unit =
    def members(open: Char, close: Char, items: List[(Option[String], Json)]): Unit =
      sb += open += '\n'
      for ((k, v), i) <- items.zipWithIndex do
        if i > 0 then sb ++= ",\n"
        sb ++= " " * (indent + 2)
        k.foreach { key =>
          Json.quote(sb, key); sb ++= ": "
        }
        v.writePretty(sb, indent + 2, width)
      sb += '\n' ++= " " * indent += close
    oneLine(width - indent) match
      case Some(s) => sb ++= s
      case None =>
        this match
          case Obj(fs) => members('{', '}', fs.map((k, v) => (Some(k), v)))
          case Arr(xs) => members('[', ']', xs.map((None, _)))
          case _ => sb ++= render

  /** The one-line rendering of [[pretty]], if it has at most `max` characters (computed only up to that). */
  private def oneLine(max: Int): Option[String] =
    val sb = StringBuilder()
    def go(j: Json): Boolean =
      j match
        case Obj(fs) =>
          sb += '{'
          fs.iterator.zipWithIndex.forall { case ((k, v), i) =>
            if i > 0 then sb ++= ", "
            Json.quote(sb, k)
            sb ++= ": "
            go(v)
          } && { sb += '}'; sb.length <= max }
        case Arr(xs) =>
          sb += '['
          xs.iterator.zipWithIndex.forall { (x, i) =>
            if i > 0 then sb ++= ", "
            go(x)
          } && { sb += ']'; sb.length <= max }
        case other =>
          other.write(sb)
          sb.length <= max
    if go(this) then Some(sb.toString) else None

  private def write(sb: StringBuilder): Unit = this match
    case Obj(fs) =>
      sb += '{'
      for ((k, v), i) <- fs.zipWithIndex do
        if i > 0 then sb += ','
        Json.quote(sb, k)
        sb += ':'
        v.write(sb)
      sb += '}'
    case Arr(xs) =>
      sb += '['
      for (x, i) <- xs.zipWithIndex do
        if i > 0 then sb += ','
        x.write(sb)
      sb += ']'
    case Str(s) => Json.quote(sb, s)
    case Num(n) => sb ++= n.toString
    case Bool(b) => sb ++= b.toString
    case Null => sb ++= "null"

object Json:
  def obj(fields: (String, Json)*): Json = Obj(fields.toList)
  def str(s: String): Json = Str(s)
  def num(n: Long): Json = Num(n)

  private[diagnostics] def quote(sb: StringBuilder, s: String): Unit =
    sb += '"'
    s.foreach {
      case '"' => sb ++= "\\\""
      case '\\' => sb ++= "\\\\"
      case '\n' => sb ++= "\\n"
      case '\r' => sb ++= "\\r"
      case '\t' => sb ++= "\\t"
      case c if c < ' ' => sb ++= f"\\u${c.toInt}%04x"
      case c => sb += c
    }
    sb += '"'
