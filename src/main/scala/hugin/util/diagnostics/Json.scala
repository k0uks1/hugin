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

  private def quote(sb: StringBuilder, s: String): Unit =
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
