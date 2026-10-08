package hugin.core
package elab

import hugin.util.*

/** Data constructors (constructors and structs not declared `%fact`) build values, which are not facts of
 *  a relation: using one as a relation (in a body atom, a rule head or a directive) is E0406. This is the
 *  data/fact split of the current object level, which REDESIGN step C3 removes (every constructor becomes
 *  a fact constructor); until then the core reports it where the old typer did. */
trait DataConstructors:
  self: Elaborator =>
  import core.*

  /** The data constructor or data struct that `t` (an object term, possibly at a position) applies. */
  def dataConstructorOf(t: Tm): Option[Int] =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case other => other
    head(t) match
      case Tm.Global(id) if isData(id) => Some(id)
      case _ => None

  def isData(id: Int): Boolean = globals(id).kind match
    case GlobalKind.Object(ObjDecl.Constructor(fact)) => !fact
    case GlobalKind.Object(ObjDecl.Struct(fact)) => !fact
    case _ => false

  /** E0406 for the data constructor `id` used as a relation at `span`. */
  def dataUsedAsRelation(id: Int, span: Span, label: String): Nothing =
    val g = globals(id)
    val what = g.kind match
      case GlobalKind.Object(ObjDecl.Struct(_)) => "data struct"
      case _ => "data constructor"
    var d = Diagnostic.error("E0406", s"$what `${g.name}` used as a relation", span, label)
      .withNote(s"`${g.name}` is a $what: it builds values, which are not facts of a relation")
    if g.span.exists then d = d.withLabel(g.span, s"declared here as a $what")
    val factWhat = what.replace("data", "fact")
    if g.declSpan.exists && g.declSpan.source.path == span.source.path then
      val text = g.declSpan.text
      val shown = if text.contains('\n') then s"%fact ${g.name} : ..." else s"%fact $text"
      d = d.withHelp(s"declare `${g.name}` as a $factWhat to read its facts: `$shown`")
        .withSuggestion("declare it with `%fact`", g.declSpan.startPoint, "%fact ")
    else if g.declSpan.exists then
      d = d.withHelp(s"`${g.name}` is declared in another file; declare a fact constructor of your own with `%fact` to read its facts")
    else d = d.withHelp(s"declare `${g.name}` with `%fact` to read its facts")
    fail(d)
