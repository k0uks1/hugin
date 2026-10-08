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
    val decl = Option.when(g.declSpan.exists)((g.declSpan, g.declSpan.text))
    val local = g.declSpan.exists && g.declSpan.source.path == span.source.path
    fail(ObjectProblem.DataAsRelation(g.name, what, label, span, g.span, decl, local))
