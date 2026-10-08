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

  /** The object constant (or family of them) that the object term `t` applies: the head of its spine, also
   *  through the splice of a family's application (`$(node ?A) L R`). */
  def objectHead(t: Tm): Option[Int] =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case Tm.Splice(f) => head(f)
      case other => other
    head(t) match
      case Tm.Global(id) => Some(id)
      case _ => None

  /** The data constructor or data struct that `t` (an object term, possibly at a position) applies. */
  def dataConstructorOf(t: Tm): Option[Int] = objectHead(t).filter(isData)

  def isData(id: Int): Boolean = declOf(id) match
    case Some(ObjDecl.Constructor(fact)) => !fact
    case Some(ObjDecl.Struct(fact)) => !fact
    case _ => false

  /** What an object constant or a family of them declares. */
  def declOf(id: Int): Option[ObjDecl] = globals(id).kind match
    case GlobalKind.Object(d) => Some(d)
    case GlobalKind.Family(d, _) => Some(d)
    case _ => None

  /** The label of a constructor field of a functor parameter that the object term `t` applies
   *  (`$(p.link) X`), if the parameter's signature does not require a fact constructor (`%fact link`). */
  def dataFieldOf(c: Cxt, t: Tm): Option[Name] =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case Tm.Splice(f) => f
      case other => other
    head(t) match
      case Tm.Proj(Tm.Var(ix), l) =>
        force(c.binder(c.lvl - ix - 1).ty) match
          case rt: Val.RecTy if !rt.reqs.contains(SigReq.Fact(l)) =>
            fieldType(rt, ev(c, Tm.Var(ix)), l).map(force).collect {
              case Val.Lift(ty) if !isRelationType(ty) && force(ty).isInstanceOf[Val.Pi] => l
            }
          case _ => None
      case _ => None

  /** E0406 for the constructor field `label` of a parameter, named `shown`, used as a relation. */
  def dataFieldUsedAsRelation(shown: String, label: Name, span: Span): Nothing =
    fail(ObjectProblem.DataFieldAsRelation(shown, label, span))

  /** E0406 for the data constructor `id` used as a relation at `span`. */
  def dataUsedAsRelation(id: Int, span: Span, label: String): Nothing =
    val g = globals(id)
    val what = g.kind match
      case GlobalKind.Object(ObjDecl.Struct(_)) => "data struct"
      case _ => "data constructor"
    val decl = Option.when(g.declSpan.exists)((g.declSpan, g.declSpan.text))
    val local = g.declSpan.exists && g.declSpan.source.path == span.source.path
    fail(ObjectProblem.DataAsRelation(g.name, what, label, span, g.span, decl, local))
