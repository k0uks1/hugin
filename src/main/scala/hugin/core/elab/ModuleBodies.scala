package hugin.core
package elab

import hugin.syntax.Trees
import hugin.syntax.Trees.*
import hugin.util.*

/** Module bodies `{ items }` (REDESIGN §6.7): record values whose object members are generative.
 *
 *  The declarations and definitions of a body are its *members*, elaborated in the context of the body
 *  (the enclosing variables, such as a functor's parameters) and of the members before them; each member
 *  is a variable of that context: an object constant `r : τ` is a variable of type `⇑τ` (as a functor's
 *  relation parameter is), a definition is let-bound. Members may be written in any order: one that
 *  refers to a later one is retried after it. The body's object items (rules, queries, directives,
 *  edges) are elaborated in the context of all members. The body's type is the record type of its
 *  members, a telescope, and its value is a record: evaluation creates fresh object constants for the
 *  object members of each instance ([[Modules]]), and the handover stages the instance's items. */
trait ModuleBodies:
  self: Elaborator =>
  import core.*

  def inferModuleBody(c: Cxt, body: Trees.ModuleBody): (Tm, Val, Stage) =
    val (memberItems, objectItems) = body.items.partition {
      case _: Decl | _: Def => true
      case _ => false
    }
    val (cb, members) = elabMembers(c, memberItems)
    recordBody(c, cb, body.span, members, memberItems)
    val items = objectItems.flatMap(item => reportingErrors(objectItem(cb, item)).getOrElse(Nil))
    val mb = hugin.core.ModuleBody(nextBodyId(), body.span, members, items)
    val ty = Tm.RecTy(members.map(m => (m.name, m.ty)), Nil, members.map(m => (m.span, m.declSpan)))
    (Tm.Module(mb, (0 until c.lvl).map(Tm.Var(_)).toList), ev(c, ty), Stage.S1)

  private def reportingErrors[A](a: => A): Option[A] =
    try Some(a)
    catch
      // a name the file declares later (a directive, a function): the definition is retried after it
      case e: ElabError if e.unresolved.exists(n => state.declaredHere(n) && lookupGlobal(n).isEmpty) => throw e
      case e: ElabError =>
        report(e)
        None

  /** Elaborates the members in dependency order (as the top level's declarations). */
  private def elabMembers(c: Cxt, items: List[Item]): (Cxt, List[Member]) =
    var cb = c
    val members = scala.collection.mutable.ListBuffer.empty[Member]
    var pending = items
    var progress = true
    while pending.nonEmpty && progress do
      val before = pending.length
      pending = pending.filter { item =>
        val later = pending.filter(_ ne item).flatMap(memberName).toSet
        try
          val (next, m) = undoOnFailure(member(cb, item))
          if members.exists(_.name == m.name) then duplicate(m, members.find(_.name == m.name).get)
          cb = next
          members += m
          false
        catch
          case e: ElabError =>
            if e.unresolved.exists(later) then true
            else
              report(e)
              false
      }
      progress = pending.length < before
    pending.foreach(item => reportingErrors(member(cb, item)))
    (cb, members.toList)

  private def duplicate(m: Member, first: Member): Nothing = fail(ElabProblem.DuplicateMember(m.name, m.span, first.span))

  private def memberName(item: Item): Option[Name] = item match
    case d: Decl => Some(d.name.name)
    case d: Def => Some(d.name.name)
    case _ => None

  /** One member, and the context extended with it. */
  private def member(c: Cxt, item: Item): (Cxt, Member) = item match
    case d: Decl if d.defn.isDefined && !isStructDecl(d) =>
      val (ty, tm) = declDefinition(c, d, d.defn.get)
      defined(c, d.name, ty, tm, d.span)
    case d: Def =>
      val (ty, tm) = definition(c, d.params, d.rhs)
      defined(c, d.name, ty, tm, d.span)
    case d: Decl => objectMember(c, d)
    case other => throw Impossible(s"not a member: $other")

  private def defined(c: Cxt, name: Ident, ty: Tm, tm: Tm, span: Span): (Cxt, Member) =
    val zty = zonk(c.env, c.lvl, ty)
    val ztm = zonk(c.env, c.lvl, tm)
    val tyV = ev(c, zty)
    (define(c, name.name, tyV, ev(c, ztm)), Member(name.name, MemberKind.Defined(ztm), zty, name.span, span))

  /** An object constant of the body: a variable of type `⇑τ`. */
  private def objectMember(c: Cxt, d: Decl): (Cxt, Member) =
    if d.sup.isDefined || d.params.nonEmpty then unsupportedAt(d.span, "refinements and families in module bodies")
    val (ty, decl) =
      if isStructDecl(d) then (structType(c, d), ObjDecl.Struct)
      else
        val (t, st) = declType(d, c)
        if st != Stage.S0 then unsupportedAt(d.span, "meta-level declarations without definition in module bodies")
        (t, objectDecl(d, ev(c, t)))
    val lifted = Tm.Lift(zonk(c.env, c.lvl, ty))
    (
      bind(c, d.name.name, ev(c, lifted), Stage.S1, BinderOrigin.Member),
      Member(d.name.name, MemberKind.Object(decl), lifted, d.name.span, d.span)
    )

  private def objectItem(c: Cxt, item: Item): List[CoreItem] = item match
    case r: Rule if isSpliceItem(r) => unsupportedAt(r.span, "reflected items (`$e.`) in module bodies")
    case r: Rule => List(ruleItem(c, r))
    case q: Query => List(queryItem(c, q))
    case d: Directive => directiveItems(c, d, inBody = true)
    case e: SubEdge => List(edgeItem(c, e))
    case other => unsupportedAt(other.span, "this item in a module body")
