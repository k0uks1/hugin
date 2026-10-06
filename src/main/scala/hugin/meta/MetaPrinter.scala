package hugin.meta

import hugin.obj.*

/** Prints elaborated meta programs with explicit quotes ⟨·⟩ and splices ~(·). */
object MetaPrinter:
  def showBody(m: MExpr, indent: String = ""): String = m match
    case MExpr.Body(items, _, _) => items.map(i => indent + showItem(i, indent)).mkString("\n")
    case other => indent + show(other, indent)

  def show(m: MExpr, indent: String): String = m match
    case MExpr.Body(_, _, _) => "{\n" + showBody(m, indent + "  ") + "\n" + indent + "}"
    case MExpr.Lam(p, b) => s"[${p.name}] ${show(b, indent)}"
    case MExpr.App(f, a, _) =>
      val fs = show(f, indent)
      val as = a match
        case _: MExpr.App | _: MExpr.Lam => s"(${show(a, indent)})"
        case _ => show(a, indent)
      s"$fs $as"
    case other => MExpr.show(other)

  def showItem(i: EItem, indent: String): String = i match
    case EItem.TypeDecl(s, TypeKindE.Open, _) => s"${s.name}${tps(s)} : type."
    case EItem.TypeDecl(s, TypeKindE.Refinement(b), _) => s"${s.name}${tps(s)} : type <: ${b.show}."
    case EItem.RelDecl(s, cols, res, isStruct, _) =>
      s"${s.name}${tps(s)} : ${(cols.map(ObjPrinter.column) :+ res.map(_.show).getOrElse("rel")).mkString(" -> ")}.${if isStruct then "  (* struct *)" else ""}"
    case EItem.EdgeDecl(sub, sup, _) => s"${sub.show} <: ${MExpr.show(sup)}."
    case EItem.MetaDef(s, rhs, _) => s"${s.name} : ${if s.mtype == null then "?" else s.mtype.nn.show} = ${show(rhs, indent)}."
    case EItem.RuleItem(r) => ObjPrinter.rule(r)
    case EItem.QueryItem(q) => ObjPrinter.query(q)
    case EItem.DirectiveItem(d) => ObjPrinter.directive(d)

  private def tps(s: Sym): String = if s.tparams.isEmpty then "" else s.tparams.mkString(" ", " ", "")
