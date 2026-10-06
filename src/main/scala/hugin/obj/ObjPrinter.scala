package hugin.obj

import hugin.meta.MExpr

/** Printer for object programs (outputs of the object-level phases). */
object ObjPrinter:
  def term(t: Term): String = t match
    case Term.Var(n) => Var.display(n)
    case Term.Lit(l) => l.show
    case Term.App(r, Nil) => r.show
    case Term.App(r, as) => (r.show :: as.map(arg)).mkString(" ")
    case Term.As(x, v) => s"(${term(x)} as $v)"
    case Term.Ascr(x, tp) => s"(${term(x)} : ${tp.show})"
    case Term.Proj(v, l) => s"${arg(v)}.$l"
    case Term.With(v, fs) => s"(${term(v)} with ${fs.map((l, t, _) => s"$l = ${term(t)}").mkString("{ ", ", ", " }")})"
    case Term.Arith(op, l, r) => s"${arith(l)} ${op.show} ${arith(r)}"
    case Term.Neg(x) => s"-${arg(x)}"
    case Term.Splice(m) => s"~(${MExpr.show(m)})"

  def arg(t: Term): String = t match
    case Term.App(_, _ :: _) | Term.Arith(_, _, _) => s"(${term(t)})"
    case _ => term(t)

  private def arith(t: Term): String = t match
    case Term.Arith(_, _, _) => s"(${term(t)})"
    case _ => arg(t)

  def formula(f: Formula): String = f match
    case Formula.Atom(r, as, None) => (r.show :: as.map(arg)).mkString(" ")
    case Formula.Atom(r, as, Some(v)) => s"(${(r.show :: as.map(arg)).mkString(" ")} as $v)"
    case Formula.Cmp(op, l, r) => s"${term(l)} ${op.show} ${term(r)}"
    case Formula.Not(a) => s"not ${if a.as.isEmpty && a.args.nonEmpty then "(" + formula(a) + ")" else formula(a)}"
    case Formula.Agg(res, k, t, b) => s"$res = ${k.show} { ${term(t)} | ${body(b)} }"
    case Formula.Disj(alts) => alts.map(body).mkString("(", " ; ", ")")
    case Formula.Splice(m) => s"~(${MExpr.show(m)})"

  def body(b: List[Formula]): String = if b.isEmpty then "true" else b.map(formula).mkString(", ")

  def rule(r: Rule): String =
    val n = r.name.map(x => s"@$x ").getOrElse("")
    val hs = r.heads.map(term).mkString(", ")
    if r.body.isEmpty then s"$n$hs." else s"$n$hs :- ${body(r.body)}."

  def query(q: Query): String = s"?- ${body(q.body)}."

  def column(c: Column): String = c.label match
    case Some(l) => s"($l : ${c.tpe.show})"
    case None => c.tpe match
        case OType.Union(_) => s"(${c.tpe.show})"
        case _ => c.tpe.show

  def relDecl(r: RelSym): String =
    val res = r.result.map(_.show).getOrElse("rel")
    val tps = if r.tparams.isEmpty then "" else r.tparams.mkString(" [", " ", "]")
    val kind = r.kind match
      case RelKind.Struct => "  (* struct *)"
      case RelKind.Demand(c, m) => s"  (* demand of ${c.name} at ${m.show} *)"
      case RelKind.Derivation(rn) => s"  (* derivations of @$rn *)"
      case RelKind.Auxiliary(purpose) => s"  (* $purpose *)"
      case _ => ""
    s"${r.name}$tps : ${(r.cols.map(column) :+ res).mkString(" -> ")}.$kind"

  def typeDecl(t: TypeSym): String =
    val tps = if t.tparams.isEmpty then "" else t.tparams.mkString(" [", " ", "]")
    t.kind match
      case TypeKind.Open => s"${t.name}$tps : type."
      case TypeKind.Refinement(b) => s"${t.name}$tps : type <: ${b.show}."

  def directive(d: Directive): String =
    val tgt = d.target.map(_.show).orElse(d.rule.map("@" + _)).getOrElse("?")
    d.kind match
      case DirKind.ModeD(spec) => s"%mode $tgt ${spec.inputs.map((b, l, _) => (if b then "+" else "-") + l.getOrElse("")).mkString(" ")}."
      case DirKind.TerminatesVar(vs, args) => s"%terminates ${hugin.syntax.Printer.measure(vs)} ($tgt ${args.map(arg).mkString(" ")})."
      case DirKind.TerminatesLabel(ls) => s"%terminates ${hugin.syntax.Printer.measure(ls)} $tgt."
      case DirKind.Partial => s"%partial $tgt."
      case DirKind.Open => s"%open $tgt."
      case DirKind.Input => s"%input $tgt."
      case DirKind.Output => s"%output $tgt."
      case DirKind.Derivations => s"%derivations $tgt."
      case DirKind.NameHint(v) => s"%name $tgt $v."

  def program(p: ObjProgram): String =
    val sb = new StringBuilder
    p.types.foreach(t => sb ++= typeDecl(t) += '\n')
    p.rels.foreach(r => sb ++= relDecl(r) += '\n')
    p.edges.foreach(e => sb ++= s"${e.sub.show} <: ${e.sup.name}.\n")
    p.directives.foreach(d => sb ++= directive(d) += '\n')
    p.rules.foreach(r => sb ++= rule(r) += '\n')
    p.queries.foreach(q => sb ++= query(q) += '\n')
    sb.toString
