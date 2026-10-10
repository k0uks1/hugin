package hugin.syntax

/** Pretty printer for surface trees (output of the `parser` phase). Fully parenthesizes operators. */
object Printer:
  def show(t: Tree): String = t match
    case Ident(n) => n
    case VarRef(n) => n
    case Wildcard() => "_"
    case RuleRef(n) => "@" + n
    case Lit(l) => l.show
    case Select(q, n) => s"${show(q)}.$n"
    case Apply(f, a) => s"${show(f)} ${showArg(a)}"
    case Infix(op, l, r) => s"(${show(l)} $op ${show(r)})"
    case Neg(a) => s"-${showArg(a)}"
    case Arrow(Some(l), d, c) => s"(${l.name} : ${show(d)}) -> ${show(c)}"
    case Arrow(None, d, c) => s"(${show(d)} -> ${show(c)})"
    case Union(l, r) => s"(${show(l)} | ${show(r)})"
    case Keyword(k) => k.toString.toLowerCase
    case RecordType(es) => es.map(showSig).mkString("{ ", ", ", " }")
    case ModuleBody(items) =>
      if items.isEmpty then "{ }" else items.map(i => "  " + showItem(i).replace("\n", "\n  ")).mkString("{\n", "\n", "\n}")
    case RecordLit(fs, rest) =>
      (fs.map(f => s"${f.label.name} = ${show(f.value)}") ++ (if rest then List("..") else Nil)).mkString("{ ", ", ", " }")
    case Lambda(p, tpe, b) => s"[${show(p)}${tpe.map(t => " : " + show(t)).getOrElse("")}] ${show(b)}"
    case As(t, v) => s"(${show(t)} as ${v.name})"
    case Ascribe(t, tp) => s"(${show(t)} : ${show(tp)})"
    case With(v, fs) => s"(${show(v)} with ${fs.map(f => s"${f.label.name} = ${show(f.value)}").mkString("{ ", ", ", " }")})"
    case Not(a) => s"not ${showArg(a)}"
    case Agg(k, t, b) => s"${k.show} { ${show(t)} | ${show(b)} }"
    case BoundType(k, t) => s"${k.show} ${showArg(t)}"
    case Conj(l, r) => s"${show(l)}, ${show(r)}"
    case Disj(l, r) => s"(${show(l)} ; ${show(r)})"
    case Parens(i) => s"(${show(i)})"
    case Builtin(n) => s"%builtin ${n.name}"
    case Import(path) => s"%import ${Literal.quote(path)}"
    case SpliceE(a) => s"$$${showArg(a)}"
    case LiftE(a) => s"⇑${showArg(a)}"
    case CodeQuote(a) => s"<${show(a)}>"
    case Hole(n) => "?" + n.getOrElse("")
    case ImplicitBinder(ns, t) => s"{${ns.map(show).mkString(" ")} : ${show(t)}}"
    case ImplicitPi(ns, d, c) => s"{${ns.map(show).mkString(" ")} : ${show(d)}} -> ${show(c)}"
    case ListLit(es) => es.map(show).mkString("[", ", ", "]")
    case ConsE(h, t) => s"(${show(h)} :: ${show(t)})"
    case Quote(es, terminated) =>
      val shown = es.map(showItem(_).stripSuffix("."))
      if shown.isEmpty then "'( )" else shown.mkString("'( ", ". ", if terminated then ". )" else " )")
    case SpliceSeq(a) => s"$$..${showArg(a)}"
    case SpliceHO(f, as) => s"$$${showArg(f)}${as.map(show).mkString("[", ", ", "]")}"
    case SymRef(_, n) => n
    case NamedVar(n) => n
    case ModeArgs(ms) => ms.map(showMode).mkString(" ")
    case ErrorTree(parts) => parts.map(show).mkString("<error: ", " ", ">")

  private def showArg(t: Tree): String = t match
    case _: Apply | _: Not | _: Lambda | _: Conj | _: Neg => s"(${show(t)})"
    case _ => show(t)

  def showSig(e: SigEntry): String = e match
    case SigEntry.FieldDecl(l, t) => s"${l.name} : ${show(t)}"
    case SigEntry.Complete(l, _) => s"%complete ${l.name}"

  def showMode(m: ModeItem): String = (if m.input then "+" else "-") + m.label.map(_.name).getOrElse("")

  def showParam(p: Param): String = p match
    case Param.VarParam(v) => v.name
    case Param.Typed(n, t, _) => s"(${show(n)} : ${show(t)})"
    case Param.Malformed(t) => s"<error: ${show(t)}>"

  def showItem(i: Item): String = i match
    case Decl(n, ps, t, sup, d) =>
      s"${(n.name :: ps.map(showParam)).mkString(" ")} : ${show(t)}${sup.map(s => " <: " + show(s)).getOrElse("")}${d.map(x => " = " + show(x)).getOrElse("")}."
    case Def(n, ps, r) => s"${(n.name :: ps.map(showParam)).mkString(" ")} = ${show(r)}."
    case SubEdge(a, b) => s"${show(a)} <: ${show(b)}."
    case Rule(n, hs, b) =>
      s"${n.map(x => "@" + x.name + " ").getOrElse("")}${hs.map(show).mkString(", ")}${b.map(x => " :- " + show(x)).getOrElse("")}."
    case Query(b) => s"?- ${show(b)}."
    case Clause(l, r, Nil) => s"${show(l)} = ${show(r)}."
    case Clause(l, r, wh) => s"${show(l)} = ${show(r)}\n  where ${wh.map(showItem).mkString("\n        ")}"
    case Directive(k, args) =>
      args match
        case DirArgs.Infix(a, p, n) => s"%$k $a $p ${n.name}."
        case DirArgs.Apply(as, decl) => (s"%$k" :: as.map(showArg)).mkString(" ") + decl.fold(".")(_ => "") // the declaration follows
        case DirArgs.Use(Import(path), ns) => s"%use ${Literal.quote(path)}${ns.fold("")(_.map(_.name).mkString(" (", ", ", ")"))}."
        case DirArgs.Use(m, ns) => s"%use ${showArg(m)}${ns.fold("")(_.map(_.name).mkString(" (", ", ", ")"))}."
        case DirArgs.Export(s) => s"%export ${showArg(s)}."

  /** A `%terminates` measure: one name, or a parenthesised tuple. */
  def measure(names: List[String]): String = names match
    case List(n) => n
    case ns => ns.mkString("(", ", ", ")")

  def showProgram(p: Program): String = p.items.map(showItem).mkString("\n")
