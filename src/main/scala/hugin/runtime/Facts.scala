package hugin.runtime

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.obj.{OType, TypeOps, RelSym, BaseType}

/** Loads ground facts of input relations (Section 9.6). Loading interns them, which establishes subfact closure. */
final class FactLoader(engine: Engine, prog: CoreProgram, ops: TypeOps, reporter: Reporter):
  private val byName: Map[String, Vector[RelSym]] = prog.rels.groupBy(_.displayName)

  final class Bad extends Exception(null, null, false, false)

  private def err(msg: String, span: Span, label: String = "", help: Option[String] = None): Nothing =
    var d = Diagnostic.error("E0801", msg, span, label)
    help.foreach(h => d = d.withHelp(h))
    reporter.report(d)
    throw Bad()

  private def path(t: Tree): Option[String] = t match
    case Ident(n) => Some(n)
    case Select(q, n) => path(q).map(_ + "." + n)
    case Parens(i) => path(i)
    case _ => None

  private def flatten(t: Tree): (Tree, List[Tree]) = t match
    case Apply(f, a) => val (h, as) = flatten(f); (h, as :+ a)
    case Parens(i) => flatten(i)
    case other => (other, Nil)

  private def value(t: Tree, expected: OType): Any = t match
    case Parens(i) => value(i, expected)
    case Lit(l) =>
      val bt = BaseType.of(l)
      if !(ops.isSub(OType.Base(bt), expected) || ops.baseOf(expected).contains(bt)) then
        err("type mismatch in input fact", t.span, s"expected `${expected.show}`, found `${bt.show}`")
      engine.fromLit(l)
    case VarRef(_) | Wildcard() => err("input facts must be ground", t.span, "variable in input fact")
    case _ =>
      val (h, args) = flatten(t)
      val name = path(h).getOrElse(err("expected a constructor term", t.span))
      val cands = byName.getOrElse(name, Vector.empty).filter(c => c.arity == args.length && ops.isSub(OType.Fact(c, Nil), expected))
      cands match
        case Vector(c) => Id(c.tag, build(c, args))
        case Vector() =>
          if byName.contains(name) then
            err(
              s"`$name` cannot occur here",
              h.span,
              s"expected a value of type `${expected.show}`",
              Some(s"`$name` takes ${byName(name).map(_.arity).distinct.mkString(" or ")} argument(s)")
            )
          else err(s"unknown constructor `$name`", h.span, "not declared in the program")
        case _ => err(s"ambiguous constructor `$name`", h.span, s"several instances fit `${expected.show}`")

  private def build(c: RelSym, args: List[Tree]): Int =
    val vs = args.zip(c.cols).map((a, col) => value(a, col.tpe)).toArray[Any]
    engine.store(c.tag).intern(vs)._1

  def load(src: SourceFile): Int =
    val prog0 = Parser.parse(src, reporter)
    var count = 0
    for item <- prog0.items do
      try
        item match
          case Rule(_, List(head), None) =>
            val (h, args) = flatten(head)
            val name = path(h).getOrElse(err("expected a fact `rel arg ...`", head.span))
            val rels = byName.getOrElse(name, Vector.empty).filter(r => !r.isCtor && r.arity == args.length)
            rels match
              case Vector(r) =>
                if !r.isInput && !r.isOpen then
                  err(
                    s"`${r.displayName}` is not an input relation",
                    h.span,
                    "facts can only be loaded into input relations",
                    Some(s"declare `%input ${r.displayName}.` in the program")
                  )
                build(r, args)
                count += 1
              case Vector() =>
                if byName.contains(name) then
                  err(s"`$name` expects ${byName(name).map(_.arity).distinct.mkString(" or ")} argument(s)", head.span)
                else err(s"unknown relation `$name`", h.span, "not declared in the program")
              case _ => err(s"ambiguous relation `$name`", h.span)
          case other => err("input files contain only ground facts", other.span, "not a fact")
      catch case _: Bad => ()
    count
