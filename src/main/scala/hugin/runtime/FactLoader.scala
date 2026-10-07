package hugin.runtime

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.ir.{CoreProgram, Id}
import hugin.obj.{OType, RelSym, BaseType}
import hugin.obj.typing.TypeOps

/** Loads ground facts of input relations (Section 9.6). Loading interns them: the fact and its nested
 *  fact-constructor terms are asserted (`subfact_F`), nested data values are only hash-consed. */
final class FactLoader(engine: Engine, prog: CoreProgram, ops: TypeOps, reporter: Reporter):
  private val byName: Map[String, Vector[RelSym]] = prog.rels.groupBy(_.displayName)

  final class Bad extends Exception(null, null, false, false)

  private def err(p: InputError): Nothing =
    reporter.report(p)
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
        err(InputError.LiteralMismatch(expected, bt, t.span))
      engine.fromLit(l)
    case VarRef(_) | Wildcard() => err(InputError.NotGround(t.span))
    case _ =>
      val (h, args) = flatten(t)
      val name = path(h).getOrElse(err(InputError.ExpectedConstructorTerm(t.span)))
      val cands = byName.getOrElse(name, Vector.empty).filter(c => c.arity == args.length && ops.isSub(OType.Fact(c, Nil), expected))
      cands match
        case Vector(c) => Id(prog.tag(c), build(c, args))
        case Vector() =>
          if byName.contains(name) then
            err(InputError.ConstructorMisplaced(name, expected, byName(name).map(_.arity).distinct.toList, h.span))
          else err(InputError.UnknownConstructor(name, h.span))
        case _ => err(InputError.AmbiguousConstructor(name, expected, h.span))

  private def build(c: RelSym, args: List[Tree]): Int =
    val vs = args.zip(c.cols).map((a, col) => value(a, col.tpe)).toArray[Any]
    engine.store(prog.tag(c)).intern(vs)

  def load(src: SourceFile): Int =
    val prog0 = Parser.parse(src, reporter)
    var count = 0
    for item <- prog0.items do
      try
        item match
          case Rule(_, List(head), None) =>
            val (h, args) = flatten(head)
            val name = path(h).getOrElse(err(InputError.ExpectedFact(head.span)))
            val rels = byName.getOrElse(name, Vector.empty).filter(r => !r.isCtor && r.arity == args.length)
            rels match
              case Vector(r) =>
                val dirs = prog.directives(prog.tag(r))
                if !dirs.input && !dirs.open then
                  err(InputError.NotInputRelation(r.displayName, h.span))
                build(r, args)
                count += 1
              case Vector() =>
                if byName.contains(name) then
                  err(InputError.RelationArity(name, byName(name).map(_.arity).distinct.toList, head.span))
                else err(InputError.UnknownRelation(name, h.span))
              case _ => err(InputError.AmbiguousRelation(name, h.span))
          case other => err(InputError.NotAFact(other.span))
      catch case _: Bad => ()
    count
