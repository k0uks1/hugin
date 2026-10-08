package hugin.core
package handover

import hugin.obj
import hugin.obj.DirKind
import hugin.core.elab.{DirectiveProblem, ReflectionProblem}
import hugin.util.*

/** The attributes that local directives attach to declarations (reference: directives), staged: the `decl`
 *  value of a [[CoreItem.DeclItem]] is evaluated (in a module instance's environment, or closed) and read
 *  ([[DeclAttributes]]), and each attribute becomes an object directive of the relation (or rule) it
 *  describes. What the data does not allow is reported: a target that is not a relation (E0701, E0406),
 *  another declaration than the one a prefix directive is attached to (E1003), a directive's own error
 *  (E1000), data that is not closed (E0918). An attribute of a family applies to each of its instances,
 *  which are known only at the end of the handover ([[family]]). */
private[handover] final class DeclData(core: Core, symbols: ObjectSymbols, reporter: Reporter):
  import core.*

  private val attributes = DeclAttributes(core)

  /** The attributes of families, staged at their instances at the end. */
  private val generic = scala.collection.mutable.ListBuffer.empty[(Int, Attribute, Span, Span, Origin)]

  /** The object directives of a local directive's result, in `base` (rule names qualified with `prefix`). */
  def directives(d: CoreItem.DeclItem, base: List[Val], prefix: String, origin: Origin): List[obj.Directive] =
    try
      val value = attributes.decode(eval(base, d.decl), d.span)
      val expected = d.attached.map(t => attributes.symbol(eval(base, t), d.span))
      value match
        case DeclValue.Rejected(m) => fail(DirectiveProblem.Rejected(m, d.span))
        case DeclValue.NamedRule(n, attrs) =>
          attrs.map {
            case Attribute.Derivations => obj.Directive(DirKind.Derivations, None, Some(qualify(prefix, n)))(d.span, origin)
            case a => fail(DirectiveProblem.NotForRules(a.directive, n, d.span))
          }
        case DeclValue.Constant(id, attrs, at) =>
          expected.filter(_ != id).foreach { e =>
            fail(DirectiveProblem.ChangedDeclaration(globals(e).name, globals(id).name, d.span))
          }
          globals(id).kind match
            case GlobalKind.Family(_, _) =>
              attrs.foreach(a => generic += ((id, a, d.span, at, origin)))
              Nil
            case _ => attrs.flatMap(a => directive(id, a, d.span, at, origin))
    catch
      case e: OpenDeclData =>
        reporter.report(ReflectionProblem.NotClosed(e.shown, if e.span.exists then e.span else d.span).toDiagnostic)
        Nil
      case Failed(p) =>
        reporter.report(p.toDiagnostic)
        Nil

  /** The directives of the attributes of families, at the instances of the families. */
  def familyDirectives(): List[obj.Directive] =
    generic.toList.flatMap((fam, a, span, at, origin) => symbols.instancesOf(fam).flatMap(i => guarded(directive(i, a, span, at, origin))))

  private def guarded(f: => List[obj.Directive]): List[obj.Directive] =
    try f
    catch
      case Failed(p) =>
        reporter.report(p.toDiagnostic)
        Nil

  private final case class Failed(p: hugin.util.diagnostics.Problem) extends Exception(null, null, false, false)
  private def fail(p: hugin.util.diagnostics.Problem): Nothing = throw Failed(p)

  /** The object directive of attribute `a` of `id`: the directive at `span`, the target at `at`. */
  private def directive(id: Int, a: Attribute, span: Span, at: Span, origin: Origin): List[obj.Directive] =
    val rel = relation(id, a.directive, at)
    val kind = a match
      case Attribute.Input => DirKind.Input
      case Attribute.Output => DirKind.Output
      case Attribute.Open => DirKind.Open
      case Attribute.Derivations => DirKind.Derivations
      case Attribute.Terminates(Some(vars), _, pattern) => DirKind.TerminatesVar(vars, pattern.map(term(_, span)))
      case Attribute.Terminates(None, labels, Nil) => DirKind.TerminatesLabel(labels)
      case Attribute.Terminates(None, _, _) => fail(DirectiveProblem.LabelsWithPattern(span))
    List(obj.Directive(kind, Some(obj.RelRef.Sym(rel)), None)(span, origin))

  /** The relation of an object constant (a relation, fact constructor or struct). */
  private def relation(id: Int, directive: String, span: Span): obj.RelSym =
    globals(id).kind match
      case _ => symbols.relSym(id).getOrElse(fail(DirectiveProblem.NotARelation(directive, span)))

  private var wildcards = 0

  private def term(t: PatternTerm, span: Span): obj.Term = t match
    case PatternTerm.Variable(n) => obj.Term.Var(n)(span)
    case PatternTerm.Literal(l) => obj.Term.Lit(l)(span)
    case PatternTerm.Other =>
      wildcards += 1
      obj.Term.Var(s"${obj.Var.WildPrefix}$wildcards")(span)

  private def qualify(prefix: String, name: String): String = if prefix.isEmpty then name else s"$prefix.$name"
