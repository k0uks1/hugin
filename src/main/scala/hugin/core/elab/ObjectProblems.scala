package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of object code and object declarations found by the new meta level (redesign B3): the shape
 *  of object items (named patterns, atoms, directives), the data/fact split, declarations of object
 *  constants. Object *typing* problems are the object typer's (`obj/typing/TypingProblems`). */
enum ObjectProblem extends Problem:
  /** An aggregate that is not the right-hand side of `X = k { … }`. */
  case UnboundAggregate(at: Span)

  /** `not` or `as` applied to something that is not a relation atom (after staging). */
  case NotAnAtom(construct: String, at: Span)

  /** Staged object code without the shape the object level needs (`what`: a variable, a term, …). */
  case NotObjectShape(what: String, shown: String, at: Span)
  case RestInHead(at: Span)
  case UnknownLabel(rel: String, label: String, known: List[String], at: Span, declared: Span)
  case MissingLabels(rel: String, missing: List[String], inHead: Boolean, at: Span, afterLast: Option[Span])
  case UnlabelledColumns(rel: String, at: Span)
  case DuplicateLabel(label: String, at: Span, first: Span)

  /** A data constructor or data struct (`what`) used as a relation; `decl` is its declaration (with its
   *  text if it is in the file of the use). */
  case DataAsRelation(name: String, what: String, label: String, at: Span, declared: Span, decl: Option[(Span, String)], local: Boolean)
  case DataFieldAsRelation(shown: String, label: String, at: Span)
  case SingletonVariable(name: String, at: Span)
  case UnknownDirective(name: String, at: Span)
  case NotARelation(directive: String, at: Span)
  case BoundOutsideRelation(kind: String, at: Span)
  case NotOpenType(name: String, at: Span, declared: Span)
  case EdgeTarget(at: Span)
  case RefinementOfNonType(at: Span)
  case StructFieldFact(at: Span)
  case StructRequirement(at: Span)
  case UsedBeforeDeclaration(name: String, at: Span)
  case StuckObjectType(shown: String, at: Span)

  case DuplicateMember(name: String, at: Span, first: Span)
  case UnknownRequirementField(label: String, at: Span)

  /** A data constructor passed for a `%fact` field of a signature. */
  case NotAFactConstructor(name: String, label: String, at: Span)
  case FormulaFunctionWithoutClauses(name: String, at: Span)
  case ClauseArity(name: String, args: Int, params: Int, at: Span)

  /** A rule of family `family`, instantiated at `instance`, uses the family at `used`. */
  case PolymorphicRecursion(family: String, used: String, instance: String, at: Span)

  def code: Code = this match
    case _: UnboundAggregate | _: NotAnAtom | _: NotObjectShape => Code.E0202
    case _: RestInHead => Code.E0302
    case _: UnknownLabel | _: UnlabelledColumns => Code.E0306
    case _: MissingLabels => Code.E0301
    case _: DuplicateLabel => Code.E0307
    case _: DataAsRelation | _: DataFieldAsRelation => Code.E0406
    case _: SingletonVariable => Code.W0002
    case _: UnknownDirective | _: NotARelation => Code.E0701
    case _: BoundOutsideRelation => Code.E0605
    case _: NotOpenType | _: EdgeTarget | _: RefinementOfNonType => Code.E0404
    case _: StructFieldFact | _: StructRequirement => Code.E0004
    case _: UsedBeforeDeclaration => Code.E0101
    case _: StuckObjectType => Code.E0909
    case _: PolymorphicRecursion => Code.E0205
    case _: FormulaFunctionWithoutClauses => Code.W0005
    case _: DuplicateMember => Code.E0102
    case _: UnknownRequirementField => Code.E0906
    case _: NotAFactConstructor => Code.E0204
    case _: ClauseArity => Code.E0207

  def primary: Span = this match
    case UnboundAggregate(s) => s
    case NotAnAtom(_, s) => s
    case NotObjectShape(_, _, s) => s
    case RestInHead(s) => s
    case UnknownLabel(_, _, _, s, _) => s
    case MissingLabels(_, _, _, s, _) => s
    case UnlabelledColumns(_, s) => s
    case DuplicateLabel(_, s, _) => s
    case DataAsRelation(_, _, _, s, _, _, _) => s
    case SingletonVariable(_, s) => s
    case DataFieldAsRelation(_, _, s) => s
    case UnknownDirective(_, s) => s
    case NotARelation(_, s) => s
    case BoundOutsideRelation(_, s) => s
    case NotOpenType(_, s, _) => s
    case EdgeTarget(s) => s
    case RefinementOfNonType(s) => s
    case StructFieldFact(s) => s
    case StructRequirement(s) => s
    case UsedBeforeDeclaration(_, s) => s
    case StuckObjectType(_, s) => s
    case PolymorphicRecursion(_, _, _, s) => s
    case FormulaFunctionWithoutClauses(_, s) => s
    case DuplicateMember(_, s, _) => s
    case UnknownRequirementField(_, s) => s
    case NotAFactConstructor(_, _, s) => s
    case ClauseArity(_, _, _, s) => s

  def message: Msg = this match
    case _: UnboundAggregate => msg"an aggregate must be bound to a variable, `X = count { ... }`"
    case NotAnAtom(c, _) => if c == "not" then msg"`not` applies only to relation atoms" else msg"`as` in a body applies to a relation atom"
    case NotObjectShape(w, _, _) => msg"expected ${Lit(w)}"
    case _: RestInHead => msg"`..` is not allowed in a rule head"
    case UnknownLabel(r, l, _, _, _) => msg"${Src(r)} has no column labelled ${Src(l)}"
    case MissingLabels(r, ms, _, _, _) => msg"missing label${Lit(if ms.length > 1 then "s" else "")} in named pattern for ${Src(r)}"
    case UnlabelledColumns(r, _) => msg"${Src(r)} does not label all of its columns, so it cannot be used with a named pattern"
    case DuplicateLabel(l, _, _) => msg"duplicate label ${Src(l)}"
    case DataAsRelation(n, w, _, _, _, _, _) => msg"${Lit(w)} ${Src(n)} used as a relation"
    case SingletonVariable(n, _) => msg"variable ${Src(n)} occurs only once in this rule"
    case DataFieldAsRelation(n, _, _) => msg"data constructor ${Src(n)} used as a relation"
    case UnknownDirective(n, _) => msg"unknown directive ${Src("%" + n)}"
    case NotARelation(d, _) => msg"${Src(d)} expects a relation"
    case BoundOutsideRelation(k, _) => msg"${Src(k)} column type outside a relation declaration"
    case NotOpenType(n, _, _) => msg"${Src(n)} is not an open type"
    case _: EdgeTarget => msg"the target of a subtyping edge must be an open type"
    case _: RefinementOfNonType => msg"only object types can be declared as refinements"
    case _: StructFieldFact => msg"`%fact` is not allowed on the fields of a struct"
    case _: StructRequirement => msg"requirements are not allowed in struct declarations"
    case UsedBeforeDeclaration(n, _) => msg"${Src(n)} is used before its declaration"
    case _: StuckObjectType => msg"cannot compute an object type at compile time"
    case _: PolymorphicRecursion => msg"polymorphic recursion"
    case FormulaFunctionWithoutClauses(n, _) => msg"formula function ${Src(n)} has no clauses"
    case DuplicateMember(n, _, _) => msg"duplicate declaration of ${Src(n)}"
    case UnknownRequirementField(l, _) => msg"no field ${Src(l)} in the signature"
    case NotAFactConstructor(n, l, _) =>
      msg"signature mismatch: field ${Src(l)} must be a fact constructor, but ${Src(n)} is a data constructor"
    case ClauseArity(n, a, p, _) => msg"clause of ${Src(n)} has $a arguments, but the function takes $p"

  override def primaryLabel: Msg = this match
    case _: NotAnAtom => msg"not a relation atom"
    case NotObjectShape(w, shown, _) => msg"${Src(shown)} is not ${Lit(w)}"
    case _: RestInHead => msg"rest pattern in head"
    case _: UnknownLabel => msg"unknown label"
    case MissingLabels(_, ms, _, _, _) => Msg.join(ms.map(l => msg"missing ${Src(l)}"), ", ")
    case _: DuplicateLabel => msg"duplicate"
    case DataAsRelation(_, _, l, _, _, _, _) => Msg.text(l)
    case _: SingletonVariable => msg"singleton variable"
    case _: DataFieldAsRelation => msg"not a relation: it has no facts to read"
    case _: FormulaFunctionWithoutClauses => msg"always false"
    case _: DuplicateMember => msg"declared again here"
    case _: NotARelation => msg"not a relation"
    case _: BoundOutsideRelation => msg"a bound column is only allowed as the last column of a relation declaration"
    case _: NotOpenType => msg"edge target must be open"
    case _: RefinementOfNonType => msg"`<:` after a type that is not `type`"
    case _: StructFieldFact => msg"struct field"
    case StuckObjectType(shown, _) => msg"${Src(shown)} is not an object type"
    case PolymorphicRecursion(f, used, inst, _) => msg"${Src(f)} used at ${Lit(used)} while instantiating ${Src(f)} at ${Lit(inst)}"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case UnknownLabel(_, _, _, _, d) if d.exists => List(d -> msg"declared here")
    case DuplicateLabel(_, _, first) => List(first -> msg"first used here")
    case DataAsRelation(_, w, _, _, d, _, _) if d.exists => List(d -> msg"declared here as a ${Lit(w)}")
    case NotOpenType(_, _, d) => List(d -> msg"declared here")
    case DuplicateMember(_, _, first) => List(first -> msg"first declared here")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: RestInHead => List(msg"the omitted columns of a derived fact would be unknown")
    case UnknownLabel(r, _, ls, _, _) =>
      List(if ls.isEmpty then msg"the columns of ${Src(r)} are not labelled" else msg"labels of ${Src(r)}: ${Lit(ls.mkString(", "))}")
    case DataAsRelation(n, w, _, _, _, _, _) => List(msg"${Src(n)} is a ${Lit(w)}: it builds values, which are not facts of a relation")
    case _: StuckObjectType => List(msg"the meta code that computes this type is stuck, so no object type results")
    case DataFieldAsRelation(_, l, _) => List(msg"the field ${Src(l)} is a data constructor: its values are data, not facts of a relation")
    case _: PolymorphicRecursion =>
      List(msg"a rule over a family must use the family at the arguments it is instantiated at, or it would create ever larger instances")
    case _ => Nil

  override def helps: List[Msg] = this match
    case MissingLabels(_, ms, head, _, _) =>
      List(
        if head then Msg.text("add " + ms.map(l => s"`$l = ...`").mkString(", "))
        else msg"add the missing labels, or end the pattern with `..` to ignore them"
      )
    case DataAsRelation(n, w, _, _, _, decl, local) =>
      val fact = w.replace("data", "fact")
      List(decl match
        case Some((_, text)) if local =>
          val shown = if text.contains('\n') then s"%fact $n : ..." else s"%fact $text"
          msg"declare ${Src(n)} as a ${Lit(fact)} to read its facts: ${Src(shown)}"
        case Some(_) => msg"${Src(n)} is declared in another file; declare a fact constructor of your own with `%fact` to read its facts"
        case None => msg"declare ${Src(n)} with `%fact` to read its facts"
      )
    case SingletonVariable(n, _) => List(msg"use `_` or ${Src("_" + n)} if this is intended")
    case DataFieldAsRelation(_, l, _) =>
      List(msg"to read its facts, require a fact constructor in the signature: ${Src(s"%fact $l : ...")}")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case MissingLabels(_, ms, head, _, Some(at)) =>
      val add = Suggestion.replace(
        at,
        ms.map(l => s", $l = ${if head then l.capitalize else "_"}").mkString,
        msg"add the missing labels",
        // in a head, the new variables still have to be bound by the body
        if head then Applicability.HasPlaceholders else Applicability.MachineApplicable
      )
      if head then List(add)
      else List(add, Suggestion.replace(at, ", ..", msg"ignore the missing labels with `..`", Applicability.MachineApplicable))
    case DataAsRelation(_, _, _, _, _, Some((d, _)), true) =>
      List(Suggestion.replace(d.startPoint, "%fact ", msg"declare it with `%fact`", Applicability.MachineApplicable))
    case SingletonVariable(n, at) =>
      List(
        Suggestion.replace(at, "_", msg"replace ${Src(n)} with `_`", Applicability.MachineApplicable),
        Suggestion.replace(at, "_" + n, msg"rename ${Src(n)} to ${Src("_" + n)}", Applicability.MaybeIncorrect)
      )
    case _ => Nil
