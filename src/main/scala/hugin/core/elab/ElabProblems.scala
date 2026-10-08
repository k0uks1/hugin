package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of the meta level with object code and declarations (docs/DIAGNOSTICS.md): the shape of
 *  object items (named patterns, atoms, directives), the data/fact split, object declarations, module
 *  bodies, signatures and their requirements, formula functions, names. Type and stage errors are
 *  [[TypeProblem]]s, those of meta functions [[ClauseProblem]]s; object *typing* problems are the object
 *  typer's (`obj/typing/TypingProblems`). */
enum ElabProblem extends Problem:
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
  case DuplicateField(label: String, inSignature: Boolean, at: Span)

  case SingletonVariable(name: String, at: Span)
  case BoundOutsideRelation(kind: String, at: Span)
  case NotOpenType(name: String, at: Span, declared: Span)
  case EdgeTarget(at: Span)
  case RefinementOfNonType(at: Span)
  case StructRequirement(at: Span)
  case UsedBeforeDeclaration(name: String, at: Span)

  /** `f : (x : A) -> B = e.` where `e` uses the binder `x` at `at`: the definition's header `header` is
   *  better written `rewritten` (`f (x : A) : B`). */
  case TypeBinderInDefinition(name: String, at: Span, header: Span, rewritten: String)

  /** `e = e'.` where `e` is not a name applied to patterns: neither a definition nor a clause. */
  case MalformedClause(at: Span)

  /** `x : A = … x ….`: a definition referring to itself (only functions defined by clauses recurse). */
  case SelfReference(name: String, at: Span, defined: Span)
  case StuckObjectType(shown: String, at: Span)

  /** A second declaration of `name` in a file or module body. */
  case DuplicateMember(name: String, at: Span, first: Span)
  case UnusedDefinition(name: String, at: Span)

  /** `c : … -> a.` where `a` is not an open type (a refinement, or a base type if `base`): it is neither a
   *  relation nor a constructor. */
  case Unclassifiable(name: String, result: String, base: Boolean, at: Span)

  /** `%builtin n` with an unknown `n`, or outside the definition `b : type = %builtin n.` of a base type. */
  case UnknownBaseType(name: String, at: Span)
  case MisplacedBuiltin(name: String, at: Span)

  /** `x : A = %builtin p.` for a primitive operation `p` whose type is not `A`. */
  case PrimitiveType(name: String, expected: String, at: Span)

  /** `f : int -> type.`: a declared function into object types (a family is declared with parameters). */
  case TypeFunction(name: String, at: Span)
  case NotAModule(name: String, tpe: String, at: Span)

  /** A family's type argument (`what`: "type argument `A` of family `nil`") that nothing determines. */
  case UndeterminedTypeArgument(what: String, at: Span)

  /** A module (record) does not match the signature (record type) `expected` it is checked against. */
  case SignatureMismatch(expected: String, note: String, at: Span)
  case MissingSignatureField(label: String, expected: String, at: Span)
  case CyclicRefinement(name: String, at: Span)

  /** A cycle of type definitions closed by the reference at `at` to `name`, declared at `declared`. */
  case CyclicTypeDefinition(name: String, at: Span, declared: Span)
  case UnresolvedName(name: String, at: Span, similar: Option[String], replaceable: Boolean)
  case ObjectArity(name: String, expected: Int, found: Int, at: Span, declared: Span)

  /** A functor negates or aggregates over (`what`) the field `label` of its parameter `param` without the
   *  signature requiring `%complete label`; the requirement would be inserted at `insertAt`. */
  case IncompleteFieldParameter(what: String, param: String, label: String, at: Span, declared: Span, insertAt: Option[Span])
  case IncompleteRelationParameter(what: String, param: String, at: Span, declared: Span)
  case UnknownRequirementField(label: String, at: Span)

  case FormulaFunctionWithoutClauses(name: String, at: Span)
  case ClauseArity(name: String, args: Int, params: Int, at: Span)

  /** A rule of family `family`, instantiated at `instance`, uses the family at `used`. */
  case PolymorphicRecursion(family: String, used: String, instance: String, at: Span)

  def code: Code = this match
    case _: UnboundAggregate | _: NotAnAtom | _: NotObjectShape => Code.E0202
    case _: RestInHead => Code.E0302
    case _: UnknownLabel | _: UnlabelledColumns => Code.E0306
    case _: MissingLabels => Code.E0301
    case _: DuplicateLabel | _: DuplicateField => Code.E0307
    case _: SingletonVariable => Code.W0002
    case _: BoundOutsideRelation => Code.E0605
    case _: NotOpenType | _: EdgeTarget | _: RefinementOfNonType => Code.E0404
    case _: StructRequirement => Code.E0004
    case _: UsedBeforeDeclaration => Code.E0101
    case _: MalformedClause => Code.E0004
    case _: TypeBinderInDefinition => Code.E0916
    case _: SelfReference => Code.E0105
    case _: StuckObjectType => Code.E0909
    case _: PolymorphicRecursion => Code.E0205
    case _: FormulaFunctionWithoutClauses => Code.W0005
    case _: DuplicateMember => Code.E0102
    case _: UnusedDefinition => Code.W0003
    case _: Unclassifiable | _: TypeFunction | _: UnknownBaseType | _: MisplacedBuiltin | _: PrimitiveType => Code.E0103
    case _: NotAModule => Code.E0107
    case _: UndeterminedTypeArgument => Code.E0206
    case _: SignatureMismatch | _: MissingSignatureField => Code.E0204
    case _: CyclicRefinement => Code.E0404
    case _: CyclicTypeDefinition => Code.E0104
    case _: UnresolvedName => Code.E0101
    case _: ObjectArity => Code.E0207
    case _: IncompleteFieldParameter | _: IncompleteRelationParameter => Code.E0210
    case _: UnknownRequirementField => Code.E0906
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
    case DuplicateField(_, _, s) => s
    case SingletonVariable(_, s) => s
    case BoundOutsideRelation(_, s) => s
    case NotOpenType(_, s, _) => s
    case EdgeTarget(s) => s
    case RefinementOfNonType(s) => s
    case StructRequirement(s) => s
    case UsedBeforeDeclaration(_, s) => s
    case MalformedClause(s) => s
    case TypeBinderInDefinition(_, s, _, _) => s
    case SelfReference(_, s, _) => s
    case StuckObjectType(_, s) => s
    case PolymorphicRecursion(_, _, _, s) => s
    case FormulaFunctionWithoutClauses(_, s) => s
    case DuplicateMember(_, s, _) => s
    case UnusedDefinition(_, s) => s
    case Unclassifiable(_, _, _, s) => s
    case TypeFunction(_, s) => s
    case UnknownBaseType(_, s) => s
    case MisplacedBuiltin(_, s) => s
    case PrimitiveType(_, _, s) => s
    case NotAModule(_, _, s) => s
    case UndeterminedTypeArgument(_, s) => s
    case SignatureMismatch(_, _, s) => s
    case MissingSignatureField(_, _, s) => s
    case CyclicRefinement(_, s) => s
    case CyclicTypeDefinition(_, s, _) => s
    case UnresolvedName(_, s, _, _) => s
    case ObjectArity(_, _, _, s, _) => s
    case IncompleteFieldParameter(_, _, _, s, _, _) => s
    case IncompleteRelationParameter(_, _, s, _) => s
    case UnknownRequirementField(_, s) => s
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
    case DuplicateField(l, sig, _) => msg"duplicate field ${Src(l)}${Lit(if sig then " in signature" else "")}"
    case SingletonVariable(n, _) => msg"variable ${Src(n)} occurs only once in this rule"
    case BoundOutsideRelation(k, _) => msg"${Src(k)} column type outside a relation declaration"
    case NotOpenType(n, _, _) => msg"${Src(n)} is not an open type"
    case _: EdgeTarget => msg"the target of a subtyping edge must be an open type"
    case _: RefinementOfNonType => msg"only object types can be declared as refinements"
    case _: StructRequirement => msg"requirements are not allowed in struct declarations"
    case UsedBeforeDeclaration(n, _) => msg"${Src(n)} is used before its declaration"
    case _: MalformedClause => msg"malformed definition"
    case TypeBinderInDefinition(n, _, _, _) => msg"${Src(n)} is not in scope in the definition"
    case SelfReference(n, _, _) => msg"${Src(n)} refers to itself"
    case _: StuckObjectType => msg"cannot compute an object type at compile time"
    case _: PolymorphicRecursion => msg"polymorphic recursion"
    case FormulaFunctionWithoutClauses(n, _) => msg"formula function ${Src(n)} has no clauses"
    case DuplicateMember(n, _, _) => msg"${Src(n)} is declared twice in this scope"
    case UnusedDefinition(n, _) => msg"unused definition ${Src(n)}"
    case Unclassifiable(n, _, _, _) => msg"cannot classify the declaration of ${Src(n)}"
    case TypeFunction(n, _) => msg"cannot classify the declaration of ${Src(n)}"
    case UnknownBaseType(n, _) => msg"unknown base type ${Src(n)}"
    case MisplacedBuiltin(n, _) => msg"${Src(s"%builtin $n")} is only allowed as the definition of a base type"
    case PrimitiveType(n, e, _) => msg"the primitive ${Src(s"%builtin $n")} has type ${Src(e)}"
    case NotAModule(n, _, _) => msg"${Src(n)} is not a module"
    case UndeterminedTypeArgument(w, _) => Msg.text(s"cannot infer $w")
    case _: SignatureMismatch => msg"signature mismatch"
    case MissingSignatureField(l, _, _) => msg"signature mismatch: missing field ${Src(l)}"
    case CyclicRefinement(n, _) => msg"cyclic refinement ${Src(n)}"
    case CyclicTypeDefinition(n, _, _) => msg"cyclic type definition ${Src(n)}"
    case UnresolvedName(n, _, _, _) => msg"unresolved name ${Src(n)}"
    case ObjectArity(n, e, f, _, _) => msg"${Src(n)} expects $e argument${Lit(if e == 1 then "" else "s")}, found $f"
    case IncompleteFieldParameter(w, p, l, _, _, _) =>
      msg"the functor ${Lit(w)} the relation parameter ${Src(s"$p.$l")} without requiring ${Src(s"%complete $l")}"
    case IncompleteRelationParameter(w, p, _, _) => msg"the function ${Lit(w)} the relation parameter ${Src(p)}"
    case UnknownRequirementField(l, _) => msg"no field ${Src(l)} in the signature"
    case ClauseArity(n, a, p, _) => msg"clause of ${Src(n)} has $a arguments, but the function takes $p"

  override def primaryLabel: Msg = this match
    case _: TypeBinderInDefinition => msg"not found in this scope"
    case _: NotAnAtom => msg"not a relation atom"
    case NotObjectShape(w, shown, _) => msg"${Src(shown)} is not ${Lit(w)}"
    case _: RestInHead => msg"rest pattern in head"
    case _: UnknownLabel => msg"unknown label"
    case MissingLabels(_, ms, _, _, _) => Msg.join(ms.map(l => msg"missing ${Src(l)}"), ", ")
    case _: DuplicateLabel => msg"duplicate"
    case _: SingletonVariable => msg"singleton variable"
    case _: FormulaFunctionWithoutClauses => msg"always false"
    case _: DuplicateMember => msg"redeclared here"
    case _: UnusedDefinition => msg"never referenced"
    case Unclassifiable(_, r, true, _) => msg"result is the base type ${Src(r)}"
    case Unclassifiable(_, r, false, _) => msg"result is ${Src(r)}, which is not an open type"
    case _: TypeFunction => msg"a function returning `type`"
    case _: UnknownBaseType => msg"not a builtin"
    case _: SelfReference => msg"recursive reference"
    case _: MalformedClause => msg"expected a name applied to parameters before `=`"
    case _: MisplacedBuiltin => msg"not a type declaration"
    case _: PrimitiveType => msg"declared with another type"
    case NotAModule(_, t, _) => msg"has meta type ${Src(t)}"
    case _: UndeterminedTypeArgument => msg"type not determined"
    case SignatureMismatch(e, _, _) => msg"expected ${Src(e)}"
    case MissingSignatureField(l, _, _) => msg"field ${Src(l)} is required"
    case _: CyclicTypeDefinition => msg"refers back to the definition"
    case _: UnresolvedName => msg"not found in this scope"
    case ObjectArity(_, _, f, _, _) => msg"$f argument${Lit(if f == 1 then "" else "s")} given"
    case IncompleteFieldParameter(_, p, l, _, _, _) => msg"${Src(s"$p.$l")} may be bound to an incomplete relation"
    case IncompleteRelationParameter(_, p, _, _) => msg"${Src(p)} may be bound to an incomplete relation"
    case _: BoundOutsideRelation => msg"a bound column is only allowed as the last column of a relation declaration"
    case _: NotOpenType => msg"edge target must be open"
    case _: RefinementOfNonType => msg"`<:` after a type that is not `type`"
    case StuckObjectType(shown, _) => msg"${Src(shown)} is not an object type"
    case PolymorphicRecursion(f, used, inst, _) => msg"${Src(f)} used at ${Lit(used)} while instantiating ${Src(f)} at ${Lit(inst)}"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case SelfReference(_, _, d) => List(d -> msg"while elaborating this definition")
    case UnknownLabel(_, _, _, _, d) if d.exists => List(d -> msg"declared here")
    case DuplicateLabel(_, _, first) => List(first -> msg"first used here")
    case NotOpenType(_, _, d) => List(d -> msg"declared here")
    case DuplicateMember(_, _, first) => List(first -> msg"first declared here")
    case CyclicTypeDefinition(_, _, d) => List(d -> msg"type definition declared here")
    case ObjectArity(_, _, _, _, d) if d.exists => List(d -> msg"declared here")
    case IncompleteFieldParameter(_, p, _, _, d, _) => List(d -> msg"parameter ${Src(p)} declared here")
    case IncompleteRelationParameter(_, p, _, d) => List(d -> msg"parameter ${Src(p)} declared here")
    case _ => Nil

  override def notes: List[Msg] = this match
    case TypeBinderInDefinition(n, _, _, _) =>
      List(msg"${Src(n)} is bound by the declared type: the binders of a type do not scope over the definition")
    case _: RestInHead => List(msg"the omitted columns of a derived fact would be unknown")
    case UnknownLabel(r, _, ls, _, _) =>
      List(if ls.isEmpty then msg"the columns of ${Src(r)} are not labelled" else msg"labels of ${Src(r)}: ${Lit(ls.mkString(", "))}")
    case _: StuckObjectType => List(msg"the meta code that computes this type is stuck, so no object type results")
    case _: UnknownBaseType => List(msg"the builtin base types are float, int, string")
    case _: SelfReference => List(msg"only a function declared with its type and defined by clauses may be recursive")
    case NotAnAtom("not", _) =>
      List(msg"a formula function use may expand to an arbitrary formula; declare a relation for the negated condition")
    case _: Unclassifiable =>
      List(msg"a declaration `c : A -> ... -> R.` declares a relation if R is `rel` and a constructor if R is an open type")
    case _: NotAModule => List(msg"a path `m.x` requires `m` to be module-valued")
    case SignatureMismatch(_, n, _) => List(Msg.text(n))
    case MissingSignatureField(_, e, _) => List(msg"expected signature ${Src(e)}")
    case _: CyclicTypeDefinition =>
      List(msg"type definitions are unfolded and must not form a cycle; declare an open type or struct instead")
    case _: PolymorphicRecursion =>
      List(msg"within a recursive component every relation must be used at exactly the type parameters of the rule family")
    case _ => Nil

  override def helps: List[Msg] = this match
    case MissingLabels(_, ms, head, _, _) =>
      List(
        if head then Msg.text("add " + ms.map(l => s"`$l = ...`").mkString(", "))
        else msg"add the missing labels, or end the pattern with `..` to ignore them"
      )
    case SingletonVariable(n, _) => List(msg"use `_` or ${Src("_" + n)} if this is intended")
    case Unclassifiable(n, r, _, _) => List(msg"to define a compile-time constant, write ${Src(s"$n : $r = ...")}.")
    case TypeFunction(n, _) => List(msg"declare a family with type parameters instead: ${Src(s"$n A : type.")}")
    case _: UndeterminedTypeArgument =>
      List(msg"ascribe a term with its type, e.g. `(nil : list int)`, so that the type argument is determined")
    case UnresolvedName(_, _, Some(s), _) => List(msg"a declaration with a similar name exists: ${Src(s)}")
    case IncompleteFieldParameter(_, p, l, _, _, _) => List(msg"add ${Src(s"%complete $l")} to the signature of ${Src(p)}")
    case _: IncompleteRelationParameter =>
      List(msg"pass the relation in a signature with `%complete`, e.g. `(m : { r : A -> rel, %complete r })`")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case TypeBinderInDefinition(_, _, header, rewritten) =>
      List(
        Suggestion.replace(header, rewritten, msg"make the binders parameters: ${Src(rewritten)}", Applicability.MachineApplicable)
      )
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
    case IncompleteFieldParameter(_, _, l, _, _, Some(at)) =>
      List(Suggestion.replace(at, s", %complete $l", msg"add ${Src(s"%complete $l")}", Applicability.MachineApplicable))
    case UnresolvedName(_, at, Some(s), true) =>
      List(Suggestion.replace(at, s, msg"replace with ${Src(s)}", Applicability.MaybeIncorrect))
    case SingletonVariable(n, at) =>
      List(
        Suggestion.replace(at, "_", msg"replace ${Src(n)} with `_`", Applicability.MachineApplicable),
        Suggestion.replace(at, "_" + n, msg"rename ${Src(n)} to ${Src("_" + n)}", Applicability.MaybeIncorrect)
      )
    case _ => Nil
