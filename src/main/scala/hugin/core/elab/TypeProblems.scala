package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** What can go wrong with the code that cannot be computed at compile time (E0909, staging). */
enum Unstaged:
  /** Spliced meta code that does not evaluate to object code (it applies a postulate or a variable). */
  case StuckSplice

  /** A persisted meta value that does not evaluate to a literal. */
  case StuckPrimitive

  /** Compile-time arithmetic that is undefined (overflow, division by zero). */
  case UndefinedArithmetic

  /** An unknown in object code that elaboration did not determine. */
  case Unsolved

  /** Something that is not object code at all. */
  case NotObjectCode

/** The type and stage errors of the meta level (E09xx up to rule heads), and the syntax its elaborator
 *  rejects (E0001). Types are given as shown to users. */
enum TypeProblem extends Problem:
  case ImplicitBinderAlone(at: Span)
  case UnknownOperator(op: String, at: Span)
  case NotAParameterName(at: Span)

  /** `notes`: why the types do not unify (an occurs check, an escaping variable, …). */
  case Mismatch(expected: String, found: String, at: Span, why: List[String])
  case NotAType(found: String, at: Span)
  case NegativeNat(tpe: String, at: Span)

  /** An integer literal beyond the 64-bit range, not checked against a nat-like family (whose numerals are
   *  unbounded, reference: lexical-structure). */
  case IntegerOutOfRange(at: Span)

  case NotNumeric(found: String, at: Span)
  case NotString(found: String, at: Span)
  case NotObjectConstantType(at: Span)

  /** Object code where a meta value of type `expected` is needed, and the other way round. */
  case ObjectForMeta(expected: String, found: String, at: Span)

  /** `unshared`: the first type in `found` that is not shared, if `found` is a meta inductive type or a
   *  shared type applied to one (it has no lifting into object code). */
  case MetaForObject(expected: String, found: String, at: Span, unshared: Option[String] = None)
  case DependsOnObject(name: String, at: Span)
  case SpliceOfObjectCode(at: Span)
  case CannotInferWildcard(at: Span)
  case CannotInfer(what: String, at: Span)
  case UniverseInconsistency(expected: String, found: String, at: Span)

  /** `f a` where `f` (named `fn`) is not a function: `why`, the argument at `arg`. */
  case NotAFunction(fn: String, why: String, at: Span, arg: Span)
  case UnknownExpectedField(label: String, fields: List[String], at: Span)
  case NoField(label: String, tpe: String, fields: List[String], similar: Option[String], at: Span)
  case NotARecord(label: String, qualifier: Span, tpe: String, at: Span)
  case Unsupported(what: String, at: Span)
  case ObjectTypeArgument(at: Span)
  case ObjectFunction(at: Span)
  case NotStaged(kind: Unstaged, shown: String, at: Span)

  /** A meta integer used as object code (persisted, or reflected as a literal) outside the object level's
   *  64-bit range (D8a): `shown` is the integer. */
  case IntegerCrossing(shown: String, at: Span)

  /** A meta integer in a compilation without `std/nat`, whose family `int` the meta `int` is
   *  (`--no-prelude`). */
  case NoMetaInt(at: Span)
  case IncompleteHead(at: Span)
  case InvalidHead(tpe: String, at: Span)

  /** A typed hole `?name` (reference: meta/functions) of type `goal` at a stage, with the variables in
   *  scope (shown as `x : A`). */
  case UnsolvedGoal(name: Option[String], goal: String, stage: String, context: List[String], at: Span)

  /** `f {x := e}` (reference: meta/functions) where `fn` has no implicit argument `x` before its next
   *  explicit argument: `available` are the names it accepts there. */
  case NoImplicitNamed(name: String, fn: String, available: List[String], at: Span)

  /** `{x := e}` outside the arguments of an application or the patterns of a clause. */
  case NamedArgumentAlone(at: Span)

  /** A relation (or struct) applied to arguments where a meta type is expected, also under an explicit
   *  `⇑`: the lift of an applied fact type, which has no closed inhabitants (#186 P9a). With `eta`, the
   *  unapplied relation `shown` where a type family is expected, which would be such a type once applied.
   *  A relation that a program owns is that program's judgment instead (#186 P9b), so the relation here
   *  is owned by none, or it is under an explicit `⇑` (`lifted`), or `std/semantics` is not loaded. */
  case AppliedRelation(shown: String, eta: Boolean, at: Span, lifted: Boolean = false)

  def code: Code = this match
    case _: ImplicitBinderAlone | _: UnknownOperator | _: NotAParameterName => Code.E0001
    case _: IntegerOutOfRange => Code.E0003
    case _: Mismatch | _: NotAType | _: NegativeNat | _: NotNumeric | _: NotString | _: NotObjectConstantType =>
      Code.E0901
    case _: ObjectForMeta | _: MetaForObject | _: DependsOnObject | _: SpliceOfObjectCode => Code.E0902
    case _: CannotInferWildcard | _: CannotInfer => Code.E0903
    case _: UniverseInconsistency => Code.E0904
    case _: NotAFunction => Code.E0905
    case _: UnknownExpectedField | _: NoField | _: NotARecord => Code.E0906
    case _: Unsupported => Code.E0907
    case _: ObjectTypeArgument | _: ObjectFunction => Code.E0908
    case _: NotStaged => Code.E0909
    case _: IntegerCrossing => Code.E0930
    case _: NoMetaInt => Code.E0931
    case _: IncompleteHead | _: InvalidHead => Code.E0910
    case _: UnsolvedGoal => Code.E0924
    case _: NoImplicitNamed | _: NamedArgumentAlone => Code.E0926
    case _: AppliedRelation => Code.E0960

  def primary: Span = this match
    case ImplicitBinderAlone(s) => s
    case UnknownOperator(_, s) => s
    case NotAParameterName(s) => s
    case Mismatch(_, _, s, _) => s
    case NotAType(_, s) => s
    case NegativeNat(_, s) => s
    case IntegerOutOfRange(s) => s
    case NotNumeric(_, s) => s
    case NotString(_, s) => s
    case NotObjectConstantType(s) => s
    case ObjectForMeta(_, _, s) => s
    case MetaForObject(_, _, s, _) => s
    case DependsOnObject(_, s) => s
    case SpliceOfObjectCode(s) => s
    case CannotInferWildcard(s) => s
    case CannotInfer(_, s) => s
    case UniverseInconsistency(_, _, s) => s
    case NotAFunction(_, _, s, _) => s
    case UnknownExpectedField(_, _, s) => s
    case NoField(_, _, _, _, s) => s
    case NotARecord(_, _, _, s) => s
    case Unsupported(_, s) => s
    case ObjectTypeArgument(s) => s
    case ObjectFunction(s) => s
    case NotStaged(_, _, s) => s
    case IntegerCrossing(_, s) => s
    case NoMetaInt(s) => s
    case IncompleteHead(s) => s
    case InvalidHead(_, s) => s
    case UnsolvedGoal(_, _, _, _, s) => s
    case NoImplicitNamed(_, _, _, s) => s
    case NamedArgumentAlone(s) => s
    case AppliedRelation(_, _, s, _) => s

  def message: Msg = this match
    case _: ImplicitBinderAlone => msg"implicit binders must be followed by `->`"
    case UnknownOperator(op, _) => msg"unknown operator ${Src(op)}"
    case _: NotAParameterName => msg"expected a parameter name"
    case _: Mismatch | _: NegativeNat | _: NotNumeric | _: NotString => msg"mismatched types"
    case _: NotAType => msg"expected a type"
    case _: IntegerOutOfRange => msg"integer literal out of range"
    case _: NotObjectConstantType => msg"not the type of an object constant"
    case _: ObjectForMeta => msg"object code used where a compile-time value is needed"
    case _: MetaForObject => msg"compile-time value used as object code"
    case _: DependsOnObject => msg"a meta type cannot depend on object code"
    case _: SpliceOfObjectCode => msg"splice of object code"
    case _: CannotInferWildcard => msg"cannot infer the type of `_`"
    case CannotInfer(w, _) => msg"cannot infer ${Lit(w)}"
    case _: UniverseInconsistency => msg"universe inconsistency"
    case _: NotAFunction => msg"not a function"
    case UnknownExpectedField(l, _, _) => msg"no field ${Src(l)} in the expected record type"
    case NoField(l, _, _, _, _) => msg"no field ${Src(l)}"
    case NotARecord(l, _, _, _) => msg"no field ${Src(l)}"
    case Unsupported(w, _) => msg"${Lit(w)} are not supported by the meta level"
    case _: ObjectTypeArgument => msg"relations and constructors cannot take object types as arguments"
    case _: ObjectFunction => msg"object-level functions cannot be defined"
    case NotStaged(k, _, _) =>
      k match
        case Unstaged.StuckSplice => msg"cannot compute object code at compile time"
        case Unstaged.StuckPrimitive => msg"cannot compute a primitive value at compile time"
        case Unstaged.UndefinedArithmetic => msg"compile-time arithmetic failure"
        case Unstaged.Unsolved => msg"cannot infer object code"
        case Unstaged.NotObjectCode => msg"not object code"
    case _: IntegerCrossing => msg"integer out of the range of the object level's `int`"
    case _: NoMetaInt => msg"meta integers are not part of this compilation"
    case _: IncompleteHead => msg"incomplete rule head"
    case _: InvalidHead => msg"invalid rule head"
    case UnsolvedGoal(n, _, _, _, _) => msg"unsolved goal ${Src("?" + n.getOrElse(""))}"
    case NoImplicitNamed(n, f, _, _) => msg"${Src(f)} has no implicit argument ${Src(n)} here"
    case _: NamedArgumentAlone => msg"an implicit argument by name outside an application"
    case AppliedRelation(r, false, _, _) => msg"${Src(r)} is not a type: it applies a relation to arguments"
    case AppliedRelation(r, true, _, _) => msg"${Src(r)} is not a type family: it is a relation, and its applications are not types"

  override def primaryLabel: Msg = this match
    case _: ImplicitBinderAlone => msg"expected `{A : T} -> B`"
    case Mismatch(e, f, _, _) => msg"expected ${Src(e)}, found ${Src(f)}"
    case NotAType(f, _) => msg"this is a term of type ${Src(f)}"
    case NegativeNat(t, _) => msg"a negative number is not a ${Src(t)}"
    case _: IntegerOutOfRange => msg"does not fit into a 64-bit integer"
    case NotNumeric(f, _) => msg"expected a number, found ${Src(f)}"
    case NotString(f, _) => msg"expected a string, found ${Src(f)}"
    case ObjectForMeta(_, f, _) => msg"object code of type ${Src(f)}"
    case MetaForObject(_, f, _, _) => msg"a meta value of type ${Src(f)}"
    case DependsOnObject(n, _) => msg"${Src(n)} is object code"
    case _: SpliceOfObjectCode => msg"this is already object code"
    case _: CannotInferWildcard => msg"type annotations needed"
    case _: CannotInfer => msg"cannot infer this"
    case UniverseInconsistency(e, f, _) => msg"expected ${Src(e)}, found ${Src(f)}"
    case _: NotAFunction => msg"applied to an argument here"
    case _: UnknownExpectedField | _: NoField | _: NotARecord => msg"unknown field"
    case _: Unsupported => msg"not supported"
    case _: ObjectTypeArgument => msg"a type"
    case _: ObjectFunction => msg"a function at the object level"
    case NotStaged(k, shown, _) =>
      k match
        case Unstaged.StuckSplice => msg"${Src(shown)} does not evaluate to object code"
        case Unstaged.StuckPrimitive => msg"${Src(shown)} does not evaluate to a literal"
        case Unstaged.UndefinedArithmetic => msg"${Src(shown)} is undefined"
        case Unstaged.Unsolved => msg"unsolved"
        case Unstaged.NotObjectCode => msg"${Src(shown)}"
    case IntegerCrossing(n, _) => msg"${Src(n)} does not fit into 64 bits"
    case _: NoMetaInt => msg"a meta integer"
    case _: IncompleteHead => msg"missing arguments"
    case InvalidHead(t, _) => msg"this has type ${Src(t)}"
    case UnsolvedGoal(_, g, _, _, _) => msg"goal: ${Src(g)}"
    case _: NoImplicitNamed => msg"no implicit argument of this name"
    case _: NamedArgumentAlone => msg"expected an argument of an application"
    case AppliedRelation(_, false, _, _) => msg"an applied relation"
    case AppliedRelation(_, true, _, _) => msg"a relation where a type family is expected"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case NotAFunction(_, _, _, arg) => List(arg -> msg"argument")
    case NotARecord(_, q, t, _) => List(q -> msg"this has type ${Src(t)}, which is not a record type")
    case _ => Nil

  override def notes: List[Msg] = this match
    case Mismatch(_, _, _, why) => why.map(Msg.text)
    case ObjectForMeta(e, _, _) =>
      List(
        msg"a meta value of type ${Src(e)} is expected here",
        msg"object terms (rule variables, constructor terms, formulas) only exist at run time; the meta level computes at compile time"
      )
    case MetaForObject(e, _, _, u) =>
      List(
        msg"object code of type ${Src(e)} is expected here",
        msg"only object code (of type `⇑A`), primitive values (`int`, `float`, `string`) and values of shared data types (declared `: data`) can be used as object code"
      ) ++ u.map(t => msg"${Src(t)} is not a shared data type, so it has no lifting into object code").toList
    case _: SpliceOfObjectCode => List(Msg.text("`$t` splices meta code of type `⇑A` into object code"))
    case _: CannotInferWildcard => List(msg"`_` stands for an unknown meta value or, in object code, for a wildcard")
    case _: CannotInfer => List(msg"the elaborator found no constraint that determines it; add a type annotation")
    case _: UniverseInconsistency =>
      List(
        msg"universe levels are inferred: `Type₀ : Type₁ : …`, and a type in `Typeᵢ` is also in `Typeⱼ` for i ≤ j",
        msg"`Type : Type` is excluded: it would make the meta level inconsistent and non-terminating"
      )
    case NotAFunction(f, why, _, _) => List(msg"${Src(f)} cannot be applied: ${Lit(why)}")
    case UnknownExpectedField(_, ls, _) => List(msg"the expected record type has the fields ${Lit(ls.map(l => s"`$l`").mkString(", "))}")
    case NoField(_, t, ls, _, _) => List(msg"${Src(t)} has the fields ${Lit(ls.map(l => s"`$l`").mkString(", "))}")
    case _: Unsupported => List(msg"see the open issues of the redesign in docs/NOTES.md")
    case _: ObjectTypeArgument => List(msg"the object level is first order; families of relations are meta functions returning relations")
    case _: ObjectFunction => List(msg"the object level is first order; functions are meta-level code (formula functions, functors)")
    case NotStaged(k, _, _) =>
      List(k match
        case Unstaged.StuckSplice =>
          msg"the meta code spliced here is stuck (it applies a postulate or a variable), so no object code results"
        case Unstaged.StuckPrimitive =>
          msg"a meta value used in object code must evaluate to a literal (overflow and division by zero are undefined)"
        case Unstaged.UndefinedArithmetic => msg"overflow and division by zero are undefined at the meta level"
        case Unstaged.Unsolved => msg"an unknown in object code was not determined by elaboration"
        case Unstaged.NotObjectCode => msg"only object terms and formulas can occur in object items"
      )
    case _: IntegerCrossing =>
      List(
        msg"meta integers are unbounded; object integers are 64-bit, from -9223372036854775808 to 9223372036854775807",
        msg"a meta integer is checked against this range where it is used as object code"
      )
    case _: NoMetaInt =>
      List(msg"the meta `int` is the family `int` of `std/nat`, with its arithmetic in `std/int`, which the prelude imports")
    case _: IncompleteHead => List(msg"a rule head must apply a relation (or a constructor) to all of its columns")
    case _: InvalidHead => List(msg"a rule head is an atom of a relation or a constructor term")
    case UnsolvedGoal(_, g, st, ctx, _) =>
      msg"the hole stands for ${Lit(if st == "object" then "object code" else "a meta value")} of type ${Src(g)}" ::
        (if ctx.isEmpty then Nil else List(msg"in scope: ${Lit(ctx.map(x => s"`$x`").mkString(", "))}"))
    case NoImplicitNamed(_, f, Nil, _) => List(msg"${Src(f)} takes no implicit argument before its next explicit argument")
    case NoImplicitNamed(_, f, all, _) =>
      // the anonymous database of a declaration's judgments has no name to give (#186 P7c)
      all.filterNot(hugin.core.Printing.isAnonymousDatabase) match
        case Nil => List(msg"${Src(f)} takes no implicit argument by name before its next explicit argument")
        case as =>
          List(msg"${Src(f)} takes the implicit arguments ${Lit(as.map(a => s"`$a`").mkString(", "))} before its next explicit argument")
    case _: NamedArgumentAlone =>
      List(msg"`{x := e}` gives the implicit argument `x` of the function it is applied to, or binds it in a pattern")
    case _: AppliedRelation =>
      List(
        msg"as a meta type, an applied relation would be `⇑(r t̄)`, the lift of a fact type of an application, which no object term has: the fact type of a relation `r` is `r` alone",
        msg"an applied relation is a proposition of the program that owns it: a relation of an instance, a module or a functor application `(f ā).r`, or one opened from an instance; a variable's relation is read by every program over it; a relation of the file, of a module body or of a functor's parameter is a proposition, written alone, in the declarations of that file or body"
      )
    case _ => Nil

  override def helps: List[Msg] = this match
    case ObjectForMeta(_, f, _) =>
      List(Msg.text(s"to take object code as an argument, declare the parameter with an object type (`⇑$f` at the meta level)"))
    case NoField(_, _, _, Some(s), _) => List(msg"did you mean ${Src(s)}?")
    case UnsolvedGoal(_, g, _, _, _) => List(msg"replace the hole with an expression of type ${Src(g)}")
    case _: IntegerCrossing =>
      List(msg"test the value with `fits64` (std/int) where it may not fit, and use object code only in the branch where it does")
    case _: NoMetaInt => List(msg"compile the program with the prelude, or use object integers only")
    case AppliedRelation(r, _, _, true) =>
      List(
        msg"without the `⇑`, an applied relation that a program owns is its judgment; for another relation, name the program with the turnstile: ${Src(s"P ⊢ $r")}"
      )
    case AppliedRelation(r, false, _, _) => List(msg"name the program with the turnstile: ${Src(s"P ⊢ $r")}")
    case AppliedRelation(r, true, _, _) => List(msg"name the program with the turnstile, in a function: ${Src(s"[x̄] P ⊢ $r x̄")}")
    case _ => Nil
