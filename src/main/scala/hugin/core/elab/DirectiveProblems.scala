package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of directives as meta functions (reference: directives): resolution (E0101), the type of the
 *  application (E1001, E1002), what the application returns (E1000, E1003), and the primitive
 *  attributes it attaches (E0701). */
enum DirectiveProblem extends Problem:
  /** `%d` where no `d` is in scope; `similar` is a directive in scope with a similar name. */
  case UnknownDirective(name: String, at: Span, similar: Option[String])

  /** `%d …` whose application has type `tpe`, which is not a directive's. */
  case NotADirective(shown: String, tpe: String, at: Span)

  /** `%d …` attached to a declaration although `d …` does not have type `decl -> decl`. */
  case NotAttachable(shown: String, tpe: String, at: Span, decl: Span)

  /** A directive attached to the declaration of `expected` returned the declaration of `found`. */
  case ChangedDeclaration(expected: String, found: String, at: Span)

  /** A directive rejected its arguments with `message` (`ierror`, `derror` in its result). */
  case Rejected(text: String, at: Span)

  /** An attribute about a relation for something that is not one. */
  case NotARelation(directive: String, at: Span)

  /** An attribute other than `%derivations` for a rule. */
  case NotForRules(directive: String, rule: String, at: Span)

  /** `%terminates l r t̄`: a measure of labels with a call pattern. */
  case LabelsWithPattern(at: Span)

  def code: Code = this match
    case _: UnknownDirective => Code.E0101
    case _: NotADirective => Code.E1001
    case _: NotAttachable => Code.E1002
    case _: ChangedDeclaration => Code.E1003
    case _: Rejected => Code.E1000
    case _: NotARelation | _: NotForRules | _: LabelsWithPattern => Code.E0701

  def primary: Span = this match
    case UnknownDirective(_, s, _) => s
    case NotADirective(_, _, s) => s
    case NotAttachable(_, _, s, _) => s
    case ChangedDeclaration(_, _, s) => s
    case Rejected(_, s) => s
    case NotARelation(_, s) => s
    case NotForRules(_, _, s) => s
    case LabelsWithPattern(s) => s

  def message: Msg = this match
    case UnknownDirective(n, _, _) => msg"unknown directive ${Src("%" + n)}"
    case NotADirective(d, _, _) => msg"${Src(d)} is not a directive"
    case NotAttachable(d, _, _, _) => msg"${Src(d)} cannot be attached to a declaration"
    case ChangedDeclaration(e, f, _) => msg"the directive returned the declaration of ${Src(f)} for that of ${Src(e)}"
    case Rejected(m, _) => Msg.text(m)
    case NotARelation(d, _) => msg"${Src(d)} expects a relation"
    case NotForRules(d, r, _) => msg"${Src(d)} does not apply to the rule ${Src("@" + r)}"
    case _: LabelsWithPattern => msg"a measure of labels names the relation without arguments"

  override def primaryLabel: Msg = this match
    case _: UnknownDirective => msg"not found in this scope"
    case NotADirective(_, t, _) => msg"its application has type ${Src(t)}"
    case NotAttachable(_, t, _, _) => msg"has type ${Src(t)}, not `decl -> decl`"
    case _: ChangedDeclaration => msg"attached here"
    case _: Rejected => msg"reported by this directive"
    case _: NotARelation => msg"not a relation"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case NotAttachable(_, _, _, decl) => List(decl -> msg"the declaration that follows")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: UnknownDirective =>
      List(msg"a directive `%d` applies the meta function `d` in scope; the prelude declares the primitive ones")
    case _: NotADirective | _: NotAttachable =>
      List(
        msg"a directive's application has type `decl` (it changes a declaration), `module -> module` (it rewrites the file's rules) or `seq item` (it adds items; also `item`, `rule`, `seq rule`)"
      )
    case _: ChangedDeclaration => List(msg"a directive attached to a declaration may change only that declaration")
    case _: LabelsWithPattern =>
      List(msg"`%terminates n r` names the column `n` of `r`; `%terminates N (r N _)` names a variable of a call pattern")
    case _ => Nil

  override def helps: List[Msg] = this match
    case UnknownDirective(_, _, Some(s)) => List(msg"a directive with a similar name exists: ${Src("%" + s)}")
    case _: NotAttachable => List(msg"end the directive with `.` if it is not meant to apply to the declaration")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case UnknownDirective(_, at, Some(s)) =>
      List(Suggestion.replace(at, "%" + s, msg"replace with ${Src("%" + s)}", Applicability.MaybeIncorrect))
    case NotAttachable(_, _, at, _) => List(Suggestion.replace(at.endPoint, ".", msg"add `.`", Applicability.MaybeIncorrect))
    case _ => Nil
