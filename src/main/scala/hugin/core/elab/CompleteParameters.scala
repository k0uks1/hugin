package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.Span

/** A functor that negates or aggregates over a relation it is given must require it to be complete
 *  (`%complete l` in the parameter's signature, Section 11; E0210): otherwise it may be bound to an
 *  incomplete (`%open`) relation, whose missing facts mean unknown, not false. A relation parameter that
 *  is not part of a signature (`(r : A -> rel)`) cannot carry the requirement at all. */
trait CompleteParameters:
  self: Elaborator =>
  import core.*

  /** Checks an atom `atom` (elaborated) that the formula at `span` negates or aggregates over (`what`). */
  def requireComplete(c: Cxt, atom: Tm, span: Span, what: String): Unit =
    parameterRelation(c, atom).foreach { (b, label) =>
      val BinderOrigin.Param(declared, tpe) = b.origin: @unchecked
      label match
        case Some(l) =>
          force(b.ty) match
            case rt: Val.RecTy if !rt.reqs.exists { case SigReq.Complete(`l`, _) => true; case _ => false } =>
              val insertAt = signatureOf(tpe).flatMap(_.entries.lastOption).map(entryEnd)
              reporter.report(ElabProblem.IncompleteFieldParameter(what, b.name, l, span, declared, insertAt).toDiagnostic)
            case _ =>
        case None => reporter.report(ElabProblem.IncompleteRelationParameter(what, b.name, span, declared).toDiagnostic)
    }

  /** The parameter (and the field of its signature) whose relation the atom applies: `$(x.l) t̄` or
   *  `$x t̄` for a parameter `x`. */
  private def parameterRelation(c: Cxt, atom: Tm): Option[(Binder, Option[Name])] =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case other => other
    def param(ix: Int): Option[Binder] =
      Some(c.binder(c.lvl - ix - 1)).filter(_.origin.isInstanceOf[BinderOrigin.Param])
    head(atom) match
      case Tm.Splice(Tm.Proj(Tm.Var(ix), l)) => param(ix).map((_, Some(l)))
      case Tm.Splice(Tm.Var(ix)) => param(ix).filter(b => isRelationTypeLifted(b.ty)).map((_, None))
      case _ => None

  private def isRelationTypeLifted(ty: Val): Boolean = force(ty) match
    case Val.Lift(t) => isRelationType(t)
    case _ => false

  /** The signature of a parameter as written: a record type in the parameter, or the definition of the
   *  named signature in this file. */
  private def signatureOf(tpe: Tree): Option[RecordType] = tpe match
    case rt: RecordType => Some(rt)
    case Parens(i) => signatureOf(i)
    case Ident(n) => state.signatures.get(n)
    case _ => None

  private def entryEnd(e: SigEntry): Span = e match
    case SigEntry.FieldDecl(_, tpe) => tpe.span.endPoint
    case SigEntry.Complete(_, sp) => sp.endPoint

  /** The atoms an aggregate's body (or a negation) reads directly. */
  def atomsOf(t: Tm): List[(Tm, Span)] =
    def go(t: Tm, span: Span): List[(Tm, Span)] = t match
      case Tm.Obj(ObjForm.Loc(sp), List(u)) => go(u, sp)
      case Tm.Obj(ObjForm.And, as) => as.flatMap(go(_, span))
      case Tm.Obj(_, _) => Nil
      case other => List((other, span))
    go(t, Span.NoSpan)
