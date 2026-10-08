package hugin.obj

import hugin.syntax.{AggKind, Bound}
import hugin.util.diagnostics.{DiagArg, Seg}

/** An object variable as written by the user (see [[Var.display]]), for messages. */
final case class VarName(name: String)

/** How object-level values appear in messages: relations, types and operators in code style. Import
 *  `hugin.obj.DiagArgs.given` in a problem inventory. */
object DiagArgs:
  given DiagArg[RelSym] = DiagArg(r => Seg.Code(r.name))
  given DiagArg[TypeSym] = DiagArg(t => Seg.Code(t.name))
  given DiagArg[OType] = DiagArg(t => Seg.Type(t.show))
  given DiagArg[VarName] = DiagArg(v => Seg.Code(Var.display(v.name)))
  given DiagArg[ArithOp] = DiagArg(op => Seg.Code(op.show))
  given DiagArg[CmpOp] = DiagArg(op => Seg.Code(op.show))
  given DiagArg[AggKind] = DiagArg(k => Seg.Code(k.show))
  given DiagArg[Bound] = DiagArg(b => Seg.Code(b.show))

  /** Terms and formulas as printed by [[ObjPrinter]]. */
  given DiagArg[Term] = DiagArg(t => Seg.Code(ObjPrinter.term(t)))
  given DiagArg[Formula] = DiagArg(f => Seg.Code(ObjPrinter.formula(f)))
