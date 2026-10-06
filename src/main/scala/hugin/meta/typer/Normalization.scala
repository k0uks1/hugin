package hugin.meta
package typer

import hugin.util.*
import hugin.syntax.*
import hugin.obj.OType
import hugin.obj

/** Substitution and static normal forms of meta expressions occurring in types (Section 4.3). */
private[meta] trait Normalization extends TyperBase:
  self: Typer =>
  import MExpr.*
  import MType.*

  // ======================================================================= substitution / normalization

  def substM(m: MExpr, s: Map[Sym, MExpr]): MExpr = if s.isEmpty then m
  else
    m match
      case Ref(x) => s.getOrElse(x, m)
      case Op(op, l, r, sp) => Op(op, substM(l, s), substM(r, s), sp)
      case Neg(x, sp) => Neg(substM(x, s), sp)
      case Proj(x, l) => Proj(substM(x, s), l)
      case Rec(fs) => Rec(fs.map((l, e) => (l, substM(e, s))))
      case App(f, a, sp) => App(substM(f, s), substM(a, s), sp)
      case QuoteType(t) => QuoteType(substO(t, s))
      case FactTypeOf(x) => FactTypeOf(substM(x, s))
      case TApp(f, as) => TApp(substM(f, s), as.map(substO(_, s)))
      case SigV(t) => SigV(substMT(t, s))
      case other => other

  def substO(t: OType, s: Map[Sym, MExpr]): OType = if s.isEmpty then t
  else
    OType.mapDeep(t) {
      case OType.Splice(m) => normO(OType.Splice(substM(m, s)))
    }

  def substMT(t: MType, s: Map[Sym, MExpr]): MType = if s.isEmpty then t
  else
    t match
      case Code(o) => Code(substO(o, s))
      case RelT(cols) => RelT(cols.map(c => c.copy(tpe = substO(c.tpe, s))))
      case Pi(x, d, c, imp) => Pi(x, substMT(d, s), substMT(c, s - x), imp)
      case Sig(fs, reqs) => Sig(fs.map((f, ft) => (f, substMT(ft, s))), reqs)
      case other => other

  /** Static normal form of meta expressions occurring in types (Section 4.3). */
  def normM(m: MExpr): MExpr = m match
    case Ref(s) if s.static.isDefined && (s.static.get ne m) => normM(s.static.get)
    case Proj(x, l) =>
      normM(x) match
        case Rec(fs) => fs.find(_._1 == l).map(f => normM(f._2)).getOrElse(Proj(Rec(fs), l))
        case nx => Proj(nx, l)
    case FactTypeOf(x) => FactTypeOf(normM(x))
    case TApp(f, as) => TApp(normM(f), as.map(normO))
    case QuoteType(t) =>
      normO(t) match
        case OType.Splice(inner) => inner
        case nt => QuoteType(nt)
    case Rec(fs) => Rec(fs.map((l, e) => (l, normM(e))))
    case other => other

  def normO(t: OType): OType = t match
    case OType.Splice(m) =>
      normM(m) match
        case QuoteType(inner) => normO(inner)
        case nm => OType.Splice(nm)
    case OType.Con(s, as) => OType.Con(s, as.map(normO))
    case OType.Fact(r, as) => OType.Fact(r, as.map(normO))
    case OType.Union(ms) => OType.union(ms.map(normO))
    case other => other

  def typesEqual(a: OType, b: OType): Boolean = normO(a) == normO(b)

  private[meta] def isStatic(m: MExpr): Boolean = m match
    case Ref(_) | Lit(_) | QuoteType(_) | SigV(_) => true
    case Proj(x, _) => isStatic(x)
    case Rec(fs) => fs.forall(f => isStatic(f._2))
    case FactTypeOf(x) => isStatic(x)
    case TApp(f, _) => isStatic(f)
    case _ => false
