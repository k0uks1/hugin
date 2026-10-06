package hugin.meta

import hugin.util.*
import hugin.syntax.Literal
import hugin.obj.*

/** Requirements on relation fields of a signature (Section 4.4). */
enum Req:
  case Complete(label: String, span: Span)
  case HasMode(label: String, mode: Mode, span: Span)

/** Meta types μ (Section 3.1). Dependency is through `OType.Splice` of paths. */
enum MType:
  /** ⇑τ */
  case Code(t: OType)

  /** `type` */
  case TypeU

  /** ⇑(τ̄ → rel): a relation; with a `result` type, ⇑(τ̄ → a): a constructor (its relation of facts, used
   *  as a relation or to build terms). */
  case RelT(cols: List[Column], result: Option[OType] = None)

  /** ⇑prop */
  case PropT

  /** b̂ */
  case Prim(b: BaseType)

  /** Π(x:μ).μ' — `implicit` for implicit type parameters. */
  case Pi(x: Sym, dom: MType, cod: MType, isImplicit: Boolean)

  /** {l1 : μ1, ...} with requirements; field symbols allow dependency on earlier fields. */
  case Sig(fields: List[(Sym, MType)], reqs: List[Req])

  /** `mod`, the universe of meta types (the type of signatures). */
  case ModU
  case Err

  def show: String = MType.show(this)

object MType:
  def show(t: MType): String = t match
    case Code(o) => s"⇑${showO(o)}"
    case TypeU => "type"
    case RelT(cols, res) =>
      s"⇑(${(cols.map(c => c.label.map(l => s"$l : ").getOrElse("") + showO(c.tpe)) :+ res.map(showO).getOrElse("rel")).mkString(" -> ")})"
    case PropT => "⇑prop"
    case Prim(b) => b.show
    case Pi(x, d, c, imp) =>
      val dom = if imp then s"{${x.name} : ${show(d)}}" else if x.name.startsWith("_") then showArg(d) else s"(${x.name} : ${show(d)})"
      s"$dom -> ${show(c)}"
    case Sig(fs, reqs) =>
      (fs.map((s, t) => s"${s.name} : ${show(t)}") ++ reqs.map {
        case Req.Complete(l, _) => s"%complete $l"
        case Req.HasMode(l, m, _) => s"%mode $l ${m.inputs.map(b => if b then "+" else "-").mkString(" ")}"
      }).mkString("{ ", ", ", " }")
    case ModU => "mod"
    case Err => "<error>"
  private def showArg(t: MType) = t match
    case _: Pi => s"(${show(t)})"
    case _ => show(t)
  private def showO(o: OType): String = o match
    case OType.Union(_) | OType.Con(_, _ :: _) | OType.Fact(_, _ :: _) => s"(${o.show})"
    case _ => o.show

/** Elaborated meta expressions with explicit quotes and splices (output of `typer`). */
enum MExpr:
  case Ref(sym: Sym)
  case Lit(l: Literal)
  case Op(op: ArithOp, l: MExpr, r: MExpr, span: Span)
  case Neg(m: MExpr, span: Span)
  case Proj(m: MExpr, label: String)
  case Rec(fields: List[(String, MExpr)])
  case Lam(param: Sym, body: MExpr)
  case App(f: MExpr, arg: MExpr, span: Span)

  /** ⟨t⟩ for object terms. */
  case QuoteTerm(t: Term)

  /** ⟨φ̄⟩ for formulas. */
  case QuoteFormula(body: List[Formula])

  /** An object type as a meta value of type `type`. */
  case QuoteType(t: OType)

  /** The fact type of a relation-valued expression. */
  case FactTypeOf(m: MExpr)

  /** Family application `f τ̄`. */
  case TApp(f: MExpr, args: List[OType])

  /** A module body. `hint` is used to build readable fresh prefixes. */
  case Body(items: List[EItem], scope: Scope, span: Span)

  /** A signature as a value (`graph : mod = {...}`). */
  case SigV(t: MType)
  case Err

object MExpr:
  def show(m: MExpr): String = m match
    case Ref(s) => s.name
    case Lit(l) => l.show
    case Op(op, l, r, _) => s"(${show(l)} ${op.show} ${show(r)})"
    case Neg(x, _) => s"-${show(x)}"
    case Proj(x, l) => s"${show(x)}.$l"
    case Rec(fs) => fs.map((l, e) => s"$l = ${show(e)}").mkString("{ ", ", ", " }")
    case Lam(p, b) => s"[${p.name}] ${show(b)}"
    case App(f, a, _) => s"${show(f)} ${showArg(a)}"
    case QuoteTerm(t) => s"⟨${ObjPrinter.term(t)}⟩"
    case QuoteFormula(b) => s"⟨${ObjPrinter.body(b)}⟩"
    case QuoteType(t) => s"⟨${t.show}⟩"
    case FactTypeOf(x) => s"factType(${show(x)})"
    case TApp(f, as) => (show(f) :: as.map(a => s"⟨${a.show}⟩")).mkString(" ")
    case Body(items, _, _) => s"{ ${items.length} items }"
    case SigV(t) => t.show
    case Err => "<error>"
  private def showArg(m: MExpr) = m match
    case _: App | _: Lam => s"(${show(m)})"
    case _ => show(m)

/** Elaborated items of a module body. */
enum EItem:
  case TypeDecl(sym: Sym, kind: TypeKindE, span: Span)
  case RelDecl(sym: Sym, cols: List[Column], result: Option[OType], isStruct: Boolean, span: Span)
  case EdgeDecl(sub: OType, sup: MExpr, span: Span)
  case MetaDef(sym: Sym, rhs: MExpr, span: Span)
  case RuleItem(rule: Rule)
  case QueryItem(q: Query)
  case DirectiveItem(d: Directive)

enum TypeKindE:
  case Open
  case Refinement(base: OType)
