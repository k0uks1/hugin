package hugin.core
package elab

import hugin.compiler.{Sym, SymKind}
import hugin.syntax.Printer
import hugin.syntax.Trees.*
import hugin.util.Span

/** What the elaborator records for tooling in the semantic index ([[hugin.compiler.SemanticIndex]]): the
 *  declarations with their descriptions (hover), the references of names to them (go to definition, find
 *  references, semantic tokens), the members of modules and the fields of signatures (also through
 *  paths `m.x`), the column labels of relations (completion in named patterns) and the names in scope. */
trait Tooling:
  self: Elaborator =>
  import core.*

  /** The tooling symbol of a global. */
  def symOf(id: Int): Sym =
    val g = globals(id)
    val name = if g.span.exists then g.span.text else g.name
    Sym(name, kindOf(id), g.span, if g.declSpan.exists then g.declSpan else g.span)

  private def kindOf(id: Int): SymKind = globals(id).kind match
    case GlobalKind.Object(d) => objectKind(d)
    case GlobalKind.Family(d, _) => objectKind(d)
    case _ => metaKind(globals(id).ty)

  private def objectKind(d: ObjDecl): SymKind = d match
    case ObjDecl.OpenType | ObjDecl.Refinement(_) => SymKind.ObjType
    case ObjDecl.Relation => SymKind.Rel
    case ObjDecl.Constructor(_) => SymKind.Ctor
    case ObjDecl.Struct(_) => SymKind.Struct

  /** A meta-level name by its type: a formula function returns `⇑prop`, a type definition `type`. */
  private def metaKind(ty: Val): SymKind = force(telescope(ty)._2) match
    case Val.Lift(Val.PropT) | Val.PropT => SymKind.FormulaFn
    case Val.Lift(Val.U0) | Val.U0 => SymKind.TypeDef
    case _ => SymKind.MetaDef

  /** What a field of a module or signature declares, by its type: an object constant (`⇑τ`) or a meta
   *  value. */
  private def fieldKind(ty: Val): SymKind = force(ty) match
    case Val.Lift(t) =>
      force(t) match
        case Val.U0 => SymKind.ObjType
        case o if isRelationType(o) => SymKind.Rel
        case _: Val.Pi => SymKind.Ctor
        case _ => SymKind.MetaDef
    case other => metaKind(other)

  /** A use of the global `id` at `span`. */
  def recordUse(span: Span, id: Int): Unit = index.reference(span, symOf(id))

  /** A use of the parameter `b` at `span`. */
  def recordParamUse(c: Cxt, span: Span, b: Binder): Unit = paramSym(c, b).foreach(index.reference(span, _))

  private def paramSym(c: Cxt, b: Binder): Option[Sym] = b.origin match
    case BinderOrigin.Param(declared, _) =>
      val sym = Sym(b.name, SymKind.MetaParam, declared, declared)
      index.declare(sym)
      index.describe(sym, s"meta parameter ${b.name} : ${show(c, b.ty)}")
      Some(sym)
    case _ => None

  /** The declaration of the global `id` by the item `item`: its description, labels and members. */
  def recordDeclaration(id: Int, item: Item): Unit =
    val g = globals(id)
    val sym = symOf(id)
    val description = g.kind match
      case GlobalKind.Definition(tm, v) if force(v).isInstanceOf[Val.RecTy] => s"signature ${sym.name} = ${showPlain(Nil, tm)}"
      case _ => describe(sym, item, isFact(g.kind), showPlain(Nil, g.tyTm))
    declared(sym, description, g.ty)

  private def declared(sym: Sym, description: String, ty: Val): Unit =
    index.declare(sym)
    index.describe(sym, description)
    index.labels(sym, labelsOf(ty))
    force(ty) match
      case rt: Val.RecTy => index.members(sym, fieldSyms(rt))
      case _ =>

  private def isFact(k: GlobalKind): Boolean = k match
    case GlobalKind.Object(ObjDecl.Constructor(f)) => f
    case GlobalKind.Object(ObjDecl.Struct(f)) => f
    case GlobalKind.Family(ObjDecl.Constructor(f), _) => f
    case _ => false

  /** `relation len A : (l : list A) -> (n : int) -> rel`: the kind, the name with its parameters and the
   *  type as written by a declaration, or `shown` (the elaborated type) for a definition without one. */
  private def describe(sym: Sym, item: Item, fact: Boolean, shown: => String): String =
    val written = item match
      case d: Decl =>
        val params = (d.params.map(paramText) ++ freeVars(d.tpe, Set.empty).map(_.name)).distinct
        Some(s"${sym.name}${params.map(" " + _).mkString} : ${typeText(d.tpe)}")
      case _ => None
    s"${if fact then "%fact " else ""}${sym.kind.describe} ${written.getOrElse(s"${sym.name} : $shown")}"

  /** A type as written, arrows without redundant parentheses. */
  private def typeText(t: hugin.syntax.Tree): String = t match
    case Arrow(None, d, c) => s"${arrowArg(d)} -> ${typeText(c)}"
    case Arrow(Some(l), d, c) => s"(${l.name} : ${typeText(d)}) -> ${typeText(c)}"
    case other => Printer.show(other)

  private def arrowArg(t: hugin.syntax.Tree): String = t match
    case _: Arrow => s"(${typeText(t)})"
    case other => typeText(other)

  private def paramText(p: Param): String = p match
    case Param.VarParam(v) => v.name
    case Param.Typed(n, _, _) => nameOf(n)

  /** The labels of a relation's or constructor's columns (the names of its Π binders). */
  private def labelsOf(ty: Val): List[String] =
    val (binders, result) = telescope(ty)
    val columns = force(result) match
      case Val.Lift(t) => telescope(t)._1
      case _ => binders
    columns.map(_._1).filter(l => l.nonEmpty && l != "_" && l.head.isLower)

  /** The fields of a record type as symbols (at their declarations, if known). */
  private def fieldSyms(rt: Val.RecTy): List[Sym] =
    var env = rt.env
    rt.labels.zip(rt.tys).zipWithIndex.map { case ((l, ty), k) =>
      val (name, decl) = rt.decls.lift(k).getOrElse((Span.NoSpan, Span.NoSpan))
      val kind = fieldKind(eval(env, ty))
      env = Val.local(rt.env.length + k) :: env
      Sym(l, kind, name, decl)
    }

  /** `q.l` at `sel`, a field of the record type `rt` of type `fty`: a reference to the field's declaration
   *  (in a module body, a signature or an imported file), described as seen through the path. */
  def recordFieldUse(c: Cxt, rt: Val.RecTy, sel: Select, fty: Val): Unit =
    val k = rt.labels.indexOf(sel.name)
    rt.decls.lift(k).foreach { (name, decl) =>
      val sym = Sym(sel.name, fieldKind(fty), name, decl)
      val path = Printer.show(sel)
      index.reference(sel.nameSpan, sym, Some(s"${sym.kind.describe} $path : ${objectType(c, fty)}"))
    }

  /** A field type as shown in a description: an object constant's type without its lift. */
  private def objectType(c: Cxt, ty: Val): String = force(ty) match
    case Val.Lift(t) => show(c, t)
    case other => show(c, other)

  /** A module body (in the context `c`, with its members in `cb`): its members are declared, and the
   *  names in scope in it are its members, the parameters around it and the top level. */
  def recordBody(c: Cxt, cb: Cxt, bodySpan: Span, members: List[Member], items: List[Item]): Unit =
    val byName = items.collect { case d: Decl => d.name.span -> (d: Item); case d: Def => d.name.span -> (d: Item) }.toMap
    val syms = members.zipWithIndex.map { (m, k) =>
      val b = cb.binder(c.lvl + k)
      val sym = Sym(m.name, fieldKind(b.ty), m.span, m.declSpan)
      val shown = objectType(cb, b.ty)
      declared(sym, byName.get(m.span).fold(s"${sym.kind.describe} ${m.name} : $shown")(describe(sym, _, false, shown)), b.ty)
      sym
    }
    val params = c.binders.reverse.flatMap(b => paramSym(c, b))
    index.scope(bodySpan, syms ++ params)

  /** The top level of a program for completion: its names and those of the prelude. */
  def recordTopLevel(): Unit =
    index.topLevel = (scope.values ++ file.parent.values).toList.distinct.map(symOf)
