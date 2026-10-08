package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Declarations of object constants beyond `x : A.` (reference: object/index): structs `s : type = { l : τ, … }.`,
 *  refinements `a : type <: b.`, subtyping edges `τ <: a.`, and the classification of a declared object
 *  constant ([[ObjDecl]]). The core records what they declare; whether the subtyping makes sense is
 *  checked by the object typer on the staged program. */
trait ObjectDecls:
  self: Elaborator =>
  import core.*

  /** The kind of an object constant declared `x : A.` with the (closed) object type `ty`. */
  def objectDecl(d: Decl, ty: Val): ObjDecl = force(ty) match
    case Val.U0 => ObjDecl.OpenType
    case other =>
      dupLabels(hugin.syntax.TreeOps.flattenArrow(d.tpe)._1.flatMap(_._1))
      if isRelationType(other) then ObjDecl.Relation
      else
        constructorResult(other) match
          case Val.Rigid(Head.Glob(id), Nil) if globals(id).kind.isInstanceOf[GlobalKind.Object] && !isOpen(id) =>
            fail(ElabProblem.Unclassifiable(d.name.name, globals(id).name, false, d.tpe.span))
          case Val.FactTy(r) =>
            // the fact type of a struct or relation is closed: its values are the facts
            val name = force(r) match
              case Val.Rigid(Head.Glob(id), _) => globals(id).name
              case _ => hugin.syntax.TreeOps.codomain(d.tpe).span.text
            fail(ElabProblem.Unclassifiable(d.name.name, name, false, d.tpe.span))
          case _ => ObjDecl.Constructor

  private def constructorResult(ty: Val): Val = force(ty) match
    case Val.Pi(_, _, _, cl) => constructorResult(inst(cl, Val.Wild))
    case other => other

  private def isOpen(id: Int): Boolean = globals(id).kind == GlobalKind.Object(ObjDecl.OpenType)

  def isStructDecl(d: Decl): Boolean = (d.tpe, d.defn) match
    case (Keyword(Kw.Type), Some(_: RecordType)) => true
    case _ => false

  /** The kind of a family of object constants, if `ty` (closed) is the type of one: binders over object
   *  types only (`{A : ⇑type} -> …`), and an object constant's type as result (`⇑$(list A)`). */
  def familyKind(d: Decl, ty: Val): Option[GlobalKind.Family] =
    val (binders, result) = telescope(ty)
    val overTypes = binders.nonEmpty && binders.forall(b => force(b._3) == Val.Lift(Val.U0))
    force(result) match
      case Val.Lift(t) if overTypes && isObjectConstantType(t) => Some(GlobalKind.Family(objectDecl(d, t), binders.length))
      case _ => None

  /** `s : type = { l₁ : τ₁, … }.`: the relation `s : (l₁ : τ₁) -> … -> rel`, whose fact type is `s`; with
   *  parameters (`pair A B : type = { … }.`) a family of structs. */
  def elabStruct(d: Decl): Unit =
    if d.params.isEmpty then elabPlainStruct(d)
    else
      val (c, ps) = bindParams(Cxt.empty, d.params, (_, _) => Tm.Lift(Tm.U0))
      val ty = pis(ps, Icit.Expl, Tm.Lift(structType(c, d)))
      declare(d.name, ty, Stage.S1, GlobalKind.Family(ObjDecl.Struct, ps.length), d.span)

  private def elabPlainStruct(d: Decl): Unit =
    declare(d.name, structType(Cxt.empty, d), Stage.S0, GlobalKind.Object(ObjDecl.Struct), d.span)

  def structType(c: Cxt, d: Decl): Tm =
    val entries = d.defn.get.asInstanceOf[RecordType].entries
    val fields = entries.map {
      case SigEntry.FieldDecl(l, t) => (l, t)
      case SigEntry.Complete(_, sp) => fail(ElabProblem.StructRequirement(sp))
    }
    dupLabels(fields.map(_._1))
    columnsType(c, fields.map((l, t) => (l.name, t)), Tm.RelT)

  /** `(l₁ : τ₁) -> … -> result` over object column types (labels are not in scope: object arrows are not
   *  dependent). */
  def columnsType(c: Cxt, cols: List[(Name, Tree)], result: Tm): Tm = cols match
    case Nil => Tm.shift(result, c.lvl)
    case (l, t) :: rest =>
      val dt = columnType(c, t)
      Tm.Pi(l, Icit.Expl, dt, columnsType(newBinder(c, l, ev(c, dt), Stage.S0), rest, result))

  /** The type of a column: an object type, or a bound column type `min τ` / `max τ` (reference: object/bound-columns,
   *  validated at the object level by `obj/check/BoundColumns`). */
  def columnType(c: Cxt, t: Tree): Tm = t match
    case Parens(i) => columnType(c, i)
    case BoundType(k, inner) => Tm.Obj(ObjForm.BoundCol(k), List(check(c, inner, Val.U0, Stage.S0)))
    case _ => check(c, t, Val.U0, Stage.S0)

  /** `a : type <: b.` */
  def elabRefinement(d: Decl): Unit =
    d.tpe match
      case Keyword(Kw.Type) if d.params.isEmpty && d.defn.isEmpty =>
        val base = check(Cxt.empty, d.sup.get, Val.U0, Stage.S0)
        declare(d.name, Tm.U0, Stage.S0, GlobalKind.Object(ObjDecl.Refinement(zonk(Nil, 0, base))), d.span)
      case _ =>
        fail(ElabProblem.RefinementOfNonType(d.sup.get.span))

  /** `τ <: a.`: the object type `τ` (an object type, a relation's or constructor's fact type) becomes a
   *  subtype of the open type `a`. */
  def elabEdge(e: SubEdge): Unit = items += edgeItem(Cxt.empty, e)

  def edgeItem(c: Cxt, e: SubEdge): CoreItem =
    val sub = check(c, e.sub, Val.U0, Stage.S0)
    val sup = check(c, e.sup, Val.U0, Stage.S0)
    force(ev(c, sup)) match
      case Val.Rigid(Head.Glob(id), Nil) if globals(id).kind == GlobalKind.Object(ObjDecl.OpenType) =>
      case Val.Rigid(Head.Glob(id), Nil) if globals(id).stage == Stage.S0 =>
        fail(ElabProblem.NotOpenType(globals(id).name, e.sup.span, globals(id).span))
      case _ => fail(ElabProblem.EdgeTarget(e.sup.span))
    CoreItem.EdgeItem(zonk(c.env, c.lvl, sub), zonk(c.env, c.lvl, sup), e.span)

  // ------------------------------------------------------------------ cycles between object declarations

  /** Declares the object relations, structs and constructors among `items` as pending globals (see
   *  [[GlobalEntry]]), so that declarations elaborated before them can use them as types. Constructors
   *  are recognised by a result type declared `x : type.` in the module. */
  def predeclare(items: List[Item]): Unit =
    val objectTypes = items.collect { case d: Decl if d.tpe == Keyword(Kw.Type) && d.defn.isEmpty => d.name.name }.toSet
    for
      d <- items.collect { case d: Decl => d }
      if !scope.contains(d.name.name) && d.params.isEmpty && !hugin.syntax.TreeOps.hasSyntaxErrors(d)
    do
      shapeOf(d, objectTypes).foreach { kind =>
        val id =
          addGlobal(GlobalEntry(
            file.objectName(d.name.name),
            Val.RelT,
            Tm.RelT,
            Stage.S0,
            GlobalKind.Object(kind),
            d.name.span,
            d.span,
            pending = true
          ))
        scope(d.name.name) = id
      }

  /** The kind of object constant a declaration declares, if its syntax tells. */
  private def shapeOf(d: Decl, objectTypes: Set[Name]): Option[ObjDecl] =
    if isStructDecl(d) then Some(ObjDecl.Struct)
    else if d.defn.isDefined || d.sup.isDefined then None
    else if endsInRel(d.tpe) then Some(ObjDecl.Relation)
    else
      hugin.syntax.TreeOps.flattenArrow(d.tpe) match
        case (_ :: _, Ident(n)) if objectTypes(n) => Some(ObjDecl.Constructor)
        case _ => None

  /** Sets the type of a pending global, now that its declaration is elaborated. */
  def completePending(id: Int, ty: Tm, kind: GlobalKind): Int =
    val g = globals(id)
    g.tyTm = ty
    g.ty = eval(Nil, ty)
    g.kind = kind
    g.pending = false
    items += CoreItem.GlobalItem(id)
    id

  /** Removes the pending globals whose declarations failed: their uses are unresolved names. */
  def dropPending(): Unit =
    scope.filterInPlace((_, id) => !globals(id).pending)

  /** A pending global at the head of `t` cannot be applied yet: the item is retried after its declaration. */
  def requireDeclared(t: Tm): Unit =
    def head(t: Tm): Tm = Tm.unloc(t) match
      case Tm.App(f, _, _) => head(f)
      case other => other
    head(t) match
      case Tm.Global(id) if globals(id).pending =>
        val name = scope.collectFirst { case (n, i) if i == id => n }.getOrElse(globals(id).name)
        throw ElabError(ElabProblem.UsedBeforeDeclaration(name, globals(id).span).toDiagnostic, Some(name))
      case _ =>
