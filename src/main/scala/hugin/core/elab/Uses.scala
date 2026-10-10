package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** `%use` and `%export` (reference: modules): the two items that connect a file's scope with module
 *  values.
 *
 *  - `%use m.` opens the fields of the module `m` into the file's scope, and `%use m (x, y).` only the
 *    fields named. The fields are those of `m`'s *type*, so a signature that `m` was ascribed (also a
 *    file's `%export`) decides what is opened. An opened name denotes the global that the field is, when
 *    the field is a declaration (an import's fields are), so an opened constructor is still a
 *    constructor; another field is opened as a definition equal to the projection. Opened names are
 *    between the file's own declarations, which shadow them in the whole file, and the enclosing scope;
 *    a name opened for two different globals is ambiguous where it is used (E0109).
 *  - `%export S.` ascribes the file's module value the signature `S`, as `(file : S)` would: an import
 *    of the file is the record of `S`'s fields (transparent: types stay their definitions, constructors
 *    constructors). It is elaborated after the file's declarations; a second one, or one in a module
 *    body, is E0110. */
trait Uses:
  self: Elaborator =>
  import core.*

  // ---------------------------------------------------------------- %use

  def elabUse(d: Directive, module: Tree, names: Option[List[Ident]]): Unit =
    val c = Cxt.empty
    val (tm, ty, _) = insertAll(c, module.span, infer(c, module))
    force(ty) match
      case rt: Val.RecTy =>
        val labels = names match
          case None => rt.labels
          case Some(ns) =>
            for n <- ns if !rt.labels.contains(n.name) do
              fail(TypeProblem.NoField(n.name, show(c, ty), rt.labels, similarName(n.name, rt.labels), n.span))
            ns.map(_.name).distinct
        val ztm = zonk(Nil, 0, tm)
        val v = eval(Nil, ztm)
        val found = labels.map(l => l -> fieldTerm(ztm, l).flatMap(entity).getOrElse(alias(l, ztm, rt, v, d.span)))
        for (l, id) <- found do
          val before = state.opened.getOrElse(l, Nil)
          if !before.exists(_._1 == id) then state.opened = state.opened.updated(l, before :+ (id, d.span))
      case other => fail(ElabProblem.NotAModule(hugin.syntax.Printer.show(module), show(c, other), module.span))

  /** The global an opened name denotes, unless the name is ambiguous. */
  def openedGlobal(n: Name): Option[Option[Int]] = state.opened.get(n).map {
    case List((id, _)) => Some(id)
    case _ => None
  }

  /** E0109 if `n` is opened for two different globals and the file does not declare it. */
  def checkAmbiguous(n: Name, span: Span): Unit =
    if !state.declaredHere(n) && scope.get(n).isEmpty then
      state.opened.get(n) match
        case Some(all @ (_ :: _ :: _)) => fail(ElabProblem.AmbiguousName(n, span, all.map(_._2)))
        case _ => ()

  /** The term of field `l` of the module term `m`, where it can be read off the term: a record (an
   *  import, a coerced record), a definition of one, a projection of one. */
  private def fieldTerm(m: Tm, l: Name): Option[Tm] = m match
    case Tm.Rec(fs) => fs.collectFirst { case (`l`, t) => t }
    case Tm.Global(id) =>
      kindOf(id) match
        case GlobalKind.Definition(t, _) => fieldTerm(t, l)
        case _ => None
    case Tm.Proj(m2, l2) => fieldTerm(m2, l2).flatMap(fieldTerm(_, l))
    case _ => None

  /** The global a field term is: a declaration (as a meta constant, or quoted as an object constant). */
  private def entity(t: Tm): Option[Int] = t match
    case Tm.Global(id) => Some(id)
    case Tm.Quote(Tm.Global(id)) => Some(id)
    case Tm.Proj(m, l) => fieldTerm(m, l).flatMap(entity)
    case _ => None

  /** A field that is not a declaration (a member of a module instance, a computed value): a definition
   *  equal to the projection, without a name in scope (the name is opened). */
  private def alias(l: Name, m: Tm, rt: Val.RecTy, v: Val, span: Span): Int =
    val fty = fieldType(rt, v, l).getOrElse(throw Impossible(s"no field $l"))
    val proj = Tm.Proj(m, l)
    declareHidden(Ident(l)(span), quote(0, fty), Stage.S1, GlobalKind.Definition(proj, eval(Nil, proj)), span)

  // ---------------------------------------------------------------- %export

  def elabExport(d: Directive, signature: Tree): Unit =
    state.exported.foreach((first, _) => fail(ElabProblem.MisplacedExport(d.span, Some(first))))
    val c = Cxt.empty
    val sty = zonk(Nil, 0, checkType(c, signature, Stage.S1))
    val sv = eval(Nil, sty)
    force(sv) match
      case _: Val.RecTy => ()
      case other =>
        fail(ElabProblem.SignatureMismatch("a signature (a record type)", s"`%export` was given `${show(c, other)}`", signature.span))
    val full = fileModule
    val coerced =
      try coe(c, d.span, full.value, eval(Nil, full.ty), Stage.S1, sv, Stage.S1)
      catch
        case e: ElabError => throw ElabError(e.diag.withNote("the file's module does not match its `%export`"), e.unresolved, e.silent)
    state.exported = Some((d.span, ImportedModule(zonk(Nil, 0, coerced), sty, full.dropped)))
