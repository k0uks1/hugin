package hugin.core
package elab

import hugin.syntax.{Printer, Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

import scala.collection.mutable

/** The judgment coercion (reference: std/semantics, "Relations as propositions"; #186 P9b, level 3.5): an
 *  atom whose relation a program owns, written where a meta type is expected, is that program's judgment
 *  at the database a turnstile without `[e]` would have there; an unapplied owned relation where a family
 *  `⇑τ₁ -> … -> ⇑τₙ -> Type` is expected is `[x̄] P ⊢ r x̄` (the η form). Like stage inference's `⇑`, it is
 *  inserted by the expected type; it elaborates the [[Judgment]] that the turnstile would, so it adds no
 *  rule to the core, and the printer shows `P ⊢ r t̄`.
 *
 *  The owner is found from the syntax of the atom's head, without evaluating an application (Lean's
 *  `CoeSort` triggers on the expected sort in the same way, Rocq's coercions to `Sortclass` likewise):
 *
 *  - `m.r`, `m` a module or an instance by its path (`fast`, `trip`, `weak.v`);
 *  - `(f ā).r`, a global functor applied to explicit arguments (`(tc G).path`; a functor alone is not);
 *  - `r`, a name that denotes a relation of a module instance (opened by `%use`).
 *
 *  A variable's relation (`G.edge`), a relation of the file or of the enclosing body is owned by none and
 *  stays E0960, whose help names the turnstile. */
trait JudgmentCoercion:
  self: Elaborator =>
  import core.*

  /** The program that owns a coerced atom: written as a tree (a module path or a functor applied), or the
   *  instance whose relation an opened name denotes. */
  private enum Owner:
    case Written(program: Tree)
    case Opened(instance: ModuleInstance, alias: Int)

  /** An owned atom: its owner, its relation's name in the owner's body, its head (`fast.path`, `path`) and
   *  its arguments. */
  private final case class OwnedAtom(owner: Owner, rel: Name, head: Tree, args: List[Tree]):
    /** Where the atom's judgment is, for the anonymous database ([[BinderOrigin.Database]]). */
    def at: Span = head.span

  private def unparen(t: Tree): Tree = t match
    case Parens(i) => unparen(i)
    case other => other

  /** `t` as an atom (applied or not) whose relation a program owns, `local` the names bound around it. */
  private def ownedAtom(c: Cxt, t: Tree, local: Name => Boolean): Option[OwnedAtom] =
    val (h, args) = TreeOps.flattenApp(unparen(t))
    val head = unparen(h)
    if args.exists(_.isInstanceOf[NamedArg]) then None
    else
      head match
        case Select(q, r) if r.headOption.exists(_.isLetter) =>
          writtenBody(c, q, local).filter(ownsRelation(_, r)).map(_ => OwnedAtom(Owner.Written(unparen(q)), r, head, args))
        case Ident(n) if !local(n) && !state.bodyDeclared(n) =>
          lookupGlobal(n).flatMap(id => openedRelation(id).map((_, id))).flatMap { (rel, alias) =>
            instanceOwning(rel).map((inst, m) => OwnedAtom(Owner.Opened(inst, alias), m.name, head, args))
          }
        case _ => None

  /** The object relation a global denotes: itself, or the relation an opened name (a definition of type
   *  `⇑τ`, the projection of an instance's field) is. Decided from the type first, so that no other
   *  definition is unfolded. */
  private def openedRelation(id: Int): Option[Int] =
    def relationLike(r: Int) = globals(r).kind match
      case GlobalKind.Object(ObjDecl.Relation | ObjDecl.Struct | ObjDecl.Constructor) => true
      case _ => false
    val g = globals(id)
    if g.stage == Stage.S0 then Option.when(relationLike(id))(id)
    else
      (force(g.ty), g.kind) match
        case (Val.Lift(x), GlobalKind.Definition(_, v)) if isFactConstantType(x) =>
          forceData(v) match
            case Val.Quote(code) =>
              forceData(code) match
                case Val.Rigid(Head.Glob(r), Nil) if relationLike(r) => Some(r)
                case _ => None
            case _ => None
        case _ => None

  // ---------------------------------------------------------------- elaboration

  /** `t` checked against `a` as a coerced judgment, if it is one: an applied owned atom against a meta
   *  universe, or an unapplied one against a family of meta types (the η form). */
  def checkCoerced(c: Cxt, t: Tree, a: Val): Option[Tm] =
    if semanticsGlobals.isEmpty then None
    else
      unparen(t) match
        case _: Apply =>
          force(a) match
            case Val.U1(_) => inferCoerced(c, t).map((tm, ty, s) => coe(c, t.span, tm, ty, s, a, Stage.S1))
            case _ => None
        case _: Select | _: Ident =>
          force(a) match
            case pi @ Val.Pi(_, Icit.Expl, _, _) if familyArity(pi, c.lvl) > 0 =>
              ownedAtom(c, t, c.scope.contains).map(atom => checkEta(c, atom, pi))
            case _ => None
        case _ => None

  /** `t` inferred as a coerced judgment, if it is an applied owned atom (where a meta type is expected:
   *  [[Bidirectional.infer]] in a type position). Nothing is coerced without `std/semantics`, so that a
   *  program without it pays nothing (its applied relations are E0960). */
  def inferCoerced(c: Cxt, t: Tree): Option[(Tm, Val, Stage)] =
    if semanticsGlobals.isEmpty then None
    else
      unparen(t) match
        case _: Apply =>
          ownedAtom(c, t, c.scope.contains).filter(_.args.nonEmpty).map { atom =>
            val (program, judgmentTree) = judgmentOf(atom, t.span)
            val resolved = atom.owner match
              case Owner.Opened(inst, alias) =>
                state.used += alias
                recordUse(atom.head.span, alias)
                Some(instanceProgram(c, inst, program, atom.head.span))
              case Owner.Written(_) => None
            try inferJudgmentOf(c, judgmentTree, resolved)
            catch
              case e: ElabError if e.diag.code == hugin.util.diagnostics.Code.E0945 || e.diag.code == hugin.util.diagnostics.Code.E0961 =>
                val judgment = Printer.show(judgmentTree).stripPrefix("(").stripSuffix(")")
                val note = s"`${Printer.show(t)}` is read as the judgment `$judgment`: its relation belongs to `${Printer.show(program)}`"
                throw ElabError(e.diag.withNote(note), e.unresolved, e.silent)
          }
        case _ => None

  /** The judgment tree an atom stands for (with its program as a tree, for display when it is opened). */
  private def judgmentOf(atom: OwnedAtom, span: Span): (Tree, Judgment) =
    val relSpan = atom.head match
      case s: Select => s.nameSpan
      case other => other.span
    val program = atom.owner match
      case Owner.Written(p) => p
      case Owner.Opened(inst, _) => Ident(inst.prefix)(atom.head.span)
    val rel = atom.args.foldLeft(Ident(atom.rel)(relSpan): Tree)((f, x) => Apply(f, x)(f.span.to(x.span)))
    (program, Judgment(program, None, rel)(span, atom.at))

  /** The number of explicit binders of a family of meta types `(x₁ : A₁) -> … -> Type`, or 0; `lvl` is the
   *  size of the context of `a`. The codomains are looked at under fresh variables (never a wildcard: a
   *  dependent codomain may project from its variable, `(t : T) -> t.vars -> Type`), and a type that does
   *  not evaluate is no family. */
  private def familyArity(a: Val, lvl: Int): Int =
    try
      var t = force(a)
      var n = 0
      while t.isInstanceOf[Val.Pi] do
        t match
          case Val.Pi(_, Icit.Expl, _, cl) =>
            t = force(inst(cl, Val.local(lvl + n)))
            n += 1
          case _ => return 0
      t match
        case Val.U1(_) => n
        case _ => 0
    catch case _: Impossible => 0

  /** The η form: `r` against `(x₁ : A₁) -> … -> Type` is `[x̄] r x̄`, whose body is the coerced atom. The
   *  binders are named after the family's, fresh against the names in scope and in the atom's head. */
  private def checkEta(c: Cxt, atom: OwnedAtom, pi: Val): Tm =
    val taken = c.names ++ TreeOps.nodes(atom.head).collect { case Ident(n) => n; case VarRef(n) => n }.toList
    val fresh = FreshNames(taken)
    val names = mutable.ListBuffer.empty[Name]
    var ty = force(pi)
    while ty.isInstanceOf[Val.Pi] do
      ty match
        case Val.Pi(x, _, _, cl) =>
          names += fresh(if x.headOption.exists(_.isLower) then x else "x")
          ty = force(inst(cl, Val.local(c.lvl + names.length - 1)))
        case _ =>
    val sp = atom.head.span
    val body = names.foldLeft(atom.head)((f, x) => Apply(f, Ident(x)(Span.NoSpan))(sp))
    val lambda = names.foldRight(body)((x, acc) => Lambda(Ident(x)(Span.NoSpan), None, acc)(sp))
    check(c, lambda, pi, Stage.S1)

  // ---------------------------------------------------------------- the anonymous database

  /** The coerced atoms of a declaration's type `trees` (bound in `c`), found syntactically for its
   *  anonymous database (#186 P7c, P9b): an owned atom, applied or not, in a syntactic type position: the
   *  declared type, an arrow's domain and codomain, a binder's type, a field type of a record type, and an
   *  argument of a global constant whose parameter type is a universe or a family of types ending in one
   *  (`iff`, `symmetric`; for a family, also the body of a function written there). With the program
   *  written, if it is (for the types of the variables written as its arguments). Nothing without
   *  `std/semantics`. A coercion in another position has a database of its own (an unknown). */
  def coercionCandidates(trees: List[Tree], c: Cxt): List[(Option[Tree], Span)] =
    if semanticsGlobals.isEmpty then Nil
    else
      val out = mutable.ListBuffer.empty[(Option[Tree], Span)]
      def add(a: OwnedAtom): Unit =
        val program = a.owner match
          case Owner.Written(p) => Some(p)
          case _ => None
        out += ((program, a.at))
      def names(t: Tree): List[Name] = unparen(t) match
        case Ident(n) => List(n)
        case VarRef(n) => List(n)
        case _ => Nil
      def typePos(t: Tree, bound: Set[Name]): Unit = unparen(t) match
        case Arrow(label, dom, cod) =>
          typePos(dom, bound)
          typePos(cod, bound ++ label.map(_.name))
        case ImplicitPi(ns, dom, cod) =>
          typePos(dom, bound)
          typePos(cod, bound ++ ns.flatMap(names))
        case RecordType(entries) =>
          entries.foreach {
            case SigEntry.FieldDecl(_, tp) => typePos(tp, bound)
            case _ =>
          }
        case app: Apply =>
          val local = (n: Name) => bound(n) || c.scope.contains(n)
          ownedAtom(c, app, local) match
            case Some(a) if a.args.nonEmpty => add(a)
            case _ => arguments(app, bound, local)
        case _ =>
      def family(t: Tree, bound: Set[Name], local: Name => Boolean): Unit = unparen(t) match
        case Lambda(p, _, body) => typePos(body, bound ++ names(p))
        case other => ownedAtom(c, other, local).filter(_.args.isEmpty).foreach(add)
      def arguments(t: Tree, bound: Set[Name], local: Name => Boolean): Unit =
        val (head, args) = TreeOps.flattenApp(t)
        unparen(head) match
          case Ident(f) if !local(f) && !state.bodyDeclared(f) =>
            lookupGlobal(f).filter(globals(_).stage == Stage.S1).foreach { id =>
              // the parameter types, under fresh variables (a type that does not evaluate: none)
              val all =
                try telescope(globals(id).ty)._1
                catch case _: Impossible => Nil
              val params = all.filter(_._2 == Icit.Expl)
              args.filterNot(_.isInstanceOf[NamedArg]).zip(params).foreach { (a, p) =>
                // only the shapes that can hold a candidate: a type, a function, an unapplied path
                unparen(a) match
                  case _: Lambda | _: Select | _: Ident =>
                    force(p._3) match
                      case pi: Val.Pi if familyArity(pi, all.length) > 0 => family(a, bound, local)
                      case Val.U1(_) => typePos(a, bound)
                      case _ =>
                  case _: Apply | _: Arrow | _: ImplicitPi | _: RecordType =>
                    force(p._3) match
                      case Val.U1(_) => typePos(a, bound)
                      case _ =>
                  case _ =>
              }
            }
          case _ =>
      trees.foreach(typePos(_, Set.empty))
      out.toList
