package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

import scala.collection.mutable

/** `match` and `rewrite` on the right-hand side (reference: meta/match; design note `docs/design/proofs.md`,
 *  4.2, batch P3). Hugin follows Lean 4's right-hand-side `match` (`src/Lean/Elab/Match.lean`, the motive
 *  generalises the scrutinee in the expected type) and Idris 2's `rewrite … in` (`theorems.rst`), so the
 *  heads of clauses stay pure patterns. Neither adds a core rule:
 *
 *  - `match [H :] e with | p₁ => e₁ | …` against a goal `G` elaborates to a function lifted from the
 *    context ([[Lifting]]), as a `where`-local function is: `m : (y : A) -> {H : eq e y} -> G'` with the
 *    clauses `m pᵢ {H := H} = eᵢ`, applied as `m e {refl}`. `G'` is `G` with the occurrences of `e`
 *    abstracted ([[abstractOccurrences]]). Coverage, unreachable branches, termination and the editor's
 *    case split are those of the function's clauses ([[Clauses]]).
 *  - `rewrite h in e` with `h : eq a b` against `G` abstracts `a` in `G`, giving `P = [y] G'`, checks
 *    `e : P b` and elaborates to `subst P (sym h) e` of `std/eq`.
 *
 *  Abstraction is syntactic, on normal forms: the goal and the term are read back with definitions
 *  unfolded and functions by clauses applied as far as evaluation takes them (the normal form conversion
 *  uses), and every subterm of the goal equal to the term up to the names of bound variables is replaced
 *  (Agda's with-abstraction, `with-abstraction.lagda.rst`). Only the goal is abstracted, not the types of
 *  the context's variables. The abstracted goal is checked again ([[MotiveCheck]]): where an argument's
 *  type still mentions the term while its function now expects the new variable, the error says which
 *  term was abstracted, what the goal became and which argument no longer fits (E0927), instead of
 *  Agda's `w != e of type A when checking that the type … of the generated with function is
 *  well-formed`, or Lean's bare `motive is not type correct`. */
trait Matches:
  self: Elaborator =>
  import core.*

  /** The function or definition being elaborated: the function of a `match` is named after it. */
  private var owner: Name = ""

  /** Runs `f` with `n` as the name the functions of its `match`es are named after. */
  def withMatchOwner[A](n: Name)(f: => A): A =
    val saved = owner
    owner = n
    try f
    finally owner = saved

  // ---------------------------------------------------------------- the equality of std/eq

  /** The globals of `std/eq` that `match H :` and `rewrite` elaborate to. */
  private final case class EqualityLibrary(eq: Int, refl: Int, subst: Int, sym: Int)

  /** The equality of `std/eq`, if the program loads it (any of its files may: the module values of the
   *  files elaborated before are known); E0929 otherwise, at `span`. This is Agda's `BUILTIN EQUALITY`,
   *  bound by loading the library instead of by a pragma. */
  private def equalityLibrary(rewrite: Boolean, span: Span): EqualityLibrary =
    val path = hugin.compiler.SourceLoader.resolve(file.path, "std/eq")
    def global(fields: List[(Name, Tm)], n: Name): Option[Int] = fields.collectFirst { case (`n`, Tm.Global(id)) => id }
    val found = file.imports.get(path).map(_.value).collect { case Tm.Rec(fields) => fields }.flatMap { fs =>
      for
        eq <- global(fs, "eq")
        refl <- global(fs, "refl")
        subst <- global(fs, "subst")
        sym <- global(fs, "sym")
      yield EqualityLibrary(eq, refl, subst, sym)
    }
    found.getOrElse {
      val start = if span.exists then Span(span.origin, 0, 0) else Span.NoSpan
      fail(MatchProblem.NoEqualityLibrary(rewrite, span, start))
    }

  /** `eq {a} x y` of the library, as a term. */
  private def eqTm(lib: EqualityLibrary, a: Tm, x: Tm, y: Tm): Tm =
    Tm.apps(Tm.Global(lib.eq), List((a, Icit.Impl), (x, Icit.Expl), (y, Icit.Expl)))

  // ---------------------------------------------------------------- match

  /** A `match` without an expected type: a plain case expression, its type an unknown that the branches
   *  determine. */
  def inferMatch(c: Cxt, m: Match): (Tm, Val, Stage) =
    val a = ev(c, freshType(c, Stage.S1, m.kwSpan, "the type of the `match`"))
    (checkMatch(c, m, a), a, Stage.S1)

  /** `match [H :] e with | p₁ => e₁ | …` against `goal`. */
  def checkMatch(c: Cxt, m: Match, goal: Val): Tm =
    val (scrut, sty) = scrutinee(c, m.scrutinee)
    val lib = m.eqn.map(h => equalityLibrary(rewrite = false, h.span))
    val y = freshVariable(c)
    val motive = abstracted(c, goal, ev(c, scrut), sty, y, m.scrutinee.span, rewrite = false)
    val a = quote(c.lvl, sty)
    val ty = (m.eqn, lib) match
      case (Some(h), Some(l)) =>
        Tm.Pi(y, Icit.Expl, a, Tm.Pi(h.name, Icit.Impl, eqTm(l, Tm.shift(a, 1), Tm.shift(scrut, 1), Tm.Var(0)), Tm.shift(motive, 1)))
      case _ => Tm.Pi(y, Icit.Expl, a, motive)
    val name = if owner.isEmpty then "match" else s"$owner.match"
    val (id, _) = liftedFunction(c, name, ty, m.kwSpan, matchFunction = true)
    val clauses = m.branches.map { b =>
      val equation = m.eqn.toList.map(h => NamedArg(h.name, h)(h.span, h.span))
      SurfaceClause(Ident(name)(m.kwSpan), equation :+ b.pat, b.rhs, b.span)
    }
    elabFunction(id, padded(c, clauses), prelude(c), Some(m.kwSpan))
    val bound = c.binders.reverse.zipWithIndex.collect { case (b, l) if b.defn.isEmpty => (Tm.Var(c.lvl - l - 1), Icit.Expl) }
    val applied = Tm.apps(Tm.Global(id), bound :+ (scrut, Icit.Expl))
    (m.eqn, lib) match
      case (Some(_), Some(l)) => Tm.App(applied, Tm.apps(Tm.Global(l.refl), List((a, Icit.Impl), (scrut, Icit.Impl))), Icit.Impl)
      case _ => applied

  /** The scrutinee with its implicit arguments inserted, and its type. */
  private def scrutinee(c: Cxt, t: Tree): (Tm, Val) =
    val (tm, ty) = inferS(c, t, Stage.S1)
    val (tm2, ty2, _) = insert(c, t.span, (tm, ty, Stage.S1))
    (tm2, ty2)

  /** A name for the abstracted variable that the context does not use. */
  private def freshVariable(c: Cxt): Name = FreshNames(c.names)("y")

  /** `goal` with the occurrences of `term` (of type `tpe`) abstracted as `y`: a term in `c` extended by
   *  `y`. Without occurrences, the goal as written (folded), which does not mention `y`. E0927 if the
   *  abstracted goal is ill-typed. */
  private def abstracted(c: Cxt, goal: Val, term: Val, tpe: Val, y: Name, at: Span, rewrite: Boolean): Tm =
    val g = quote(c.lvl, goal)
    val t = quote(c.lvl, term)
    val (motive, count) = abstractOccurrences(g, t)
    if count == 0 then Tm.shift(quoteFolded(c.lvl, goal), 1)
    else
      MotiveCheck(c, tpe, t, y).run(motive).foreach { arg =>
        fail(MatchProblem.IllTypedAbstraction(
          rewrite,
          showPlain(c.names, t),
          showPlain(c.names, g),
          y,
          showPlain(y :: c.names, motive),
          arg,
          at
        ))
      }
      motive

  /** `goal` (a normal form in a context of some level) with every subterm equal to `term` up to the
   *  names of bound variables replaced by a variable bound after the context: a term in the context
   *  extended by it, and the number of occurrences replaced. An offset `b + k` contains `b + j` for
   *  `j < k` (it is the successor applied `k` times); numerals are atoms (as Agda's literals are). */
  private def abstractOccurrences(goal: Tm, term: Tm): (Tm, Int) =
    var count = 0
    val shifted = mutable.HashMap.empty[Int, Tm]
    def termAt(d: Int) = shifted.getOrElseUpdate(d, Tm.shift(term, d))
    def go(t: Tm, d: Int): Tm =
      if sameTerm(t, termAt(d)) then
        count += 1
        Tm.Var(d)
      else
        (t, termAt(d)) match
          case (Tm.NatAdd(fam, b, k), Tm.NatAdd(fam2, b2, j)) if fam == fam2 && j < k && sameTerm(b, b2) =>
            count += 1
            Tm.NatAdd(fam, Tm.Var(d), k - j)
          case _ =>
            t match
              case Tm.Var(ix) => if ix >= d then Tm.Var(ix + 1) else t
              case Tm.Lam(x, i, b) => Tm.Lam(x, i, go(b, d + 1))
              case Tm.Pi(x, i, a, b) => Tm.Pi(x, i, go(a, d), go(b, d + 1))
              case Tm.Let(x, a, v, b) => Tm.Let(x, go(a, d), go(v, d), go(b, d + 1))
              case Tm.RecTy(fs, rs, ds) => Tm.RecTy(fs.zipWithIndex.map((f, j) => (f._1, go(f._2, d + j))), rs, ds)
              case Tm.Fresh(ns, b) => Tm.Fresh(ns, go(b, d + ns.length))
              case Tm.AppPruning(f, pr) => Tm.AppPruning(f, pr.take(d) ++ List(None) ++ pr.drop(d))
              case other => Tm.mapChildren(other)(go(_, d))
    val out = go(goal, 0)
    (out, count)

  /** Whether two terms are equal up to the names of bound variables and source positions. */
  private def sameTerm(a: Tm, b: Tm): Boolean =
    (a eq b) || ((Tm.unloc(a), Tm.unloc(b)) match
      case (Tm.App(f, x, i), Tm.App(g, y, j)) => i == j && sameTerm(x, y) && sameTerm(f, g)
      case (Tm.Lam(_, i, x), Tm.Lam(_, j, y)) => i == j && sameTerm(x, y)
      case (Tm.Pi(_, i, a1, b1), Tm.Pi(_, j, a2, b2)) => i == j && sameTerm(a1, a2) && sameTerm(b1, b2)
      case (Tm.Let(_, a1, d1, b1), Tm.Let(_, a2, d2, b2)) => sameTerm(a1, a2) && sameTerm(d1, d2) && sameTerm(b1, b2)
      case (Tm.RecTy(fs, _, _), Tm.RecTy(gs, _, _)) =>
        fs.map(_._1) == gs.map(_._1) && fs.zip(gs).forall((f, g) => sameTerm(f._2, g._2))
      case (x, y) if x.getClass eq y.getClass =>
        val (xs, ys) = (Tm.children(x), Tm.children(y))
        xs.length == ys.length && Tm.mapChildren(x)(_ => Tm.U0) == Tm.mapChildren(y)(_ => Tm.U0) &&
        xs.zip(ys).forall(sameTerm)
      case _ => false
    )

  // ---------------------------------------------------------------- rewrite

  /** `rewrite h in e` against `goal`: `subst P (sym h) e` with `P = [y] G'`, the goal with the left side
   *  of `h`'s equation abstracted. */
  def checkRewrite(c: Cxt, r: Rewrite, goal: Val): Tm =
    force(goal) match
      case Val.Flex(_, _) => fail(MatchProblem.RewriteWithoutGoal(r.kwSpan))
      case _ =>
    val lib = equalityLibrary(rewrite = true, r.kwSpan)
    val (h, hty) = scrutinee(c, r.eqn)
    val (a, lhs, rhs) = force(hty) match
      case Val.Rigid(Head.Glob(e), sp) if e == lib.eq && sp.length == 3 =>
        sp.reverse.collect { case Elim.EApp(v, _) => v } match
          case List(a, x, y) => (a, x, y)
          case _ => fail(MatchProblem.NotAnEquation(show(c, hty), r.eqn.span))
      case _ => fail(MatchProblem.NotAnEquation(show(c, hty), r.eqn.span))
    val y = freshVariable(c)
    val g = quote(c.lvl, goal)
    val (_, count) = abstractOccurrences(g, quote(c.lvl, lhs))
    if count == 0 then fail(MatchProblem.NoOccurrence(show(c, lhs), showPlain(c.names, g), r.eqn.span))
    val motive = abstracted(c, goal, lhs, a, y, r.eqn.span, rewrite = true)
    val p = Tm.Lam(y, Icit.Expl, motive)
    val body = check(c, r.body, eval(rhs :: c.env, motive), Stage.S1)
    val (aTm, lTm, rTm) = (quoteFolded(c.lvl, a), quoteFolded(c.lvl, lhs), quoteFolded(c.lvl, rhs))
    rewriteLevels(c, lib, a, lhs, rhs, motive, r.kwSpan)
    val symmetric = Tm.apps(Tm.Global(lib.sym), List((aTm, Icit.Impl), (lTm, Icit.Impl), (rTm, Icit.Impl), (h, Icit.Expl)))
    Tm.apps(
      Tm.Global(lib.subst),
      List((aTm, Icit.Impl), (rTm, Icit.Impl), (lTm, Icit.Impl), (p, Icit.Expl), (symmetric, Icit.Expl), (body, Icit.Expl))
    )

  /** The universe constraints of `subst {a} {rhs} {lhs} P (sym {a} {lhs} {rhs} h) e`: `a` must fit the
   *  universes of `subst`'s and `sym`'s `A`, and the motive's body that of `subst`'s `P`. Levels are
   *  global (reference: meta/universes), so the use raises them as an application written by hand would;
   *  E0904 if it cannot. */
  private def rewriteLevels(c: Cxt, lib: EqualityLibrary, a: Val, lhs: Val, rhs: Val, motive: Tm, span: Span): Unit =
    val types = c.binders.reverse.map(_.ty).toVector
    def binderUniverse(ty: Val): Option[Level] = force(ty) match
      case Val.Pi(_, _, dom, _) =>
        force(dom) match
          case Val.U1(l) => Some(l)
          case _ => None
      case _ => None
    def fits(lower: List[Level], l: Option[Level], shown: String): Unit = l.foreach { k =>
      if !lower.forall(levels.le(_, k)) then fail(TypeProblem.UniverseInconsistency(showLevel(k), shown, span))
    }
    val aLevels = typeLevels(types, c.lvl, a)
    fits(aLevels, binderUniverse(globals(lib.sym).ty), show(c, a))
    val substTy = globals(lib.subst).ty
    fits(aLevels, binderUniverse(substTy), show(c, a))
    // `P : A -> Type`, after `{A}`, `{x}` and `{y}`
    val afterImplicits = List(a, rhs, lhs).foldLeft(substTy) { (t, v) =>
      force(t) match
        case Val.Pi(_, _, _, cl) => inst(cl, v)
        case other => other
    }
    val pUniverse = force(afterImplicits) match
      case Val.Pi(_, _, pDom, _) =>
        force(pDom) match
          case Val.Pi(_, _, _, cl) =>
            force(inst(cl, Val.local(c.lvl))) match
              case Val.U1(l) => Some(l)
              case _ => None
          case _ => None
      case _ => None
    fits(typeLevels(types :+ a, c.lvl + 1, eval(Val.local(c.lvl) :: c.env, motive)), pUniverse, showPlain(c.names, quote(c.lvl, a)))

  // ---------------------------------------------------------------- checking an abstracted goal

  /** A check of an abstracted goal `motive`, a normal form in `c` extended by a variable of type `tpe`
   *  (for `term`): the arguments of its applications must have the types their functions expect. Types
   *  that cannot be inferred (lambdas without an expected type, object code) are not checked, nor are
   *  universes (abstraction does not change levels). It reports the first argument that does not fit. */
  private final class MotiveCheck(c: Cxt, tpe: Val, term: Tm, y: Name):
    private final class Found(val arg: IllTypedArgument) extends Exception(null, null, false, false)

    def run(motive: Tm): Option[IllTypedArgument] =
      val types = c.binders.reverse.map(b => Option(b.ty)).toVector :+ Some(tpe)
      try
        infer(motive, Val.local(c.lvl) :: c.env, types, y :: c.names)
        None
      catch case f: Found => Some(f.arg)

    private def infer(t: Tm, env: List[Val], types: Vector[Option[Val]], names: List[Name]): Option[Val] =
      val lvl = types.length
      def under(x: Name, ty: Option[Val], body: Tm, value: Val = Val.local(lvl)) = infer(body, value :: env, types :+ ty, x :: names)
      t match
        case Tm.Var(ix) => types.lift(lvl - ix - 1).flatten
        case Tm.Global(id) => Some(globals(id).ty)
        case Tm.Meta(m) => Some(metas(m).ty)
        case Tm.App(f, a, _) =>
          infer(f, env, types, names).map(force) match
            case Some(Val.Pi(_, _, dom, cl)) =>
              checkArg(t, a, dom, env, types, names)
              Some(inst(cl, eval(env, a)))
            case _ =>
              infer(a, env, types, names)
              None
        case Tm.Pi(x, _, a, b) =>
          infer(a, env, types, names)
          under(x, Some(eval(env, a)), b)
          None
        case Tm.Lam(x, _, b) =>
          under(x, None, b)
          None
        case Tm.Let(x, a, d, b) =>
          val av = eval(env, a)
          checkTerm(t, d, av, env, types, names)
          under(x, Some(av), b, eval(env, d))
        case Tm.Lit(l, Stage.S1) => Some(Val.Base(BaseType.of(l), Stage.S1))
        case Tm.Proj(r, l) =>
          infer(r, env, types, names).map(force) match
            case Some(rt: Val.RecTy) => fieldType(rt, eval(env, r), l)
            case _ => None
        case Tm.Rec(fs) =>
          fs.foreach(f => infer(f._2, env, types, names))
          None
        case Tm.NatAdd(_, b, _) =>
          infer(b, env, types, names)
          None
        case _ => None

    /** The argument `a` of the application `app` against the domain `dom` of its function. */
    private def checkArg(app: Tm, a: Tm, dom: Val, env: List[Val], types: Vector[Option[Val]], names: List[Name]): Unit =
      checkTerm(app, a, dom, env, types, names)

    private def checkTerm(app: Tm, a: Tm, expected: Val, env: List[Val], types: Vector[Option[Val]], names: List[Name]): Unit =
      val lvl = types.length
      (a, force(expected)) match
        case (_, Val.U1(_)) => infer(a, env, types, names)
        case (Tm.Lam(x, _, b), Val.Pi(_, _, dom, cl)) =>
          checkTerm(b, b, inst(cl, Val.local(lvl)), Val.local(lvl) :: env, types :+ Some(dom), x :: names)
        case _ =>
          infer(a, env, types, names).foreach { found =>
            force(found) match
              case Val.U1(_) =>
              case _ =>
                if !tentatively(conv(lvl, found, expected)) then
                  // the term, from `c`, under the abstracted variable and the binders of the goal after it
                  val here = Tm.shift(term, lvl - c.lvl)
                  val mentions = Tm.exists(quote(lvl, found))(sameTerm(_, here))
                  throw Found(
                    IllTypedArgument(
                      showPlain(names, app),
                      showPlain(names, a),
                      showPlain(names, quoteFolded(lvl, found)),
                      showPlain(names, quoteFolded(lvl, expected)),
                      mentions
                    )
                  )
          }
