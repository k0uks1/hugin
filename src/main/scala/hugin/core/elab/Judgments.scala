package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

import scala.collection.mutable

/** The judgment notation and rule names (reference: std/semantics, "The judgment notation", "Rule names";
 *  #186 P7b). Both are notation for `std/semantics`'s family `derives`; neither adds a rule to the core.
 *
 *  - `P ⊢[e] r t₁ … tₙ` is `derives (programOf P) e (atom ρ [v t₁, …, v tₙ])`: `r` is resolved in the scope
 *    of `P`'s body as `programOf` reads its rules (its own relations `own i`, its parameters' relations
 *    `arg l`, the file's relations `ext s`), and each `tᵢ` is checked as code of `r`'s column type.
 *  - The program names its functor's arguments: a functor written alone is an error (E0946); in the type
 *    of a declaration, `tc G ⊢ …` binds `G` as any free uppercase variable (#186 P7c).
 *  - A judgment without `[e]` in the type of a declaration (and its parameters' types) is at the
 *    declaration's one anonymous database, its first implicit binder, shared by all such judgments of the
 *    declaration; elsewhere its database is an unknown that unification must determine (E0947). No
 *    identifier is generalised that the user did not write (Agda's `variable` and Lean's auto-bound
 *    implicits bind written names only; one database per statement is Abella's ambient specification).
 *  - A rule name `r.k` (or a rule's label) is a pattern synonym for `fire` at the `k`-th rule of `r`, with
 *    the rule's variables, its premises in body order and its first head: as a pattern on a derivation, and
 *    as an expression that builds one. `given I` is `given t I` with `t` the proof that the relation is an
 *    input (Agda's pattern synonyms, Isabelle's `tc.intros(k)`, Abella's `case` on `{P |- A}`). */
object Judgments:
  /** What the unknown database of a judgment without `[e]` outside a declaration's type is called; unsolved,
   *  it is E0947 ([[Items.checkSolved]]). */
  val UnknownDatabase = "the database of a judgment"

trait Judgments:
  self: Elaborator =>
  import core.*

  // ---------------------------------------------------------------- the judgment

  /** `P ⊢[e] r t̄`. */
  def inferJudgment(c: Cxt, j: Judgment): (Tm, Val, Stage) = inferJudgmentOf(c, j, None)

  /** `P ⊢[e] r t̄`, with the program already resolved if `resolved` is given (a coerced atom of an opened
   *  instance relation, #186 P9b: `j.program` then only shows it). */
  def inferJudgmentOf(c: Cxt, j: Judgment, resolved: Option[(Tm, ProgramScope)]): (Tm, Val, Stage) =
    val sem = semanticsGlobals.getOrElse(fail(JudgmentProblem.NoLibrary(j.opSpan)))
    val programTy = eval(Nil, Tm.Global(sem("program")))
    // the program: a functor applied, a module or a program value; a functor alone names no arguments
    val (prog, scope) = resolved match
      case Some((p, sc)) => (p, Some(sc))
      case None =>
        rejectFunctorAlone(j)
        if programValued(c, j.program, programTy) then (check(c, j.program, programTy, Stage.S1), None)
        else judgmentProgram(c, j.program, j.opSpan)
    val programShown = hugin.syntax.Printer.show(j.program)
    // a program with a negation or an aggregate is read stratum by stratum, in `std/strata` (#186 P9c);
    // without the library, E0961 (#186 P9a)
    val stratified = nonPositiveRule(sem, ev(c, prog)).map { (rel, aggregate) =>
      strataGlobals.getOrElse(fail(JudgmentProblem.NotPositive(programShown, rel, aggregate, j.program.span)))
    }
    // the database
    val dbTy = eval(Nil, Tm.Global(sem("db")))
    val db = j.db match
      case Some(e) => check(c, e, dbTy, Stage.S1)
      case None =>
        anonymousDatabase(c, j.opSpan) match
          case Some(level) => quote(c.lvl, Val.local(level))
          case None => freshMeta(c, dbTy, Stage.S1, j.opSpan, Judgments.UnknownDatabase)
    // the atom: its relation in the program's scope, its arguments as code of the relation's column types
    val (head, args) = TreeOps.flattenApp(j.atom)
    val path = namePath(head).getOrElse(fail(JudgmentProblem.NotAnAtom(hugin.syntax.Printer.show(j.atom), j.atom.span)))
    val relShown = path.mkString(".")
    val (ref, relTy) =
      relationRef(c, sem, prog, scope, path).getOrElse(fail(JudgmentProblem.UnknownRelation(relShown, programShown, head.span)))
    // a relation of the file that is the value of an argument written out names that argument, which the
    // program reads as its parameter's relation `arg l`, not as `ext s`: an error, not another meaning
    ref match
      case Tm.App(Tm.Global(e), _, _) if e == sem("ext") && path.length == 1 =>
        argumentRelation(c, j.program, path.head).foreach { (functor, param, label) =>
          fail(JudgmentProblem.ArgumentRelation(relShown, functor, param, label, head.span))
        }
      case _ =>
    val columns = relTy.map(t => objectColumns(t).map(_._2))
    columns.foreach { cs =>
      if cs.length != args.length then fail(JudgmentProblem.AtomArity(relShown, cs.length, args.length, j.atom.span))
    }
    val valueTy = Tm.Global(sem("value"))
    val values = args.zipWithIndex.map { (a, i) =>
      val (code, ty) = columns match
        case Some(cs) => (check(c, a, Val.Lift(cs(i)), Stage.S1), cs(i))
        case None =>
          val (tm, ty) = inferS(c, a, Stage.S1)
          force(ty) match
            case Val.Lift(t) => (tm, t)
            case _ => fail(JudgmentProblem.UntypedArgument(relShown, a.span))
      Tm.apps(Tm.Global(sem("v")), List((Tm.quote(quote(c.lvl, ty)), Icit.Impl), (code, Icit.Expl)))
    }
    val r = reflective(j.span)
    val list = values.foldRight(Tm.App(Tm.Global(r.nil), valueTy, Icit.Impl): Tm)((x, acc) =>
      Tm.apps(Tm.Global(r.cons), List((valueTy, Icit.Impl), (x, Icit.Expl), (acc, Icit.Expl)))
    )
    val atomTm = Tm.apps(Tm.Global(sem("atom")), List((ref, Icit.Expl), (list, Icit.Expl)))
    val (family, programArg, dbArg) = stratified match
      case None => (sem("derives"), prog, db)
      case Some(st) =>
        // `nderives (layer p sₖ) (upTo p k d) a`, `k` the stratum of the relation's judgment
        val data = programData(ev(c, prog))
        val k = data.fold(0)(_.stratumOf(rrefKey(sem, ev(c, ref))))
        val nat = natOf(sem)
        val natTy = Tm.Global(nat)
        val sk = data.flatMap(_.strata.lift(k)).getOrElse(Nil).foldRight(Tm.App(Tm.Global(r.nil), natTy, Icit.Impl): Tm)((i, acc) =>
          Tm.apps(Tm.Global(r.cons), List((natTy, Icit.Impl), (Tm.Nat(nat, BigInt(i)), Icit.Expl), (acc, Icit.Expl)))
        )
        val layerTm = Tm.apps(Tm.Global(st("layer")), List((prog, Icit.Expl), (sk, Icit.Expl)))
        val upToTm = Tm.apps(Tm.Global(st("upTo")), List((prog, Icit.Expl), (Tm.Nat(nat, BigInt(k)), Icit.Expl), (db, Icit.Expl)))
        (st("nderives"), layerTm, upToTm)
    val tm = Tm.apps(Tm.Global(family), List((programArg, Icit.Expl), (dbArg, Icit.Expl), (atomTm, Icit.Expl)))
    var ty = globals(family).ty
    for a <- List(programArg, dbArg, atomTm) do
      force(ty) match
        case Val.Pi(_, _, _, cl) => ty = inst(cl, ev(c, a))
        case _ => throw Impossible("a judgment over three arguments")
    (tm, ty, Stage.S1)

  /** The globals of `std/strata`, if it is loaded: the stratified reading of the notation (#186 P9c). */
  def strataGlobals: Option[Map[Name, Int]] =
    if strataCache == null then strataCache = Some(libraryModule("std/strata")).filter(_.contains("upTo"))
    strataCache.nn

  private var strataCache: Option[Map[Name, Int]] | Null = null

  /** If the program is a functor applied to arguments and the relation `rel` of the file (by its resolved
   *  constant, compared syntactically, without evaluation) is the value of an argument that is not a
   *  variable, or of a field of a record literal written as one: the functor, the parameter and the
   *  field (#186 P7c). */
  private def argumentRelation(c: Cxt, program: Tree, rel: Name): Option[(String, Name, Option[Name])] =
    def constant(t: Tree): Option[Int] = t match
      case Parens(i) => constant(i)
      case Ident(n) if !c.scope.contains(n) => lookupGlobal(n).map(sharedAt(_, Stage.S0))
      case _ => None
    val target = constant(Ident(rel)(Span.NoSpan))
    val (head, written) = TreeOps.flattenApp(program)
    def unwrap(t: Tree): Tree = t match
      case Parens(i) => unwrap(i)
      case other => other
    (head, target) match
      case (Ident(f), Some(id)) if !c.scope.contains(f) && lookupGlobal(f).isDefined =>
        val params = telescope(globals(lookupGlobal(f).get).ty)._1.filter(_._2 == Icit.Expl).map(_._1)
        written.filterNot(_.isInstanceOf[NamedArg]).zipWithIndex.iterator.flatMap { (a, i) =>
          val param = params.lift(i).getOrElse("_")
          unwrap(a) match
            case VarRef(n) if c.scope.contains(n) => None
            case Ident(n) if c.scope.contains(n) => None
            case r: RecordLit => r.fields.find(fl => constant(fl.value).contains(id)).map(fl => (f, param, Some(fl.label.name)))
            case other => Option.when(constant(other).contains(id))((f, param, None))
        }.nextOption()
      case _ => None

  /** `a.b.c` as a path of names. */
  private def namePath(t: Tree): Option[List[Name]] = t match
    case Ident(n) => Some(List(n))
    case VarRef(n) => Some(List(n))
    case Select(q, n) if n.headOption.exists(_.isLetter) => namePath(q).map(_ :+ n)
    case Parens(i) => namePath(i)
    case _ => None

  /** A functor written alone as the program of a judgment, with its parameters' names: a global meta
   *  constant of a Π type with explicit binders (written as a name, not applied). */
  def functorAlone(p: Tree): Option[(String, List[Name])] = p match
    case Parens(i) => functorAlone(i)
    case Ident(n) if lookupGlobal(n).isDefined => functorParams(lookupGlobal(n).get).map(ps => (n, ps))
    case _ => None

  /** E0946 for a judgment whose program is a functor written alone; the help applies it to variables named
   *  after its parameters, `tc G`. */
  private def rejectFunctorAlone(j: Judgment): Unit =
    functorAlone(j.program).foreach { (name, params) =>
      val applied = (name :: params.map(x => if x.headOption.exists(_.isLetter) then x.capitalize else "X")).mkString(" ")
      fail(JudgmentProblem.FunctorAlone(name, applied, j.program.span))
    }

  private def functorParams(id: Int): Option[List[Name]] =
    if globals(id).stage != Stage.S1 then None
    else
      val explicit = telescope(globals(id).ty)._1.takeWhile(_._2 == Icit.Expl).map(_._1)
      Option.when(explicit.nonEmpty && telescope(globals(id).ty)._1.forall(_._2 == Icit.Expl))(explicit)

  /** The level of the anonymous database of the declaration whose type has the judgment with the turnstile
   *  at `at` and without `[e]`, if `c` binds it. */
  private def anonymousDatabase(c: Cxt, at: Span): Option[Int] =
    c.binders.zipWithIndex.collectFirst {
      case (b, k) if (b.origin match
            case BinderOrigin.Database(js) => js.contains(at)
            case _ => false
          ) => c.lvl - k - 1
    }

  /** Whether the program of a judgment is a value of type `program` (a variable or a constant of that type,
   *  possibly applied), rather than a module body for `programOf`. Decided from the head's declared type, so
   *  that a functor application is not evaluated (which would create an instance). */
  private def programValued(c: Cxt, p: Tree, programTy: Val): Boolean =
    val (head, args) = TreeOps.flattenApp(p)
    val headTy = head match
      case Ident(n) if c.scope.contains(n) => Some(c.binder(c.scope(n)).ty)
      case Ident(n) => lookupGlobal(n).filter(globals(_).stage == Stage.S1).map(globals(_).ty)
      case _ => None
    headTy.exists { ty =>
      var t = ty
      var k = args.count(!_.isInstanceOf[NamedArg])
      var ok = true
      while ok && k > 0 do
        force(t) match
          case Val.Pi(_, Icit.Expl, _, cl) =>
            t = inst(cl, Val.Wild)
            k -= 1
          case Val.Pi(_, Icit.Impl, _, cl) => t = inst(cl, Val.Wild)
          case _ => ok = false
      ok && (t match
        case Val.Top(id, Nil, _) => Tm.Global(id) == Tm.Global(programTyId(programTy))
        case _ => false
      )
    }

  private def programTyId(programTy: Val): Int = programTy match
    case Val.Top(id, _, _) => id
    case _ => -1

  /** The reference of the relation at `path` and its type (in `c`), in the scope of the program. */
  private def relationRef(c: Cxt, sem: Map[Name, Int], prog: Tm, scope: Option[ProgramScope], path: List[Name]): Option[(Tm, Option[Val])] =
    def own(i: Int) = Tm.App(Tm.Global(sem("own")), Tm.Nat(natOf(sem), BigInt(i)), Icit.Expl)
    def arg(l: String) = Tm.App(Tm.Global(sem("arg")), Tm.Lit(hugin.syntax.Literal.StrL(l), Stage.S1), Icit.Expl)
    def global: Option[(Tm, Option[Val])] = path match
      case List(n) if !c.scope.contains(n) =>
        lookupGlobal(n).map(sharedAt(_, Stage.S0)).filter(id => globals(id).stage == Stage.S0 && isRelationLike(id)).map { id =>
          state.used += id
          recordUse(Span.NoSpan, id)
          (Tm.App(Tm.Global(sem("ext")), Tm.Quote(Tm.Global(id)), Icit.Expl), Some(globals(id).ty))
        }
      case _ => None
    scope match
      case Some(sc) =>
        path match
          case List(n) if sc.own.contains(n) => Some((own(sc.own(n)._1), sc.own(n)._2))
          case _ =>
            sc.param(path) match
              case Some((label, ty)) => Some((arg(label), ty))
              case None => global
      case None =>
        // a program value: its own relations by the names it lists
        val relations = programData(ev(c, prog)).map(_.relations).getOrElse(Nil)
        path match
          case List(n) if relations.contains(n) => Some((own(relations.indexOf(n)), None))
          case _ => global

  private def isRelationLike(id: Int): Boolean = globals(id).kind match
    case GlobalKind.Object(ObjDecl.Relation | ObjDecl.Struct | ObjDecl.Constructor) => true
    case _ => false

  private def natOf(sem: Map[Name, Int]): Int =
    telescope(globals(sem("own")).ty)._1.collectFirst { case (_, Icit.Expl, d) => d }.map(forceData) match
      case Some(Val.Rigid(Head.Glob(id), Nil)) => id
      case other => throw Impossible(s"own over $other")

  // ---------------------------------------------------------------- generalisation

  /** The generalised binder of a declaration's type `trees` (its type and its parameters' types), bound in
   *  `c`: the anonymous database, if a judgment has no `[e]`. It has no source name, so it cannot be
   *  referred to or matched by `{x := p}`; the judgments without `[e]` of `trees`, and only they, are at it. */
  def generalisedBinders(trees: List[Tree], c: Cxt): (Cxt, List[(Name, Tm)]) =
    // the judgments without `[e]`, and the atoms coerced to judgments (#186 P9b), which have none
    val omitted = (trees.flatMap(t => TreeOps.nodes(t).collect { case j: Judgment if j.db.isEmpty => j.opSpan }) ++
      coercionCandidates(trees, c).map(_._2)).toSet
    semanticsGlobals.filter(_ => omitted.nonEmpty) match
      case Some(sem) =>
        val dbTm = Tm.Global(sem("db"))
        val x = Printing.AnonymousDatabase
        (bind(c, x, eval(Nil, dbTm), Stage.S1, BinderOrigin.Database(omitted)), List((x, dbTm)))
      case None => (c, Nil)

  /** The types of the free uppercase variables `generalised` of a declaration's type `trees` (bound in `c`)
   *  that are a functor's arguments in a judgment, `tc G ⊢ …`, or its database, `⊢[D]`: unified with the
   *  types of the functor's parameters and with `db`, before the type is elaborated, so that a binder
   *  before the judgment may use them (`{x y : G.node} -> tc G ⊢ path x y`). A disagreement is left to the
   *  elaboration of the judgment, which reports it. */
  def judgmentArgumentTypes(trees: List[Tree], c: Cxt, generalised: Set[Name]): Unit =
    def agree(n: Name, ty: Val): Unit =
      if generalised(n) && c.scope.contains(n) then
        try undoOnFailure(unify(c.lvl, c.binder(c.scope(n)).ty, ty))
        catch case _: UnifyError => ()
    def functorArguments(program: Tree): Unit =
      val (head, args) = TreeOps.flattenApp(program)
      head match
        case Ident(f) if !c.scope.contains(f) =>
          lookupGlobal(f).filter(globals(_).stage == Stage.S1).foreach { id =>
            var ty = globals(id).ty
            var rest = args
            while rest.nonEmpty do
              (rest.head, force(ty)) match
                case (VarRef(n), Val.Pi(_, Icit.Expl, dom, cl)) if c.scope.contains(n) =>
                  agree(n, dom)
                  ty = inst(cl, Val.local(c.scope(n)))
                  rest = rest.tail
                case _ => rest = Nil
          }
        case _ =>
    for j <- trees.flatMap(t => TreeOps.nodes(t).collect { case j: Judgment => j }) do
      // before the binders that would need the argument's type (`{x : G.node} -> tc ⊢ …`)
      rejectFunctorAlone(j)
      functorArguments(j.program)
      j.db match
        case Some(VarRef(n)) => semanticsGlobals.foreach(sem => agree(n, eval(Nil, Tm.Global(sem("db")))))
        case _ =>
    // the programs of the coerced atoms, `(tc G).path x y` (#186 P9b)
    for case (Some(program), _) <- coercionCandidates(trees, c) do functorArguments(program)

  // ---------------------------------------------------------------- program data

  /** A rule of a program, as rule names need it: its position in the program's rules, its head relation
   *  and index among that relation's rules (`crule.head`, `crule.index`: by its first head), its label, its
   *  variables' number and names, which of its body literals are atoms (premises) rather than comparisons,
   *  the relation of each of its head atoms (`crule.heads`, nested facts included) and of each premise
   *  (`None` for a relation of a parameter). */
  final case class RuleData(
      position: Int,
      head: Int,
      index: Int,
      label: Option[String],
      vars: Int,
      names: List[Name],
      body: List[Boolean],
      headRels: List[Option[RelKey]],
      premiseRels: List[Option[RelKey]] = Nil,
      lits: List[BodyLit] = Nil
  ):
    def heads: Int = headRels.length

  /** A literal of a rule's body, as a stratum-local rule name reads it (#186 P9c): an atom, a comparison, a
   *  negated atom (of the relation `rel`, with local variables or not) or an aggregate. */
  enum BodyLit:
    case Pos, Cmp, Agg
    case Neg(rel: Option[RelKey], locals: Boolean)

    /** Whether the literal is a written premise of a stratum-local rule name (all but comparisons). */
    def written: Boolean = this != BodyLit.Cmp

  /** A relation of a rule's atom: `Left(i)` for `own i`, `Right(s)` for `ext` of the file's constant `s` (the
   *  constructor of a nested fact, say), as [[goalRelation]] gives a goal's. */
  type RelKey = Either[Int, String]

  /** A (rule, head) pair that a rule name names: the head at position `j` of `rule`'s head atoms, of the
   *  relation `rel`, the `k`-th such pair of `rel` in program and head order (`rel.k`, #186 P9d). */
  final case class HeadName(rule: RuleData, j: Int, rel: RelKey, k: Int)

  /** `arguments`: the values of the program's environment variables (its functor's arguments), if known. */
  final case class ProgramData(
      relations: List[String],
      rules: List[RuleData],
      display: Option[ProgramDisplay],
      context: List[Name],
      arguments: List[Val] = Nil,
      strata: List[List[Int]] = Nil
  ):
    /** The names of the program's (rule, head) pairs, numbered per head relation (reference: std/semantics,
     *  "Rule names"). `crule.index` keeps numbering rules by their first head; rule names need not agree. */
    lazy val headNames: List[HeadName] =
      val seen = mutable.Map.empty[RelKey, Int].withDefaultValue(0)
      for
        r <- rules
        (rel, j) <- r.headRels.zipWithIndex
        i <- rel
      yield
        seen(i) += 1
        HeadName(r, j, i, seen(i))

    /** The heads of `rule` of the relation `rel`. */
    def headsOf(rule: RuleData, rel: RelKey): List[HeadName] = headNames.filter(h => h.rule.position == rule.position && h.rel == rel)

    /** The strata (by index) whose layer has `rule`: those with one of its own heads (std/strata's `layer`). */
    def layersOf(rule: RuleData): List[Int] =
      strata.indices.toList.filter(i => rule.headRels.exists { case Some(Left(x)) => strata(i).contains(x); case _ => false })

    /** The stratum of a relation's stratum-local judgment (#186 P9c): the last stratum with a rule that has a
     *  head of it, 0 for a relation without rules (an input, of a parameter or of the file). */
    def stratumOf(rel: Option[RelKey]): Int =
      rel.fold(0)(k => headNames.filter(_.rel == k).flatMap(h => layersOf(h.rule)).maxOption.getOrElse(0))

    /** The rules of the layer of the stratum `j`, in program order (`filter (headIn s) p.rules`). */
    def layerRules(j: Int): List[RuleData] = rules.filter(layersOf(_).contains(j))

  /** The rules of a program value, if they evaluate (a program of a module body, possibly in parameters). */
  def programData(p: Val): Option[ProgramData] =
    semanticsGlobals.flatMap { sem =>
      val display = p match
        case Val.Top(id, _, _) if globals(id).program != null => Some(globals(id).program.nn)
        case _ => None
      try
        forceData(p) match
          case rec: Val.Rec =>
            val relations =
              listElems(proj(rec, "relations")).map(_.map(forceData).collect { case Val.Lit(hugin.syntax.Literal.StrL(s), _) => s })
            val rules = listElems(proj(rec, "rules")).map(_.zipWithIndex.flatMap { (r, pos) =>
              forceData(r) match
                case rr: Val.Rec =>
                  for
                    head <- natValue(proj(rr, "head"))
                    index <- natValue(proj(rr, "index"))
                    vars <- listElems(proj(rr, "vars"))
                    body <- listElems(proj(rr, "body"))
                    heads <- listElems(proj(rr, "heads"))
                  yield
                    val label = forceData(proj(rr, "label")) match
                      case Val.Rigid(Head.Glob(_), sp) =>
                        sp.collect { case Elim.EApp(a, Icit.Expl) => forceData(a) }.collectFirst {
                          case Val.Lit(hugin.syntax.Literal.StrL(s), _) => s
                        }
                      case _ => None
                    val isPos = body.map(b =>
                      forceData(b) match
                        case Val.Rigid(Head.Glob(id), _) => id == sem("cpos")
                        case _ => true
                    )
                    val names = display.flatMap(_.varNames.lift(pos)).filter(_.length == vars.length).getOrElse(Nil)
                    val premiseRels = body.flatMap(b =>
                      forceData(b) match
                        case Val.Rigid(Head.Glob(id), bsp) if id == sem("cpos") =>
                          List(bsp.reverse.collectFirst { case Elim.EApp(a, Icit.Expl) => a }.flatMap(relOf(sem, _)))
                        case _ => Nil
                    )
                    val lits = body.map(b =>
                      forceData(b) match
                        case Val.Rigid(Head.Glob(id), _) if id == sem("cpos") => BodyLit.Pos
                        case Val.Rigid(Head.Glob(id), bsp) if sem.get("cnot").contains(id) =>
                          val ex = bsp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }
                          BodyLit.Neg(ex.lift(1).flatMap(relOf(sem, _)), ex.headOption.flatMap(listElems).forall(_.nonEmpty))
                        case Val.Rigid(Head.Glob(id), _) if sem.get("cagg").contains(id) => BodyLit.Agg
                        case _ => BodyLit.Cmp
                    )
                    RuleData(pos, head.toInt, index.toInt, label, vars.length, names, isPos, heads.map(relOf(sem, _)), premiseRels, lits)
                case _ => None
            })
            for
              rs <- relations
              ru <- rules
            yield
              val arguments = p match
                case Val.Top(_, sp, _) => sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }
                case _ => Nil
              val strata =
                listElems(proj(rec, "strata")).toList.flatten.map(s => listElems(s).toList.flatten.flatMap(natValue).map(_.toInt))
              ProgramData(rs, ru, display, display.map(_.context).getOrElse(Nil), arguments, strata)
          case _ => None
      catch case _: Impossible => None
    }

  /** The relation of an atom `cat ρ ts` of a rule: `own i` or `ext` of a constant. */
  private def relOf(sem: Map[Name, Int], atom: Val): Option[RelKey] = forceData(atom) match
    case Val.Rigid(Head.Glob(_), sp) => sp.reverse.collectFirst { case Elim.EApp(r, Icit.Expl) => r }.flatMap(rrefKey(sem, _))
    case _ => None

  /** A relation `own i` or `ext` of a constant as a key (`None` for `arg l`). */
  private def rrefKey(sem: Map[Name, Int], r: Val): Option[RelKey] = forceData(r) match
    case Val.Rigid(Head.Glob(k), rsp) =>
      val arg = rsp.collectFirst { case Elim.EApp(x, Icit.Expl) => x }
      if k == sem("own") then arg.flatMap(natValue).map(n => Left(n.toInt))
      else if k == sem("ext") then
        arg.map(forceData).collect { case Val.Quote(q) => forceData(q) }.collect { case Val.Rigid(Head.Glob(id), Nil) =>
          Right(globals(id).name)
        }
      else None
    case _ => None

  private def natValue(v: Val): Option[BigInt] = forceData(v) match
    case Val.Nat(_, n) => Some(n)
    case _ => None

  /** The first rule of a program value with a negation or an aggregate in its body, if its rules
   *  evaluate: the relation of its head (if known by name) and whether it is an aggregate. */
  private def nonPositiveRule(sem: Map[Name, Int], p: Val): Option[(Option[String], Boolean)] =
    try
      forceData(p) match
        case rec: Val.Rec =>
          val relations = listElems(proj(rec, "relations")).map(_.map(forceData).collect {
            case Val.Lit(hugin.syntax.Literal.StrL(s), _) => s
          })
          listElems(proj(rec, "rules")).getOrElse(Nil).iterator.flatMap { r =>
            forceData(r) match
              case rr: Val.Rec =>
                val kinds = listElems(proj(rr, "body")).getOrElse(Nil).map(forceData).collect {
                  case Val.Rigid(Head.Glob(id), _) if sem.get("cnot").contains(id) => false
                  case Val.Rigid(Head.Glob(id), _) if sem.get("cagg").contains(id) => true
                }
                kinds.headOption.map { aggregate =>
                  val rel = natValue(proj(rr, "head")).flatMap(h => relations.flatMap(_.lift(h.toInt)))
                  (rel, aggregate)
                }
              case _ => None
          }.nextOption()
        case _ => None
    catch case _: Impossible => None

  /** The elements of a meta list value, if it is a list of known length. */
  private def listElems(v: Val): Option[List[Val]] =
    reflectiveGlobals.flatMap { r =>
      val out = mutable.ListBuffer.empty[Val]
      var cur = forceData(v)
      var result: Option[List[Val]] = None
      var done = false
      while !done do
        cur match
          case Val.Rigid(Head.Glob(r.nil), _) =>
            result = Some(out.toList)
            done = true
          case Val.Rigid(Head.Glob(r.cons), sp) =>
            sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a } match
              case List(x, xs) =>
                out += x
                cur = forceData(xs)
              case _ => done = true
          case _ => done = true
      result
    }

  /** `derives P d a` as its three arguments. */
  def derivationType(ty: Val): Option[(Val, Val, Val)] =
    semanticsGlobals.flatMap { sem =>
      force(ty) match
        case Val.Rigid(Head.Glob(id), sp) if id == sem("derives") =>
          sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a } match
            case List(p, d, a) => Some((p, d, a))
            case _ => None
        case _ => None
    }

  /** A judgment type as rule names read it (#186 P9c): `derives p d a`, or a stratum-local `nderives (layer p
   *  s) m a` whose database `m` is `upTo p k d` (folded, unfolded, or as the chain of the strata below that
   *  matching on `ngiven` leaves): the whole program `p`, the database `d`, the goal and the stratum `k`. */
  final case class JudgmentView(program: Val, db: Val, goal: Val, stratum: Option[Int])

  def judgmentView(ty: Val): Option[JudgmentView] =
    derivationType(ty).map((p, d, a) => JudgmentView(p, d, a, None)).orElse {
      strataGlobals.flatMap { st =>
        force(ty) match
          case Val.Rigid(Head.Glob(id), sp) if id == st("nderives") =>
            explicitArgs(sp) match
              case List(_, m, a) => stratumDb(st, m, 0).map((p, k, d) => JudgmentView(p, d, a, Some(k)))
              case _ => None
          case _ => None
      }
    }

  private def explicitArgs(sp: Spine): List[Val] = sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }

  /** The program, stratum and database of the database `m` of a stratum's derivations, `depth` strata
   *  above it. */
  private def stratumDb(st: Map[Name, Int], m: Val, depth: Int): Option[(Val, Int, Val)] =
    def read(v: Val, extra: Int): Option[(Val, Int, Val)] = v match
      case Val.Rigid(Head.Glob(id), sp) if id == st("inputs") && explicitArgs(sp).length == 2 + extra =>
        val List(p, d) = explicitArgs(sp).take(2): @unchecked
        Some((p, depth, d))
      case Val.Rigid(Head.Glob(id), sp) if id == st("nderives") && explicitArgs(sp).length == 2 + extra =>
        stratumDb(st, explicitArgs(sp)(1), depth + 1)
      case _ => None
    m match
      case Val.Top(id, sp, _) if id == st("upTo") =>
        explicitArgs(sp) match
          case List(p, k, d) => natValue(k).map(n => (p, n.toInt + depth, d))
          case _ => None
      case _ =>
        force(m) match
          case lam: Val.Lam => read(force(app(lam, Val.local(1 << 24), Icit.Expl)), 1)
          case other => read(other, 0)

  /** The relation of a goal atom `atom ρ vs`: `Left(i)` for `own i`, `Right(shown)` for another relation,
   *  `None` if it is not known. */
  private def goalRelation(sem: Map[Name, Int], a: Val, data: ProgramData, names: List[Name] = Nil): Option[Either[Int, String]] =
    // a parameter relation through its argument, shown in the names `names` of the judgment's context (as
    // the user writes it, `G.edge`), or by its label without them
    def through(i: Int, rest: String): Option[String] =
      Option.when(names.nonEmpty)(()).flatMap(_ => data.arguments.lift(i)).map { v =>
        val shown = showValPlain(names, v)
        if shown.contains(' ') && !shown.startsWith("{") then s"($shown).$rest" else s"$shown.$rest"
      }
    forceData(a) match
      case Val.Rigid(Head.Glob(at), sp) if at == sem("atom") =>
        sp.reverse.collectFirst { case Elim.EApp(r, Icit.Expl) => forceData(r) } match
          case Some(Val.Rigid(Head.Glob(k), rsp)) =>
            val arg = rsp.collectFirst { case Elim.EApp(x, Icit.Expl) => forceData(x) }
            if k == sem("own") then arg.collect { case Val.Nat(_, n) => Left(n.toInt) }
            else if k == sem("arg") then
              arg.collect { case Val.Lit(hugin.syntax.Literal.StrL(l), _) =>
                val (x, rest) = l.span(_ != '.')
                Right(
                  if data.context.length == 1 && !l.contains('.') then through(0, l).getOrElse(l)
                  else if rest.nonEmpty then through(data.context.indexOf(x), rest.drop(1)).getOrElse(l)
                  else l
                )
              }
            else if k == sem("ext") then
              arg.collect { case Val.Quote(q) => forceData(q) }.collect { case Val.Rigid(Head.Glob(id), Nil) => Right(globals(id).name) }
            else None
          case _ => None
      case _ => None

  // ---------------------------------------------------------------- rule names

  /** A rule name: `r.k`, a label, or `given` with one argument. */
  private enum RuleForm:
    case Indexed(rel: Name, k: Int)
    case Label(name: Name)
    case Given

  private def ruleForm(c: Cxt, head: Tree, explicitArgs: Int): Option[RuleForm] = head match
    case Select(Ident(r), k) if k.nonEmpty && k.forall(_.isDigit) => Some(RuleForm.Indexed(r, k.toInt))
    case Ident("given") if explicitArgs == 1 && !c.scope.contains("given") && givenIsSemantics => Some(RuleForm.Given)
    case Ident(l) if !c.scope.contains(l) && lookupGlobal(l).isEmpty => Some(RuleForm.Label(l))
    case _ => None

  /** Whether `t` may be a rule name, by its form alone (cheap: tried for every checked term). */
  def mayBeRuleName(c: Cxt, t: Tree): Boolean =
    val (head, args) = TreeOps.flattenApp(t)
    head match
      case Select(Ident(_), k) => k.nonEmpty && k.forall(_.isDigit)
      case Ident("given") => args.count(!_.isInstanceOf[NamedArg]) == 1 && !c.scope.contains("given")
      case Ident(l) => !c.scope.contains(l) && !state.bodyDeclared(l) && lookupGlobal(l).isEmpty && semanticsGlobals.isDefined
      case _ => false

  private def givenIsSemantics: Boolean =
    semanticsGlobals.exists(sem => lookupGlobal("given").forall(_ == sem("given")))

  /** The (rule, head) pair a form names in the program, checked against the goal; `None` for a label the
   *  program does not have (the name is then elaborated as usual). `r.k` names the `k`-th head of `r`; a
   *  label names the head of its rule whose relation is the goal's (E0948 if there are several), the first
   *  head where the goal's relation is not known. `hint` is the goal's relation where the goal is not
   *  known yet (a premise of a rule pattern). */
  private def namedRule(
      sem: Map[Name, Int],
      form: RuleForm,
      data: ProgramData,
      goal: Val,
      shown: String,
      at: Span,
      names: List[Name] = Nil,
      hint: Option[RelKey] = None
  ): Option[HeadName] =
    val programShown = data.display.flatMap(_.functor).getOrElse("the program")
    val goalRel = goalRelation(sem, goal, data, names).orElse(hint)
    def relShown(k: RelKey) = k.fold(data.relations.lift(_).getOrElse("?"), identity)
    val named = form match
      case RuleForm.Indexed(r, k) =>
        // a relation of the program, or a constant of the file that a head builds (a nested fact's)
        val i = data.relations.indexOf(r)
        val key: RelKey = if i >= 0 then Left(i) else Right(r)
        if i < 0 && !data.headNames.exists(_.rel == key) then
          fail(JudgmentProblem.UnknownRule(shown, programShown, s"it has no relation `$r`", at))
        val ofR = data.headNames.filter(_.rel == key)
        Some(ofR.find(_.k == k).getOrElse {
          val why = if ofR.isEmpty then s"`$r` has no rules" else s"`$r` has ${ofR.length} rule(s), `$r.1` to `$r.${ofR.length}`"
          fail(JudgmentProblem.UnknownRule(shown, programShown, why, at))
        })
      case RuleForm.Label(l) =>
        data.rules.find(_.label.contains(l)).map { rd =>
          val first = data.headNames.find(_.rule.position == rd.position).getOrElse(HeadName(rd, 0, Left(rd.head), rd.index))
          goalRel match
            case Some(i) =>
              data.headsOf(rd, i) match
                case List(h) => h
                case Nil => first
                case hs => fail(JudgmentProblem.LabelHeads(l, relShown(i), hs.map(h => s"${relShown(i)}.${h.k}"), at))
            case _ => first
        }
      case RuleForm.Given => None
    named.foreach { h =>
      goalRel.foreach {
        case k if k == h.rel =>
        case other =>
          val goalShown = other match
            case Left(i) => data.relations.lift(i).getOrElse(s"own $i")
            case Right(s) => s
          fail(JudgmentProblem.RuleHeadMismatch(shown, relShown(h.rel), goalShown, at))
      }
    }
    named

  /** The proof `there^j here` that a rule's `j`-th head atom is the goal's. */
  private def headProof[A](j: Int, here: A, there: A => A): A = (0 until j).foldLeft(here)((acc, _) => there(acc))

  /** The globals rule names elaborate to. */
  private final case class RuleGlobals(
      fire: Int,
      givenC: Int,
      here: Int,
      there: Int,
      econs: Int,
      enil: Int,
      ppos: Int,
      pcmp: Int,
      pnil: Int,
      refl: Int
  )

  private def ruleGlobals(sem: Map[Name, Int]): RuleGlobals =
    // `refl` is the constructor of the equation `ppos` takes (the family `eq` of `std/eq`)
    val refl = telescope(globals(sem("ppos")).ty)._1.collectFirst { case (_, Icit.Expl, d) => d }.map(force) match
      case Some(Val.Rigid(Head.Glob(eq), _)) => constructors(eq).head
      case other => throw Impossible(s"ppos over $other")
    RuleGlobals(
      sem("fire"),
      sem("given"),
      sem("here"),
      sem("there"),
      sem("econs"),
      sem("enil"),
      sem("ppos"),
      sem("pcmp"),
      sem("pnil"),
      refl
    )

  private def ruleShown(head: Tree): String = hugin.syntax.Printer.show(head)

  /** A rule name checked against the derivation type `a` (an expression), or `None` if `t` is not one. */
  def checkRuleName(c: Cxt, t: Tree, a: Val): Option[Tm] =
    val (head, args) = TreeOps.flattenApp(t)
    val (named, positional) = args.partition(_.isInstanceOf[NamedArg])
    ruleForm(c, head, positional.length).flatMap { form =>
      val sem = semanticsGlobals.get
      val shown = ruleShown(head)
      def without: Option[Tm] = form match
        case RuleForm.Indexed(_, _) => fail(JudgmentProblem.RuleNameWithoutJudgment(shown, head.span))
        case _ => None
      judgmentView(a) match
        case None => without
        case Some(view) =>
          val g = ruleGlobals(sem)
          val p = view.program
          form match
            case RuleForm.Given =>
              Option.when(named.isEmpty)(view.stratum match
                case None => checkGiven(c, sem, g, positional.head, p, view.goal, a, head.span)
                case Some(j) => checkGivenIn(c, sem, view, j, positional.head, a, head.span)
              )
            case _ =>
              programData(p) match
                case None => without
                case Some(data) =>
                  val byName = named.collect { case n: NamedArg => n }
                  namedRule(sem, form, data, view.goal, shown, head.span, c.names).map(h =>
                    view.stratum match
                      case None => checkRule(c, g, h, shown, head, byName, positional, a)
                      case Some(j) => checkRuleIn(c, g, data, view, j, h, shown, head, byName, positional, a)
                  )
    }

  /** `fire` at the rule, its premises checked in body order (comparisons proved by evaluation). */
  private def checkRule(
      c: Cxt,
      g: RuleGlobals,
      named: HeadName,
      shown: String,
      head: Tree,
      byName: List[NamedArg],
      premises: List[Tree],
      expected: Val
  ): Tm =
    val rule = named.rule
    val sp = head.span
    val premiseCount = rule.body.count(identity)
    if premises.length != premiseCount then
      fail(JudgmentProblem.PremiseCount(
        shown,
        premiseCount,
        premises.length,
        Span(sp.origin, sp.from, premises.lastOption.map(_.span.until).getOrElse(sp.until))
      ))
    for n <- byName if !rule.names.contains(n.name) do
      fail(JudgmentProblem.NoRuleVariable(shown, n.name, rule.names.filter(isVariableName), n.nameSpan))
    def ref(id: Int) = SymRef(id, globals(id).name)(sp)
    val sem = semanticsGlobals.get
    // `fire`: its implicit arguments unknown and its result unified with the goal; the rule (its member
    // proof) and with it the rule's variables; the head, which determines the variables in it; then the
    // premises in body order, and the comparisons last, proved by evaluation
    val (fire, fireArgs) = applied(c, g.fire, 3, expected, shown, sp)
    val member = (0 until rule.position).foldLeft(ref(g.here): Tree)((acc, _) => Apply(ref(g.there), acc)(sp))
    val m = check(c, member, fireArgs.dom(Nil), Stage.S1)
    val (xsDom, xsMeta) = fireArgs.implicits("xs")
    val supplied = (0 until rule.vars).map(i => rule.names.lift(i).flatMap(x => byName.find(_.name == x)).map(_.value)).toList
    unifyAt(c, sp, xsMeta, ev(c, ruleEnv(c, g, xsDom, supplied, shown, rule.names, sp)))
    val psMeta = freshMeta(c, fireArgs.dom(List(m)), Stage.S1, sp, s"the premises of `$shown`")
    // the head: `there^j here` for the rule's `j`-th head atom (#186 P9d)
    val h = check(c, headProof[Tree](named.j, ref(g.here), Apply(ref(g.there), _)(sp)), fireArgs.dom(List(m, psMeta)), Stage.S1)
    val comparisons = mutable.ListBuffer.empty[(Val, Tm)]
    var remaining = premises
    def premisesTm(lits: List[Boolean], ty: Val): Tm = lits match
      case Nil => check(c, ref(g.pnil), ty, Stage.S1)
      case true :: rest =>
        val (pp, args) = applied(c, g.ppos, 3, ty, shown, sp)
        val eq = check(c, ref(g.refl), args.dom(Nil), Stage.S1)
        val e = check(c, remaining.head, args.dom(List(eq)), Stage.S1)
        remaining = remaining.tail
        val tail = premisesTm(rest, args.dom(List(eq, e)))
        Tm.apps(pp, List((eq, Icit.Expl), (e, Icit.Expl), (tail, Icit.Expl)))
      case false :: rest =>
        val (pc, args) = applied(c, g.pcmp, 2, ty, shown, sp)
        val proof = freshMeta(c, args.dom(Nil), Stage.S1, sp, s"a comparison of `$shown`")
        comparisons += ((args.dom(Nil), proof))
        val tail = premisesTm(rest, args.dom(List(proof)))
        Tm.apps(pc, List((proof, Icit.Expl), (tail, Icit.Expl)))
    val ps = premisesTm(rule.body, fireArgs.dom(List(m)))
    unifyAt(c, sp, ev(c, psMeta), ev(c, ps))
    for (ty, proof) <- comparisons do unifyAt(c, sp, ev(c, proof), ev(c, comparisonProof(c, sem, ty, shown, sp)))
    Tm.apps(fire, List((m, Icit.Expl), (ps, Icit.Expl), (h, Icit.Expl)))

  /** A constant applied to unknowns for its implicit arguments, its type after `n` explicit ones unified with
   *  `expected`; with the types of the explicit arguments ([[Applied.dom]]) and the implicit arguments. */
  private final class Applied(c: Cxt, start: Val, val implicits: Map[Name, (Val, Val)]):
    /** The type of the next explicit argument, given the ones before it (terms in `c`). */
    def dom(before: List[Tm]): Val =
      var t = start
      for b <- before do
        force(t) match
          case Val.Pi(_, Icit.Expl, _, cl) => t = inst(cl, ev(c, b))
          case _ => throw Impossible("too many arguments")
      force(t) match
        case Val.Pi(_, Icit.Expl, d, _) => d
        case _ => throw Impossible("too many arguments")

  private def applied(c: Cxt, id: Int, n: Int, expected: Val, shown: String, sp: Span): (Tm, Applied) =
    var ft: Tm = Tm.Global(id)
    var fty = globals(id).ty
    val implicits = mutable.LinkedHashMap.empty[Name, (Val, Val)]
    var more = true
    while more do
      force(fty) match
        case Val.Pi(x, Icit.Impl, dom, cl) =>
          val m = freshMeta(c, dom, Stage.S1, sp, s"the implicit argument `$x` of `$shown`")
          val mv = ev(c, m)
          implicits(x) = (dom, mv)
          ft = Tm.App(ft, m, Icit.Impl)
          fty = inst(cl, mv)
        case _ => more = false
    def after(ty: Val, k: Int): Val =
      if k == n then ty
      else
        force(ty) match
          case Val.Pi(_, Icit.Expl, _, cl) => after(inst(cl, Val.local(c.lvl + k)), k + 1)
          case _ => throw Impossible(s"${globals(id).name} over $n arguments")
    unifyAt(c, sp, expected, after(fty, 0))
    (ft, Applied(c, fty, implicits.toMap))

  /** The proof of a comparison `holdsCmp o x y` of a rule's body, by evaluation: `fromSome (decideCmp o x y)
   *  tt` (E0948 if it does not hold or does not evaluate). */
  private def comparisonProof(c: Cxt, sem: Map[Name, Int], ty: Val, shown: String, sp: Span): Tm =
    forceData(ty) match
      case Val.Rigid(Head.Glob(_), csp) =>
        val args = csp.reverse.collect { case Elim.EApp(a, i) => (quote(c.lvl, a), i) }
        val decided = Tm.apps(Tm.Global(sem("decideCmp")), args)
        val tyTm = quote(c.lvl, ty)
        val so = forceData(ev(c, Tm.apps(Tm.Global(sem("isSome")), List((tyTm, Icit.Impl), (decided, Icit.Expl)))))
        so match
          case Val.Rigid(Head.Glob(t), Nil) if globals(t).name == "true" =>
            Tm.apps(Tm.Global(sem("fromSome")), List((tyTm, Icit.Impl), (decided, Icit.Expl), (Tm.Global(unitConstructor(sem)), Icit.Expl)))
          case _ => fail(JudgmentProblem.ComparisonUndecided(shown, show(c, ty), sp))
      case _ => fail(JudgmentProblem.ComparisonUndecided(shown, show(c, ty), sp))

  /** The values of a rule's variables, `env ts` (`xsDom`, with `ts` known once the rule is): the given
   *  ones checked as code of their types, the others unknowns that the premises and the head determine. */
  private def ruleEnv(c: Cxt, g: RuleGlobals, xsDom: Val, supplied: List[Option[Tree]], shown: String, names: List[Name], sp: Span): Tm =
    val types = force(xsDom) match
      case Val.Rigid(Head.Glob(_), esp) => esp.collectFirst { case Elim.EApp(ts, Icit.Expl) => ts }.flatMap(listElems)
      case _ => None
    val tys = types.getOrElse(throw Impossible(s"the variables of a rule: ${show(c, xsDom)}"))
    val codeT = Tm.Lift(Tm.U0)
    val r = reflective(sp)
    def listTm(ts: List[Tm]): Tm =
      ts.foldRight(Tm.App(Tm.Global(r.nil), codeT, Icit.Impl): Tm)((x, acc) =>
        Tm.apps(Tm.Global(r.cons), List((codeT, Icit.Impl), (x, Icit.Expl), (acc, Icit.Expl)))
      )
    val tyTms = tys.map(t => quote(c.lvl, t))
    tys.indices.foldRight(Tm.Global(g.enil): Tm) { (i, acc) =>
      val tyCode = ev(c, Tm.splice(tyTms(i)))
      val x = supplied.lift(i).flatten match
        case Some(e) => check(c, e, Val.Lift(tyCode), Stage.S1)
        case None => freshMeta(c, Val.Lift(tyCode), Stage.S1, sp, s"the variable `${names.lift(i).getOrElse(s"#$i")}` of the rule `$shown`")
      Tm.apps(Tm.Global(g.econs), List((tyTms(i), Icit.Impl), (listTm(tyTms.drop(i + 1)), Icit.Impl), (x, Icit.Expl), (acc, Icit.Expl)))
    }

  /** The constructor `tt` of `std/eq`'s `unit`, found as the only constructor of the family that
   *  `so true` evaluates to. */
  private def unitConstructor(sem: Map[Name, Int]): Int =
    val soId = telescope(globals(sem("given")).ty)._1.collectFirst { case (_, Icit.Expl, d) => d } match
      case Some(d) =>
        quote(6, d) match
          case Tm.App(Tm.Global(so), _, Icit.Expl) => so
          case other => throw Impossible(s"given over $other")
      case None => throw Impossible("given without arguments")
    val trueId = force(telescope(globals(sem("inputOf")).ty)._2) match
      case Val.Rigid(Head.Glob(bool), _) => constructors(bool).find(globals(_).name == "true").getOrElse(throw Impossible("no true"))
      case other => throw Impossible(s"inputOf into $other")
    forceData(app(Val.Rigid(Head.Glob(soId), Nil), Val.Rigid(Head.Glob(trueId), Nil), Icit.Expl)) match
      case Val.Rigid(Head.Glob(fam), Nil) if constructors(fam).length == 1 => constructors(fam).head
      case other => throw Impossible(s"so true is $other")

  /** `given I`: `given t I` with `t` the proof that the goal's relation is an input. */
  private def checkGiven(c: Cxt, sem: Map[Name, Int], g: RuleGlobals, fact: Tree, p: Val, goal: Val, expected: Val, sp: Span): Tm =
    var ft: Tm = Tm.Global(g.givenC)
    var fty = globals(g.givenC).ty
    var more = true
    while more do
      force(fty) match
        case Val.Pi(x, Icit.Impl, dom, cl) =>
          val m = freshMeta(c, dom, Stage.S1, sp, s"the implicit argument `$x` of `given`")
          ft = Tm.App(ft, m, Icit.Impl)
          fty = inst(cl, ev(c, m))
        case _ => more = false
    val result = force(fty) match
      case Val.Pi(_, _, _, cl1) =>
        force(inst(cl1, Val.local(c.lvl))) match
          case Val.Pi(_, _, _, cl2) => inst(cl2, Val.local(c.lvl + 1))
          case _ => throw Impossible("given over two arguments")
      case _ => throw Impossible("given over two arguments")
    unifyAt(c, sp, expected, result)
    val relShown = programData(p).flatMap(data =>
      goalRelation(sem, goal, data, c.names).map(_.fold(i => data.relations.lift(i).getOrElse(s"own $i"), identity))
    ).getOrElse("the relation")
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, cl) =>
        val proof = forceData(dom) match
          case Val.Rigid(Head.Glob(fam), Nil) if isFamily(fam) && constructors(fam).length == 1 => Tm.Global(constructors(fam).head)
          case Val.Rigid(Head.Glob(fam), Nil) if isFamily(fam) && constructors(fam).isEmpty =>
            fail(JudgmentProblem.NotAnInput(relShown, true, sp))
          case _ => fail(JudgmentProblem.NotAnInput(relShown, false, sp))
        ft = Tm.App(ft, proof, Icit.Expl)
        fty = inst(cl, ev(c, proof))
      case _ => throw Impossible("given over two arguments")
    force(fty) match
      case Val.Pi(_, Icit.Expl, dom, _) => Tm.App(ft, check(c, fact, dom, Stage.S1), Icit.Expl)
      case _ => throw Impossible("given over two arguments")

  // ---------------------------------------------------------------- stratum-local rule names (#186 P9c)

  /** The proof of `so b` for a `b` that evaluates to `true`: the constructor of `unit`. */
  private def unitProof(ty: Val): Option[Tm] = forceData(ty) match
    case Val.Rigid(Head.Glob(fam), Nil) if isFamily(fam) && constructors(fam).length == 1 => Some(Tm.Global(constructors(fam).head))
    case _ => None

  /** `ngiven tt (… (ngiven tt x))`, `levels` times, against `ty`, with `x` built against the type below. */
  private def liftBy(c: Cxt, st: Map[Name, Int], levels: Int, ty: Val, shown: String, sp: Span)(inner: Val => Tm): Tm =
    if levels <= 0 then inner(ty)
    else
      val (ng, args) = applied(c, st("ngiven"), 2, ty, shown, sp)
      val t = unitProof(args.dom(Nil)).getOrElse(throw Impossible("ngiven of a layer, whose relations are all inputs"))
      val x = liftBy(c, st, levels - 1, args.dom(List(t)), shown, sp)(inner)
      Tm.apps(ng, List((t, Icit.Expl), (x, Icit.Expl)))

  /** The stratum (at most `j`) at which a stratum-local derivation fires `rule`: the last layer with it. */
  private def firingStratum(data: ProgramData, rule: RuleData, j: Int, shown: String, sp: Span): Int =
    data.layersOf(rule).filter(_ <= j).maxOption.getOrElse(fail(JudgmentProblem.LaterStratum(shown, sp)))

  /** A rule name against a stratum-local judgment of the stratum `j`: `ngiven` down to the stratum whose layer
   *  fires the rule, then `nfire` there, with its written premises in body order: an atom's derivation lifted
   *  by `ngiven` from its relation's stratum, a negated atom's (a refutation of its relation's judgment if it
   *  has no local variables, see [[negatedPremise]]) and an aggregate's witness. */
  private def checkRuleIn(
      c: Cxt,
      g: RuleGlobals,
      data: ProgramData,
      view: JudgmentView,
      j: Int,
      named: HeadName,
      shown: String,
      head: Tree,
      byName: List[NamedArg],
      premises: List[Tree],
      expected: Val
  ): Tm =
    val st = strataGlobals.get
    val sem = semanticsGlobals.get
    val rule = named.rule
    val sp = head.span
    val count = rule.lits.count(_.written)
    if premises.length != count then
      fail(JudgmentProblem.PremiseCount(
        shown,
        count,
        premises.length,
        Span(sp.origin, sp.from, premises.lastOption.map(_.span.until).getOrElse(sp.until))
      ))
    for n <- byName if !rule.names.contains(n.name) do
      fail(JudgmentProblem.NoRuleVariable(shown, n.name, rule.names.filter(isVariableName), n.nameSpan))
    val at = firingStratum(data, rule, j, shown, sp)
    def ref(id: Int) = SymRef(id, globals(id).name)(sp)
    liftBy(c, st, j - at, expected, shown, sp) { ty =>
      val (fire, fireArgs) = applied(c, st("nfire"), 3, ty, shown, sp)
      val position = data.layerRules(at).indexWhere(_.position == rule.position)
      val member = (0 until position).foldLeft(ref(g.here): Tree)((acc, _) => Apply(ref(g.there), acc)(sp))
      val m = check(c, member, fireArgs.dom(Nil), Stage.S1)
      val (xsDom, xsMeta) = fireArgs.implicits("xs")
      val supplied = (0 until rule.vars).map(i => rule.names.lift(i).flatMap(x => byName.find(_.name == x)).map(_.value)).toList
      unifyAt(c, sp, xsMeta, ev(c, ruleEnv(c, g, xsDom, supplied, shown, rule.names, sp)))
      val psMeta = freshMeta(c, fireArgs.dom(List(m)), Stage.S1, sp, s"the premises of `$shown`")
      val h = check(c, headProof[Tree](named.j, ref(g.here), Apply(ref(g.there), _)(sp)), fireArgs.dom(List(m, psMeta)), Stage.S1)
      val comparisons = mutable.ListBuffer.empty[(Val, Tm)]
      var remaining = premises
      var rels = rule.premiseRels
      def next(): Tree =
        val e = remaining.head
        remaining = remaining.tail
        e
      def premisesTm(lits: List[BodyLit], ty: Val): Tm = lits match
        case Nil => check(c, ref(st("nnil")), ty, Stage.S1)
        case BodyLit.Pos :: rest =>
          val (pp, args) = applied(c, st("npos"), 3, ty, shown, sp)
          val eq = check(c, ref(g.refl), args.dom(Nil), Stage.S1)
          val rel = rels.headOption.flatten
          rels = rels.drop(1)
          val e = next()
          val d = liftBy(c, st, at - data.stratumOf(rel), args.dom(List(eq)), shown, sp)(t => check(c, e, t, Stage.S1))
          val tail = premisesTm(rest, args.dom(List(eq, d)))
          Tm.apps(pp, List((eq, Icit.Expl), (d, Icit.Expl), (tail, Icit.Expl)))
        case BodyLit.Cmp :: rest =>
          val (pc, args) = applied(c, st("ncmp"), 2, ty, shown, sp)
          val proof = freshMeta(c, args.dom(Nil), Stage.S1, sp, s"a comparison of `$shown`")
          comparisons += ((args.dom(Nil), proof))
          val tail = premisesTm(rest, args.dom(List(proof)))
          Tm.apps(pc, List((proof, Icit.Expl), (tail, Icit.Expl)))
        case BodyLit.Neg(rel, locals) :: rest =>
          val (pn, args) = applied(c, st("nneg"), 2, ty, shown, sp)
          val n = negatedPremise(c, st, sem, data, view, at, rel, locals, args, next(), shown, sp)
          val tail = premisesTm(rest, args.dom(List(n)))
          Tm.apps(pn, List((n, Icit.Expl), (tail, Icit.Expl)))
        case BodyLit.Agg :: rest =>
          val (pa, args) = applied(c, st("nagg"), 2, ty, shown, sp)
          val w = check(c, next(), args.dom(Nil), Stage.S1)
          val tail = premisesTm(rest, args.dom(List(w)))
          Tm.apps(pa, List((w, Icit.Expl), (tail, Icit.Expl)))
      val ps = premisesTm(rule.lits, fireArgs.dom(List(m)))
      unifyAt(c, sp, ev(c, psMeta), ev(c, ps))
      for (ty, proof) <- comparisons do unifyAt(c, sp, ev(c, proof), ev(c, comparisonProof(c, sem, ty, shown, sp)))
      Tm.apps(fire, List((m, Icit.Expl), (ps, Icit.Expl), (h, Icit.Expl)))
    }

  /** The premise of a negated atom of a rule that fires at the stratum `at`. Without local variables, and of
   *  a relation `rel` of a stratum `k` below: a refutation `P ⊢ q t̄ -> empty` of its judgment, made the
   *  premise `absent …` by `absentOf k at tt`, or else the premise itself; with local variables, the premise
   *  `absent …` (#186 P9c, the addendum of proofs-level35 §6.3). */
  private def negatedPremise(
      c: Cxt,
      st: Map[Name, Int],
      sem: Map[Name, Int],
      data: ProgramData,
      view: JudgmentView,
      at: Int,
      rel: Option[RelKey],
      locals: Boolean,
      args: Applied,
      e: Tree,
      shown: String,
      sp: Span
  ): Tm =
    val raw = args.dom(Nil)
    val k = data.stratumOf(rel)
    def direct: Tm = check(c, e, raw, Stage.S1)
    if locals || rel.isEmpty || k >= at then direct
    else
      val nat = natOf(sem)
      def q(n: Name) = quote(c.lvl, args.implicits(n)._2)
      val implicits = List(quote(c.lvl, view.program), quote(c.lvl, view.db), q("ts"), q("xs"), q("b")).map((_, Icit.Impl))
      val head =
        Tm.apps(Tm.Global(st("absentOf")), implicits ++ List((Tm.Nat(nat, BigInt(k)), Icit.Expl), (Tm.Nat(nat, BigInt(at)), Icit.Expl)))
      var ty = globals(st("absentOf")).ty
      for (a, _) <- implicits ++ List((Tm.Nat(nat, BigInt(k)), Icit.Expl), (Tm.Nat(nat, BigInt(at)), Icit.Expl)) do
        force(ty) match
          case Val.Pi(_, _, _, cl) => ty = inst(cl, ev(c, a))
          case _ => throw Impossible("absentOf over seven arguments")
      force(ty) match
        case Val.Pi(_, Icit.Expl, so, cl) =>
          unitProof(so) match
            case None => direct
            case Some(t) =>
              force(inst(cl, ev(c, t))) match
                case Val.Pi(_, Icit.Expl, refutation, cl2) =>
                  try
                    undoOnFailure {
                      val r = check(c, e, refutation, Stage.S1)
                      unifyAt(c, sp, raw, inst(cl2, ev(c, r)))
                      Tm.apps(head, List((t, Icit.Expl), (r, Icit.Expl)))
                    }
                  catch
                    case first: ElabError =>
                      try undoOnFailure(direct)
                      catch case _: ElabError => throw first
                case _ => throw Impossible("absentOf over nine arguments")
        case _ => throw Impossible("absentOf over eight arguments")

  /** `given I` against a stratum-local judgment of the stratum `j`: for an input relation, `ngiven` down to
   *  the program's input facts, `{ fst = tt, snd = I }`; for a relation with rules whose judgment's stratum
   *  `k` is `j` or below, `I` is its judgment, lifted by `ngiven` (E0949 otherwise). */
  private def checkGivenIn(c: Cxt, sem: Map[Name, Int], view: JudgmentView, j: Int, fact: Tree, expected: Val, sp: Span): Tm =
    val st = strataGlobals.get
    val data = programData(view.program)
    val relShown =
      data.flatMap(d => goalRelation(sem, view.goal, d, c.names).map(_.fold(i => d.relations.lift(i).getOrElse(s"own $i"), identity)))
        .getOrElse("the relation")
    val input = forceData(app(proj(forceData(view.program), "input"), goalRef(sem, view.goal), Icit.Expl)) match
      case Val.Rigid(Head.Glob(id), Nil) => Some(globals(id).name != "false")
      case _ => None
    input match
      case Some(true) =>
        liftBy(c, st, j, expected, "given", sp) { ty =>
          val (ng, args) = applied(c, st("ngiven"), 2, ty, "given", sp)
          val t = unitProof(args.dom(Nil)).getOrElse(throw Impossible("ngiven of a layer, whose relations are all inputs"))
          val record = force(args.dom(List(t))) match
            case Val.RecTy(List(fst, snd), env, List(fstTy, sndTy), _, _) =>
              val proof = unitProof(eval(env, fstTy)).getOrElse(fail(JudgmentProblem.NotAnInput(relShown, false, sp)))
              val i = check(c, fact, eval(ev(c, proof) :: env, sndTy), Stage.S1)
              Tm.Rec(List(fst -> proof, snd -> i))
            case other => throw Impossible(s"the input facts of a program: ${show(c, other)}")
          Tm.apps(ng, List((t, Icit.Expl), (record, Icit.Expl)))
        }
      case Some(false) =>
        val k = data.fold(j)(d => d.stratumOf(goalRelation(sem, view.goal, d)))
        if k > j then fail(JudgmentProblem.NotAnInput(relShown, true, sp))
        liftBy(c, st, j - k, expected, "given", sp)(ty => check(c, fact, ty, Stage.S1))
      case None => fail(JudgmentProblem.NotAnInput(relShown, false, sp))

  /** A name a rule variable can be bound by in a pattern (written in the rule: not a wildcard or a
   *  generated name). */
  private def isVariableName(x: Name): Boolean =
    x.nonEmpty && x.head.isUpper && x.forall(ch => ch.isLetterOrDigit || ch == '_' || ch == '\'')

  // ---------------------------------------------------------------- rule names as patterns

  /** A rule name as a pattern against the (possibly open) derivation type `ty`, or `None` if `t` is not one. */
  def rulePattern(t: Tree, ty: Val): Option[Pat] =
    val (head, args) = TreeOps.flattenApp(t)
    val positional = args.count(!_.isInstanceOf[NamedArg])
    if semanticsGlobals.isEmpty then None
    else
      ruleForm(Cxt.empty, head, positional).flatMap { form =>
        judgmentView(ty) match
          case Some(view) => rulePatternIn(t, form, view.program, view.goal, None, view.stratum)
          case None =>
            form match
              case RuleForm.Indexed(_, _) => fail(JudgmentProblem.RuleNameWithoutJudgment(ruleShown(head), head.span))
              case _ => None
      }

  private def rulePatternIn(t: Tree, form: RuleForm, p: Val, goal: Val, hint: Option[RelKey], stratum: Option[Int]): Option[Pat] =
    val sem = semanticsGlobals.get
    val g = ruleGlobals(sem)
    val (head, args) = TreeOps.flattenApp(t)
    val named = args.collect { case n: NamedArg => n }
    val positional = args.filterNot(_.isInstanceOf[NamedArg])
    val sp = t.span
    val shown = ruleShown(head)
    // a premise: a rule name of the same program (of the premise's relation `rel`, if own; at the stratum `k`
    // of its judgment, if stratified), or any pattern
    def premise(e: Tree, rel: Option[RelKey], k: Option[Int] = None): Pat =
      val (h, as) = TreeOps.flattenApp(e)
      ruleForm(Cxt.empty, h, as.count(!_.isInstanceOf[NamedArg])).flatMap(f => rulePatternIn(e, f, p, Val.Wild, rel, k)).getOrElse(pattern(
        e,
        None
      ))
    // `ngiven _ (… (ngiven _ q))`, `levels` times
    def lifted(levels: Int, q: Pat): Pat =
      (0 until levels).foldLeft(q)((acc, _) => Pat.PCon(strataGlobals.get("ngiven"), List(Pat.PWild(sp), acc), sp))
    form match
      case RuleForm.Given if stratum.isDefined =>
        if named.nonEmpty then None
        else
          // a judgment of a stratum `k` below, lifted, for a relation with rules; otherwise down to the input
          // facts (where, for a relation with rules, `I.fst` refutes it)
          val j = stratum.get
          val data = programData(p)
          val rel = data.flatMap(d => goalRelation(sem, goal, d).orElse(hint))
          val k = for d <- data; r <- rel if d.headNames.exists(_.rel == r) yield d.stratumOf(rel)
          val levels = k.filter(_ < j).fold(j + 1)(j - _)
          Some(lifted(levels, premise(positional.head, None)))
      case RuleForm.Given =>
        if named.nonEmpty then None
        else Some(Pat.PCon(g.givenC, List(Pat.PWild(sp), premise(positional.head, None)), sp))
      case _ =>
        val data = programData(p) match
          case Some(d) => d
          case None =>
            form match
              case RuleForm.Indexed(_, _) => fail(JudgmentProblem.RuleNameWithoutJudgment(shown, head.span))
              case _ => ProgramData(Nil, Nil, None, Nil)
        namedRule(sem, form, data, goal, shown, head.span, hint = hint).map { hn =>
          val rule = hn.rule
          val premiseCount = if stratum.isDefined then rule.lits.count(_.written) else rule.body.count(identity)
          if positional.length != premiseCount then fail(JudgmentProblem.PremiseCount(shown, premiseCount, positional.length, sp))
          for n <- named if !rule.names.contains(n.name) do
            fail(JudgmentProblem.NoRuleVariable(shown, n.name, rule.names.filter(isVariableName), n.nameSpan))
          val member = (0 until rule.position).foldLeft(Pat.PCon(g.here, Nil, sp))((acc, _) => Pat.PCon(g.there, List(acc), sp))
          val env = (0 until rule.vars).foldRight(Pat.PCon(g.enil, Nil, sp)) { (i, acc) =>
            val x = rule.names.lift(i)
            val pat = x.flatMap(n => named.find(_.name == n)) match
              case Some(na) => pattern(na.value, None)
              case None => x.filter(isVariableName).map(n => Pat.PVar(n, head.span, implicitBinder = true)).getOrElse(Pat.PWild(sp))
            Pat.PCon(g.econs, List(pat, acc), sp)
          }
          var rest = positional
          var rels = rule.premiseRels
          def prems(lits: List[Boolean]): Pat = lits match
            case Nil => Pat.PCon(g.pnil, Nil, sp)
            case true :: more =>
              val e = premise(rest.head, rels.headOption.flatten)
              rest = rest.tail
              rels = rels.drop(1)
              Pat.PCon(g.ppos, List(Pat.PCon(g.refl, Nil, sp), e, prems(more)), sp)
            case false :: more => Pat.PCon(g.pcmp, List(Pat.PWild(sp), prems(more)), sp)
          // the head: `there^j here` for the rule's `j`-th head atom (#186 P9d)
          val headPat = headProof[Pat](hn.j, Pat.PCon(g.here, Nil, sp), q => Pat.PCon(g.there, List(q), sp))
          stratum match
            case None => Pat.PCon(g.fire, List(member, prems(rule.body), headPat), sp, List("xs" -> env))
            case Some(j) =>
              // stratum-local (#186 P9c): `ngiven` down to the stratum that fires the rule, `nfire` there
              val st = strataGlobals.get
              val at = firingStratum(data, rule, j, shown, head.span)
              val position = data.layerRules(at).indexWhere(_.position == rule.position)
              val layerMember = (0 until position).foldLeft(Pat.PCon(g.here, Nil, sp))((acc, _) => Pat.PCon(g.there, List(acc), sp))
              def nprems(lits: List[BodyLit]): Pat = lits match
                case Nil => Pat.PCon(st("nnil"), Nil, sp)
                case BodyLit.Pos :: more =>
                  val rel = rels.headOption.flatten
                  val k = data.stratumOf(rel)
                  val e = premise(rest.head, rel, Some(math.min(k, at)))
                  rest = rest.tail
                  rels = rels.drop(1)
                  Pat.PCon(st("npos"), List(Pat.PCon(g.refl, Nil, sp), lifted(at - k, e), nprems(more)), sp)
                case BodyLit.Cmp :: more => Pat.PCon(st("ncmp"), List(Pat.PWild(sp), nprems(more)), sp)
                case BodyLit.Neg(_, _) :: more =>
                  val e = pattern(rest.head, None)
                  rest = rest.tail
                  Pat.PCon(st("nneg"), List(e, nprems(more)), sp)
                case BodyLit.Agg :: more =>
                  val e = pattern(rest.head, None)
                  rest = rest.tail
                  Pat.PCon(st("nagg"), List(e, nprems(more)), sp)
              lifted(j - at, Pat.PCon(st("nfire"), List(layerMember, nprems(rule.lits), headPat), sp, List("xs" -> env)))
        }

  // ---------------------------------------------------------------- coverage

  /** Below a derivation `given …` or `fire …` of a program whose rules are known, the positions (relative,
   *  the last step first) of `fire`'s rule and head proofs and of their `there` chains, as long as the
   *  program's rules and heads: with them in Π, coverage splits a derivation into the program's rules, and
   *  refutes those whose head does not match the goal (reference: meta/coverage, "Derivations"). */
  def derivationPositions(ctor: Int, sp: Spine): Option[List[List[Int]]] =
    // also `ngiven` and `nfire` of a stratum, whose program is the stratum's layer (#186 P9c)
    def stratified = strataGlobals.exists(st => ctor == st("ngiven") || ctor == st("nfire"))
    semanticsGlobals.filter(sem => ctor == sem("given") || ctor == sem("fire") || stratified).flatMap { _ =>
      sp.reverse.collectFirst { case Elim.EApp(p, Icit.Impl) => p }.flatMap(programData).map { data =>
        val rules = data.rules.length
        val heads = data.rules.map(_.heads).maxOption.getOrElse(1)
        def chain(start: Int, depth: Int): List[List[Int]] = (0 to depth).toList.map(k => List.fill(k)(0) :+ start)
        chain(0, rules) ++ chain(2, heads)
      }
    }

  // ---------------------------------------------------------------- case splits

  /** The patterns a split of a variable of the derivation type `ty` offers (for tooling): the rules whose
   *  head relation is the goal's, by their names, with their premises named by their relations, and `given`
   *  if the goal's relation is an input; each case's names are fresh against `taken`. */
  def ruleSplits(ty: Val, taken: Iterable[String]): Option[List[String]] =
    judgmentView(ty).flatMap { view =>
      val sem = semanticsGlobals.get
      val p = view.program
      val goal = view.goal
      programData(p).map { data =>
        val rel = goalRelation(sem, goal, data)
        // every (rule, head) pair of the goal's relation, by its label if it names that head alone; at a
        // stratum, those of the rules that fire in it or below (#186 P9c)
        val heads = data.headNames.filter(h => rel.forall(_ == h.rel) && view.stratum.forall(j => data.layersOf(h.rule).exists(_ <= j)))
        val premiseNames = premiseInitials(p, sem, data, view.stratum.isDefined)
        val ruleCases = heads.map { h =>
          val r = h.rule
          val byLabel =
            data.headsOf(r, h.rel).length == 1 && (rel.isDefined || data.headNames.find(_.rule.position == r.position).contains(h))
          val name = r.label.filter(_ => byLabel).getOrElse(s"${h.rel.fold(data.relations.lift(_).getOrElse("?"), identity)}.${h.k}")
          val fresh = FreshNames(taken)
          val ps = premiseNames.lift(r.position).getOrElse(Nil).map(fresh(_))
          if ps.isEmpty then name else (name :: ps).mkString("(", " ", ")")
        }
        val input = forceData(app(proj(forceData(p), "input"), goalRef(sem, goal), Icit.Expl)) match
          case Val.Rigid(Head.Glob(id), Nil) => globals(id).name != "false"
          case _ => true
        // at a stratum, `given` is a case for every relation: the facts from below (#186 P9c)
        if input || view.stratum.isDefined then ruleCases :+ s"(given ${FreshNames(taken)("I")})" else ruleCases
      }
    }

  private def goalRef(sem: Map[Name, Int], goal: Val): Val = forceData(goal) match
    case Val.Rigid(Head.Glob(_), sp) => sp.reverse.collectFirst { case Elim.EApp(r, Icit.Expl) => r }.getOrElse(Val.Wild)
    case _ => Val.Wild

  /** For each rule, the names of its premises: the initial of the premise's relation, capitalised (`E`
   *  for `g.edge`, `P` for `path`). */
  private def premiseInitials(p: Val, sem: Map[Name, Int], data: ProgramData, stratified: Boolean = false): List[List[String]] =
    listElems(proj(forceData(p), "rules")).getOrElse(Nil).map { r =>
      listElems(proj(forceData(r), "body")).getOrElse(Nil).flatMap { b =>
        forceData(b) match
          case Val.Rigid(Head.Glob(id), sp) if id == sem("cpos") =>
            val atom = sp.reverse.collectFirst { case Elim.EApp(a, Icit.Expl) => forceData(a) }
            val rel = atom.flatMap {
              case Val.Rigid(Head.Glob(_), asp) => asp.reverse.collectFirst { case Elim.EApp(x, Icit.Expl) => x }
              case _ => None
            }
            val name = rel.map(forceData) match
              case Some(Val.Rigid(Head.Glob(k), rsp)) =>
                val arg = rsp.collectFirst { case Elim.EApp(x, Icit.Expl) => forceData(x) }
                if k == sem("own") then arg.collect { case Val.Nat(_, n) => data.relations.lift(n.toInt).getOrElse("p") }.getOrElse("p")
                else if k == sem("arg") then
                  arg.collect { case Val.Lit(hugin.syntax.Literal.StrL(l), _) => l.split('.').last }.getOrElse("p")
                else
                  arg.collect { case Val.Quote(q) => forceData(q) }.collect { case Val.Rigid(Head.Glob(g), Nil) =>
                    globals(g).name.split('.').last
                  }.getOrElse("p")
              case _ => "p"
            List(name.take(1).toUpperCase)
          // the written premises of a stratum-local rule name (#186 P9c)
          case Val.Rigid(Head.Glob(id), _) if stratified && sem.get("cnot").contains(id) => List("N")
          case Val.Rigid(Head.Glob(id), _) if stratified && sem.get("cagg").contains(id) => List("A")
          case _ => Nil
      }
    }
