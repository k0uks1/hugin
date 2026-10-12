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
 *  - In the type of a declaration, a functor written alone before `⊢` stands for the functor applied to its
 *    parameters, and a judgment without `[e]` for one at the database `d`: they become the declaration's
 *    first implicit binders, shared by its judgments (Agda's generalisation of declared variables, Lean's
 *    auto-bound implicits).
 *  - A rule name `r.k` (or a rule's label) is a pattern synonym for `fire` at the `k`-th rule of `r`, with
 *    the rule's variables, its premises in body order and its first head: as a pattern on a derivation, and
 *    as an expression that builds one. `given I` is `given t I` with `t` the proof that the relation is an
 *    input (Agda's pattern synonyms, Isabelle's `tc.intros(k)`, Abella's `case` on `{P |- A}`). */
trait Judgments:
  self: Elaborator =>
  import core.*

  // ---------------------------------------------------------------- the judgment

  /** `P ⊢[e] r t̄`. */
  def inferJudgment(c: Cxt, j: Judgment): (Tm, Val, Stage) =
    val sem = semanticsGlobals.getOrElse(fail(JudgmentProblem.NoLibrary(j.opSpan)))
    val programTy = eval(Nil, Tm.Global(sem("program")))
    // the program: a functor alone is applied to its parameters, which generalisation bound
    val (prog, scope) = generalisedFunctor(j.program) match
      case Some((name, params)) =>
        val applied = params.foldLeft(j.program) { (f, x) =>
          if !c.scope.contains(x) then
            fail(JudgmentProblem.CannotGeneralise(
              name,
              x,
              s"`$x` is not in scope here (generalisation applies in the type of a declaration)",
              j.program.span
            ))
          Apply(f, Ident(x)(j.program.span))(j.program.span)
        }
        judgmentProgram(c, applied, j.opSpan)
      case None =>
        if programValued(c, j.program, programTy) then (check(c, j.program, programTy, Stage.S1), None)
        else judgmentProgram(c, j.program, j.opSpan)
    val programShown = hugin.syntax.Printer.show(j.program)
    // the notation reads the program in `derives`, the positive fragment (#186 P9a, E0961)
    nonPositiveRule(sem, ev(c, prog)).foreach { (rel, aggregate) =>
      fail(JudgmentProblem.NotPositive(programShown, rel, aggregate, j.program.span))
    }
    // the database
    val dbTy = eval(Nil, Tm.Global(sem("db")))
    val db = j.db match
      case Some(e) => check(c, e, dbTy, Stage.S1)
      case None =>
        if !c.scope.contains("d") then fail(JudgmentProblem.NoDatabase(j.opSpan))
        check(c, Ident("d")(j.opSpan), dbTy, Stage.S1)
    // the atom: its relation in the program's scope, its arguments as code of the relation's column types
    val (head, args) = TreeOps.flattenApp(j.atom)
    val path = namePath(head).getOrElse(fail(JudgmentProblem.NotAnAtom(hugin.syntax.Printer.show(j.atom), j.atom.span)))
    val relShown = path.mkString(".")
    val (ref, relTy) =
      relationRef(c, sem, prog, scope, path).getOrElse(fail(JudgmentProblem.UnknownRelation(relShown, programShown, head.span)))
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
    val tm = Tm.apps(Tm.Global(sem("derives")), List((prog, Icit.Expl), (db, Icit.Expl), (atomTm, Icit.Expl)))
    var ty = globals(sem("derives")).ty
    for a <- List(prog, db, atomTm) do
      force(ty) match
        case Val.Pi(_, _, _, cl) => ty = inst(cl, ev(c, a))
        case _ => throw Impossible("derives over three arguments")
    (tm, ty, Stage.S1)

  /** `a.b.c` as a path of names. */
  private def namePath(t: Tree): Option[List[Name]] = t match
    case Ident(n) => Some(List(n))
    case Select(q, n) if n.headOption.exists(_.isLetter) => namePath(q).map(_ :+ n)
    case Parens(i) => namePath(i)
    case _ => None

  /** The functor that a program written alone stands for, with its parameters' names: a global meta
   *  constant of a Π type with explicit binders (written as a name or a path, not applied). */
  def generalisedFunctor(p: Tree): Option[(String, List[Name])] = p match
    case Parens(i) => generalisedFunctor(i)
    case Ident(n) if lookupGlobal(n).isDefined => functorParams(lookupGlobal(n).get).map(ps => (n, ps))
    case _ => None

  private def functorParams(id: Int): Option[List[Name]] =
    if globals(id).stage != Stage.S1 then None
    else
      val explicit = telescope(globals(id).ty)._1.takeWhile(_._2 == Icit.Expl).map(_._1)
      Option.when(explicit.nonEmpty && telescope(globals(id).ty)._1.forall(_._2 == Icit.Expl))(explicit)

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

  /** The generalised binders of a declaration's type `trees` (its type and its parameters' types), bound
   *  in `c`: the database `d` if a judgment has no `[e]`, and the parameters of each functor written alone
   *  before `⊢`, by the names of its declaration; parameters of the same name are one binder, if their
   *  types agree. Names in `bound` (the declaration's own parameters) and names in scope are not bound. */
  def generalisedBinders(trees: List[Tree], c: Cxt, bound: Set[Name]): (Cxt, List[(Name, Tm)]) =
    val judgments = trees.flatMap(t => TreeOps.nodes(t).collect { case j: Judgment => j })
    if judgments.isEmpty then (c, Nil)
    else
      var cx = c
      val out = mutable.ListBuffer.empty[(Name, Tm)]
      val ours = mutable.Map.empty[Name, Int]
      if judgments.exists(_.db.isEmpty) && !bound("d") && !cx.scope.contains("d") then
        semanticsGlobals.foreach { sem =>
          val dbTm = Tm.Global(sem("db"))
          cx = bind(cx, "d", eval(Nil, dbTm), Stage.S1)
          out += (("d", dbTm))
        }
      for j <- judgments do
        generalisedFunctor(j.program).foreach { (name, _) =>
          var ty = globals(lookupGlobal(name).get).ty
          var more = true
          while more do
            force(ty) match
              case Val.Pi(x, Icit.Expl, dom, cl) =>
                if x == "_" then fail(JudgmentProblem.CannotGeneralise(name, "_", "it has no name", j.program.span))
                val level =
                  if bound(x) then None
                  else
                    ours.get(x) match
                      case Some(l) =>
                        val agrees =
                          try { undoOnFailure(unify(cx.lvl, cx.binder(l).ty, dom)); true }
                          catch case _: UnifyError => false
                        if !agrees then
                          fail(
                            JudgmentProblem.CannotGeneralise(
                              name,
                              x,
                              s"another functor's parameter `$x` has the type `${show(cx, cx.binder(l).ty)}`, this one `${show(cx, dom)}`",
                              j.program.span
                            )
                          )
                        Some(l)
                      case None if cx.scope.contains(x) => Some(cx.scope(x))
                      case None =>
                        out += ((x, quote(cx.lvl, dom)))
                        cx = bind(cx, x, dom, Stage.S1)
                        ours(x) = cx.lvl - 1
                        Some(cx.lvl - 1)
                ty = inst(cl, level.map(Val.local).getOrElse(Val.Wild))
              case _ => more = false
        }
      (cx, out.toList)

  // ---------------------------------------------------------------- program data

  /** A rule of a program, as rule names need it: its position in the program's rules, its head relation
   *  and index among that relation's rules, its label, its variables' number and names, and which of its
   *  body literals are atoms (premises) rather than comparisons. */
  final case class RuleData(
      position: Int,
      head: Int,
      index: Int,
      label: Option[String],
      vars: Int,
      names: List[Name],
      body: List[Boolean],
      heads: Int
  )

  final case class ProgramData(relations: List[String], rules: List[RuleData], display: Option[ProgramDisplay], context: List[Name])

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
                    RuleData(pos, head.toInt, index.toInt, label, vars.length, names, isPos, heads.length)
                case _ => None
            })
            for
              rs <- relations
              ru <- rules
            yield ProgramData(rs, ru, display, display.map(_.context).getOrElse(Nil))
          case _ => None
      catch case _: Impossible => None
    }

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

  /** The relation of a goal atom `atom ρ vs`: `Left(i)` for `own i`, `Right(shown)` for another relation,
   *  `None` if it is not known. */
  private def goalRelation(sem: Map[Name, Int], a: Val, data: ProgramData): Option[Either[Int, String]] =
    forceData(a) match
      case Val.Rigid(Head.Glob(at), sp) if at == sem("atom") =>
        sp.reverse.collectFirst { case Elim.EApp(r, Icit.Expl) => forceData(r) } match
          case Some(Val.Rigid(Head.Glob(k), rsp)) =>
            val arg = rsp.collectFirst { case Elim.EApp(x, Icit.Expl) => forceData(x) }
            if k == sem("own") then arg.collect { case Val.Nat(_, n) => Left(n.toInt) }
            else if k == sem("arg") then
              arg.collect { case Val.Lit(hugin.syntax.Literal.StrL(l), _) =>
                Right(if data.context.length == 1 && !l.contains('.') then s"${data.context.head}.$l" else l)
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

  /** The rule a form names in the program, checked against the goal; `None` for a label the program does
   *  not have (the name is then elaborated as usual). */
  private def namedRule(sem: Map[Name, Int], form: RuleForm, data: ProgramData, goal: Val, shown: String, at: Span): Option[RuleData] =
    val programShown = data.display.flatMap(_.functor).getOrElse("the program")
    val rule = form match
      case RuleForm.Indexed(r, k) =>
        val i = data.relations.indexOf(r)
        if i < 0 then fail(JudgmentProblem.UnknownRule(shown, programShown, s"it has no relation `$r`", at))
        val ofR = data.rules.filter(_.head == i)
        Some(ofR.find(_.index == k).getOrElse {
          val why = if ofR.isEmpty then s"`$r` has no rules" else s"`$r` has ${ofR.length} rule(s), `$r.1` to `$r.${ofR.length}`"
          fail(JudgmentProblem.UnknownRule(shown, programShown, why, at))
        })
      case RuleForm.Label(l) => data.rules.find(_.label.contains(l))
      case RuleForm.Given => None
    rule.foreach { rd =>
      goalRelation(sem, goal, data).foreach {
        case Left(i) if i == rd.head =>
        case other =>
          val goalShown = other match
            case Left(i) => data.relations.lift(i).getOrElse(s"own $i")
            case Right(s) => s
          fail(JudgmentProblem.RuleHeadMismatch(shown, data.relations.lift(rd.head).getOrElse("?"), goalShown, at))
      }
    }
    rule

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
      derivationType(a) match
        case None => without
        case Some((p, _, goal)) =>
          val g = ruleGlobals(sem)
          form match
            case RuleForm.Given => Option.when(named.isEmpty)(checkGiven(c, sem, g, positional.head, p, goal, a, head.span))
            case _ =>
              programData(p) match
                case None => without
                case Some(data) =>
                  namedRule(sem, form, data, goal, shown, head.span).map(rule =>
                    checkRule(c, g, rule, shown, head, named.collect { case n: NamedArg => n }, positional, a)
                  )
    }

  /** `fire` at the rule, its premises checked in body order (comparisons proved by evaluation). */
  private def checkRule(
      c: Cxt,
      g: RuleGlobals,
      rule: RuleData,
      shown: String,
      head: Tree,
      named: List[NamedArg],
      premises: List[Tree],
      expected: Val
  ): Tm =
    val sp = head.span
    val premiseCount = rule.body.count(identity)
    if premises.length != premiseCount then
      fail(JudgmentProblem.PremiseCount(
        shown,
        premiseCount,
        premises.length,
        Span(sp.origin, sp.from, premises.lastOption.map(_.span.until).getOrElse(sp.until))
      ))
    for n <- named if !rule.names.contains(n.name) do
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
    val supplied = (0 until rule.vars).map(i => rule.names.lift(i).flatMap(x => named.find(_.name == x)).map(_.value)).toList
    unifyAt(c, sp, xsMeta, ev(c, ruleEnv(c, g, xsDom, supplied, shown, rule.names, sp)))
    val psMeta = freshMeta(c, fireArgs.dom(List(m)), Stage.S1, sp, s"the premises of `$shown`")
    val h = check(c, ref(g.here), fireArgs.dom(List(m, psMeta)), Stage.S1)
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
      goalRelation(sem, goal, data).map(_.fold(i => data.relations.lift(i).getOrElse(s"own $i"), identity))
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
        derivationType(ty) match
          case Some((p, _, goal)) => rulePatternIn(t, form, p, goal)
          case None =>
            form match
              case RuleForm.Indexed(_, _) => fail(JudgmentProblem.RuleNameWithoutJudgment(ruleShown(head), head.span))
              case _ => None
      }

  private def rulePatternIn(t: Tree, form: RuleForm, p: Val, goal: Val): Option[Pat] =
    val sem = semanticsGlobals.get
    val g = ruleGlobals(sem)
    val (head, args) = TreeOps.flattenApp(t)
    val named = args.collect { case n: NamedArg => n }
    val positional = args.filterNot(_.isInstanceOf[NamedArg])
    val sp = t.span
    val shown = ruleShown(head)
    // a premise: a rule name of the same program, or any pattern
    def premise(e: Tree): Pat =
      val (h, as) = TreeOps.flattenApp(e)
      ruleForm(Cxt.empty, h, as.count(!_.isInstanceOf[NamedArg])).flatMap(f => rulePatternIn(e, f, p, Val.Wild)).getOrElse(pattern(e, None))
    form match
      case RuleForm.Given =>
        if named.nonEmpty then None
        else Some(Pat.PCon(g.givenC, List(Pat.PWild(sp), premise(positional.head)), sp))
      case _ =>
        val data = programData(p) match
          case Some(d) => d
          case None =>
            form match
              case RuleForm.Indexed(_, _) => fail(JudgmentProblem.RuleNameWithoutJudgment(shown, head.span))
              case _ => ProgramData(Nil, Nil, None, Nil)
        namedRule(sem, form, data, goal, shown, head.span).map { rule =>
          val premiseCount = rule.body.count(identity)
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
          def prems(lits: List[Boolean]): Pat = lits match
            case Nil => Pat.PCon(g.pnil, Nil, sp)
            case true :: more =>
              val e = premise(rest.head)
              rest = rest.tail
              Pat.PCon(g.ppos, List(Pat.PCon(g.refl, Nil, sp), e, prems(more)), sp)
            case false :: more => Pat.PCon(g.pcmp, List(Pat.PWild(sp), prems(more)), sp)
          Pat.PCon(g.fire, List(member, prems(rule.body), Pat.PCon(g.here, Nil, sp)), sp, List("xs" -> env))
        }

  // ---------------------------------------------------------------- coverage

  /** Below a derivation `given …` or `fire …` of a program whose rules are known, the positions (relative,
   *  the last step first) of `fire`'s rule and head proofs and of their `there` chains, as long as the
   *  program's rules and heads: with them in Π, coverage splits a derivation into the program's rules, and
   *  refutes those whose head does not match the goal (reference: meta/coverage, "Derivations"). */
  def derivationPositions(ctor: Int, sp: Spine): Option[List[List[Int]]] =
    semanticsGlobals.filter(sem => ctor == sem("given") || ctor == sem("fire")).flatMap { _ =>
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
    derivationType(ty).flatMap { (p, _, goal) =>
      val sem = semanticsGlobals.get
      programData(p).map { data =>
        val rel = goalRelation(sem, goal, data)
        val rules = data.rules.filter(r => rel.forall(_ == Left(r.head)))
        val premiseNames = premiseInitials(p, sem, data)
        val ruleCases = rules.map { r =>
          val name = r.label.getOrElse(s"${data.relations.lift(r.head).getOrElse("?")}.${r.index}")
          val fresh = FreshNames(taken)
          val ps = premiseNames.lift(r.position).getOrElse(Nil).map(fresh(_))
          if ps.isEmpty then name else (name :: ps).mkString("(", " ", ")")
        }
        val input = forceData(app(proj(forceData(p), "input"), goalRef(sem, goal), Icit.Expl)) match
          case Val.Rigid(Head.Glob(id), Nil) => globals(id).name != "false"
          case _ => true
        if input then ruleCases :+ s"(given ${FreshNames(taken)("I")})" else ruleCases
      }
    }

  private def goalRef(sem: Map[Name, Int], goal: Val): Val = forceData(goal) match
    case Val.Rigid(Head.Glob(_), sp) => sp.reverse.collectFirst { case Elim.EApp(r, Icit.Expl) => r }.getOrElse(Val.Wild)
    case _ => Val.Wild

  /** For each rule, the names of its premises: the initial of the premise's relation, capitalised (`E`
   *  for `g.edge`, `P` for `path`). */
  private def premiseInitials(p: Val, sem: Map[Name, Int], data: ProgramData): List[List[String]] =
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
          case _ => Nil
      }
    }
