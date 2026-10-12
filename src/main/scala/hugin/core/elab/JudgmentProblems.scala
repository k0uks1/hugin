package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of the judgment notation `P ⊢[e] r t̄` and of rule names (reference: std/semantics, "The
 *  judgment notation", "Rule names"): the atom of a judgment (E0945), a functor written alone (E0946),
 *  the database (E0947), a rule name (E0948), `given` (E0949) and a program with negation or
 *  aggregates (E0961). Terms are given as shown to users. */
enum JudgmentProblem extends Problem:
  /** A judgment in a program that does not load `std/semantics`. */
  case NoLibrary(at: Span)

  /** The atom's relation `rel` is not a relation of the program, of its parameters or of the file. */
  case UnknownRelation(rel: String, program: String, at: Span)

  /** The atom is not a relation applied to arguments. */
  case NotAnAtom(shown: String, at: Span)

  /** The relation `rel` has `expected` columns and is applied to `found` arguments. */
  case AtomArity(rel: String, expected: Int, found: Int, at: Span)

  /** The type of an argument of `rel` cannot be inferred (a program value, whose relations have no types). */
  case UntypedArgument(rel: String, at: Span)

  /** The functor `functor` written alone before `⊢`; `applied` is it applied to variables named after its
   *  parameters, as the help shows it. */
  case FunctorAlone(functor: String, applied: String, at: Span)

  /** A judgment without `[e]` outside the type of a declaration whose database unification did not
   *  determine. */
  case NoDatabase(at: Span)

  /** A rule name used where no derivation of a known program is expected. */
  case RuleNameWithoutJudgment(name: String, at: Span)

  /** A rule name that names no rule of the program (`count` rules of its relation, `known` relations). */
  case UnknownRule(name: String, program: String, why: String, at: Span)

  /** The rule `name` derives facts of `derives`, but the goal is a fact of `goal`. */
  case RuleHeadMismatch(name: String, derives: String, goal: String, at: Span)

  /** The rule `name` has `expected` premises (atoms of its body), and `found` are given. */
  case PremiseCount(name: String, expected: Int, found: Int, at: Span)

  /** `{x := e}` for a rule `name` without a variable `x` (its variables `vars`). */
  case NoRuleVariable(name: String, x: String, vars: List[String], at: Span)

  /** A comparison `cmp` of the rule `name`'s body that does not evaluate to true. */
  case ComparisonUndecided(name: String, cmp: String, at: Span)

  /** `given` for the relation `rel`, which is not an input of the program (it has rules), or whose input test
   *  does not evaluate (`decided` false). */
  case NotAnInput(rel: String, decided: Boolean, at: Span)

  /** A judgment over the program `program`, a rule of which (with a head of `rel`, if known) has a negation
   *  or (`aggregate`) an aggregate: the notation reads programs in the positive `derives` (#186 P9a). */
  case NotPositive(program: String, rel: Option[String], aggregate: Boolean, at: Span)

  def code: Code = this match
    case _: NoLibrary | _: UnknownRelation | _: NotAnAtom | _: AtomArity | _: UntypedArgument => Code.E0945
    case _: FunctorAlone => Code.E0946
    case _: NoDatabase => Code.E0947
    case _: RuleNameWithoutJudgment | _: UnknownRule | _: RuleHeadMismatch | _: PremiseCount | _: NoRuleVariable | _: ComparisonUndecided =>
      Code.E0948
    case _: NotAnInput => Code.E0949
    case _: NotPositive => Code.E0961

  def primary: Span = this match
    case NoLibrary(s) => s
    case UnknownRelation(_, _, s) => s
    case NotAnAtom(_, s) => s
    case AtomArity(_, _, _, s) => s
    case UntypedArgument(_, s) => s
    case FunctorAlone(_, _, s) => s
    case NoDatabase(s) => s
    case RuleNameWithoutJudgment(_, s) => s
    case UnknownRule(_, _, _, s) => s
    case RuleHeadMismatch(_, _, _, s) => s
    case PremiseCount(_, _, _, s) => s
    case NoRuleVariable(_, _, _, s) => s
    case ComparisonUndecided(_, _, s) => s
    case NotAnInput(_, _, s) => s
    case NotPositive(_, _, _, s) => s

  def message: Msg = this match
    case _: NoLibrary => msg"the judgment `⊢` needs the library `std/semantics`"
    case UnknownRelation(r, p, _) => msg"${Src(r)} is not a relation of ${Src(p)}"
    case NotAnAtom(t, _) => msg"${Src(t)} is not an atom: a relation applied to arguments"
    case AtomArity(r, e, f, _) => msg"${Src(r)} has $e column(s), but the atom gives $f argument(s)"
    case UntypedArgument(r, _) => msg"cannot infer the object type of this argument of ${Src(r)}"
    case FunctorAlone(f, _, _) => msg"the functor ${Src(f)} is written alone before `⊢`, without its arguments"
    case _: NoDatabase => msg"cannot determine the database of this judgment"
    case RuleNameWithoutJudgment(n, _) => msg"the rule name ${Src(n)} is used where no derivation of a known program is expected"
    case UnknownRule(n, p, why, _) => msg"${Src(n)} is not a rule of ${Src(p)}: " ++ Msg.text(why)
    case RuleHeadMismatch(n, d, g, _) => msg"the rule ${Src(n)} derives facts of ${Src(d)}, but the goal is a fact of ${Src(g)}"
    case PremiseCount(n, e, f, _) => msg"the rule ${Src(n)} has $e premise(s), but $f are given"
    case NoRuleVariable(n, x, _, _) => msg"the rule ${Src(n)} has no variable ${Src(x)}"
    case ComparisonUndecided(n, cmp, _) => msg"cannot prove a comparison of the rule ${Src(n)} by evaluation: ${Src(cmp)}"
    case NotAnInput(r, true, _) => msg"${Src(r)} is not an input of the program: it has rules, so `given` cannot derive its facts"
    case NotAnInput(r, false, _) => msg"cannot decide whether ${Src(r)} is an input of the program"
    case _: NotPositive => msg"the judgment notation covers programs without negation and aggregates; use `nderives` of `std/strata`"

  override def primaryLabel: Msg = this match
    case _: NoLibrary => msg"judgment here"
    case _: UnknownRelation => msg"unknown relation"
    case _: NotAnAtom => msg"expected an atom"
    case _: AtomArity => msg"wrong number of arguments"
    case _: UntypedArgument => msg"type unknown"
    case _: FunctorAlone => msg"a functor, not a program"
    case _: NoDatabase => msg"which database?"
    case _: RuleNameWithoutJudgment => msg"no derivation expected here"
    case _: UnknownRule => msg"unknown rule"
    case _: RuleHeadMismatch => msg"the rule's head does not match the goal"
    case _: PremiseCount => msg"wrong number of premises"
    case _: NoRuleVariable => msg"unknown variable"
    case _: ComparisonUndecided => msg"comparison not proved"
    case _: NotAnInput => msg"not an input"
    case NotPositive(_, _, false, _) => msg"a program with a negation"
    case NotPositive(_, _, true, _) => msg"a program with an aggregate"

  override def notes: List[Msg] = this match
    case _: NoLibrary => List(msg"`P ⊢[d] r t̄` stands for `derives (programOf P) d (atom ρ [v t̄])` of `std/semantics`")
    case _: UnknownRelation =>
      List(
        msg"the atom of `P ⊢ r t̄` names a relation of `P`'s body, of a parameter through the functor's argument (`G.edge` in `tc G ⊢ …`) or of the file, as the body's rules do"
      )
    case _: UntypedArgument => List(msg"a program given as a value has no column types; write the argument as code of a known type")
    case _: FunctorAlone =>
      List(
        msg"the program of a judgment is a functor applied to arguments, a module or a program value; no parameter of a functor is bound by its name",
        msg"in the type of a declaration, a free uppercase variable as the argument (`G`) is bound as an implicit argument, as any other"
      )
    case _: NoDatabase =>
      List(
        msg"outside the type of a declaration, a judgment without `[e]` has an unknown database, which the expected type must determine",
        msg"in the type of a declaration, the judgments without `[e]` share the declaration's anonymous database"
      )
    case _: RuleNameWithoutJudgment =>
      List(msg"a rule name `r.k` is a derivation of a judgment `P ⊢ r t̄`, so its expected type must be one, with `P` a module body")
    case UnknownRule(_, _, _, _) =>
      List(msg"the rules of a relation `r` are `r.1`, `r.2`, … in the order of the program; a label `@n` adds the name `n`")
    case NoRuleVariable(_, _, vs, _) =>
      if vs.isEmpty then List(msg"the rule's variables are not known by name")
      else List(Msg.text("the rule's variables: ") ++ Msg.join(vs.map(v => msg"${Src(v)}"), ", "))
    case _: ComparisonUndecided =>
      List(
        msg"in an expression, a rule name proves its comparisons by evaluating them; one with unknown values needs `fire` and `pcmp` written out"
      )
    case NotAnInput(_, true, _) =>
      List(msg"`given` derives the facts of an input relation: one without rules, of a parameter, or outside the program")
    case NotPositive(p, rel, aggregate, _) =>
      val what = if aggregate then "an aggregate" else "a negation"
      val rule = rel.fold(msg"a rule of ${Src(p)}")(r => msg"a rule of ${Src(r)} in ${Src(p)}")
      List(
        rule ++ Msg.text(s" has $what in its body"),
        msg"`P ⊢ r t̄` is `derives`, the positive fragment, in which such a rule never fires: a judgment over this program could contradict its run"
      )
    case _ => Nil

  override def helps: List[Msg] = this match
    case _: NoLibrary => List(msg"add ${Src("%use \"std/semantics\".")} to the file")
    case FunctorAlone(_, applied, _) => List(msg"apply the functor to its arguments: write ${Src(s"$applied ⊢ …")}")
    case _: NoDatabase => List(msg"give the database: ${Src("P ⊢[e] r t̄")}, with a database `e` in scope")
    case _: NotPositive =>
      List(
        msg"state it with ${Src("nderives")} or ${Src("perfect")} of `std/strata`, which read negations and aggregates stratum by stratum"
      )
    case _ => Nil
