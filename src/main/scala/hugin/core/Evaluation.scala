package hugin.core

import hugin.obj.{BaseType, Prims}
import hugin.syntax.Literal

/** Normalisation by evaluation: `eval` into values with closures, `quote` (read-back) into normal forms.
 *  Meta-level computation happens here; object code (stage 0) is inert data, except that splices of
 *  quotes cancel (`$⟨t⟩ = t`), which is what makes evaluation of a closed program its staging. */
trait Evaluation:
  self: Core =>
  import Val.*

  final class Impossible(msg: String) extends Exception(msg)

  /** Observes the staging of code at positions while the handover stages items (for tooling). */
  var observer: StagingObserver | Null = null

  def eval(env: List[Val], t: Tm): Val = t match
    case Tm.Obj(ObjForm.Loc(sp), List(inner)) if observer != null => observed(env, sp, inner)
    case Tm.Quote(t @ Tm.Obj(ObjForm.Loc(sp), _)) if observer != null =>
      val v = eval(env, t)
      observer.nn.quoted(sp, v)
      vQuote(v)
    case Tm.Var(ix) => env(ix)
    case Tm.Global(id) => globalValue(id)
    case Tm.Meta(m) => metaValue(m)
    case Tm.AppPruning(t, pr) => appPruning(env, eval(env, t), pr)
    case Tm.Lam(x, i, b) => Lam(x, i, Closure(env, b))
    case Tm.App(f, a, i) => app(eval(env, f), eval(env, a), i)
    case Tm.Pi(x, i, a, b) => Pi(x, i, eval(env, a), Closure(env, b))
    case Tm.Let(_, _, d, b) => eval(eval(env, d) :: env, b)
    case Tm.U0 => U0
    case Tm.U1(l) => U1(l)
    case Tm.Lift(a) => Lift(eval(env, a))
    case Tm.Quote(t) => vQuote(eval(env, t))
    case Tm.Splice(t) => vSplice(eval(env, t))
    case Tm.RecTy(fs, rs, ds) => RecTy(fs.map(_._1), env, fs.map(_._2), rs, ds)
    case Tm.Require(rs, use, t) => required(rs, use, eval(env, t))
    case Tm.Trace(frame, t) => traced(frame)(eval(env, t))
    case Tm.Rec(fs) => Rec(fs.map((l, t) => (l, eval(env, t))))
    case Tm.Proj(t, l) => proj(eval(env, t), l)
    case Tm.Lit(l, st) => Lit(l, st)
    case Tm.Base(b, st) => Base(b, st)
    case Tm.RelT => RelT
    case Tm.PropT => PropT
    case Tm.Arith(op, a, b, st) => arith(op, eval(env, a), eval(env, b), st)
    case Tm.Negate(a, st) => negate(eval(env, a), st)
    case Tm.Obj(f, as) => Obj(f, as.map(eval(env, _)))
    case Tm.Fresh(ns, b) => eval(ns.reverse.map(freshObjectVariable) ++ env, b)
    case Tm.Module(b, menv) => evalModule(b, menv.map(eval(env, _)))
    case Tm.Persist(t) => persist(eval(env, t))
    case Tm.FactTy(r) => FactTy(eval(env, r))

  /** Object code at the position `sp`, a splice or a persisted value, observed. */
  private def observed(env: List[Val], sp: hugin.util.Span, inner: Tm): Val =
    val v = inner match
      case Tm.Splice(m) =>
        val code = vSplice(eval(env, m))
        if !isFamilyConstant(m) then observer.nn.spliced(sp, code)
        code
      case Tm.Persist(m) =>
        val x = eval(env, m)
        observer.nn.persisted(sp, x)
        persist(x)
      case other => eval(env, other)
    Obj(ObjForm.Loc(sp), List(v))

  /** A family's constant with its implicit arguments (`nil` for `nil[int]`): its splice is no staging a
   *  user wrote. */
  private def isFamilyConstant(t: Tm): Boolean = t match
    case Tm.App(f, _, Icit.Impl) => isFamilyConstant(f)
    case Tm.Global(id) => globals(id).kind.isInstanceOf[GlobalKind.Family]
    case _ => false

  private var hygiene = 0

  protected def copyEvaluation(from: Evaluation): Unit = hygiene = from.hygiene

  /** A fresh object variable named after `x` (`X#k`). */
  def freshObjectVariable(x: Name): Val =
    hygiene += 1
    Obj(ObjForm.Named(s"$x#$hygiene"), Nil)

  def globalValue(id: Int): Val = globals(id).kind match
    case GlobalKind.Definition(_, v) => v
    case _ => Rigid(Head.Glob(id), Nil)

  def metaValue(m: Int): Val = metas(m).solution.getOrElse(Flex(m, Nil))

  def inst(cl: Closure, v: Val): Val = eval(v :: cl.env, cl.body)

  /** `t` applied to the variables of `env` selected by the pruning. */
  def appPruning(env: List[Val], v: Val, pr: Pruning): Val = (env, pr) match
    case (Nil, Nil) => v
    case (e :: env1, Some(i) :: pr1) => app(appPruning(env1, v, pr1), e, i)
    case (_ :: env1, None :: pr1) => appPruning(env1, v, pr1)
    case _ => throw Impossible("pruning does not match the environment")

  def app(f: Val, a: Val, i: Icit): Val = f match
    case Lam(_, _, cl) => inst(cl, a)
    case Obj(ObjForm.Loc(_), List(g)) => app(g, a, i)
    case Rigid(h, sp) => rigid(h, Elim.EApp(a, i) :: sp)
    case Flex(m, sp) => Flex(m, Elim.EApp(a, i) :: sp)
    case other => throw Impossible(s"application of a non-function value $other")

  /** A neutral value; a function applied to enough arguments reduces ([[Matching]]). */
  private def rigid(h: Head, sp: Spine): Val = h match
    case Head.Glob(id) => reduceFunction(id, sp).getOrElse(Rigid(h, sp))
    case _ => Rigid(h, sp)

  /** `⟨$t⟩ = t`, also for a splice at a position (the code spliced has positions of its own). */
  def vQuote(v: Val): Val = Val.unloc(v) match
    case Rigid(h, Elim.ESplice :: sp) => Rigid(h, sp)
    case Flex(m, Elim.ESplice :: sp) => Flex(m, sp)
    case _ => Quote(v)

  def vSplice(v: Val): Val = v match
    case Quote(t) => t
    case Rigid(h, sp) => Rigid(h, Elim.ESplice :: sp)
    case Flex(m, sp) => Flex(m, Elim.ESplice :: sp)
    case other => throw Impossible(s"splice of $other")

  def proj(v: Val, l: Name): Val = v match
    case Rec(fs) => fs.find(_._1 == l).map(_._2).getOrElse(throw Impossible(s"no field $l"))
    case Rigid(h, sp) => Rigid(h, Elim.EProj(l) :: sp)
    case Flex(m, sp) => Flex(m, Elim.EProj(l) :: sp)
    case other => throw Impossible(s"projection .$l of $other")

  def arith(op: hugin.obj.ArithOp, a: Val, b: Val, st: Stage): Val = (a, b, st) match
    case (Lit(x, Stage.S1), Lit(y, Stage.S1), Stage.S1) =>
      Prims.arith(op, x, y).map(Lit(_, Stage.S1)).getOrElse(Arith(op, a, b, st))
    case _ => Arith(op, a, b, st)

  def negate(a: Val, st: Stage): Val = (a, st) match
    case (Lit(x, Stage.S1), Stage.S1) => Prims.neg(x).map(Lit(_, Stage.S1)).getOrElse(Negate(a, st))
    case _ => Negate(a, st)

  def persist(v: Val): Val = v match
    case Lit(l, Stage.S1) => Lit(l, Stage.S0)
    case t => Persist(t)

  def elim(v: Val, e: Elim): Val = e match
    case Elim.EApp(a, i) => app(v, a, i)
    case Elim.ESplice => vSplice(v)
    case Elim.EProj(l) => proj(v, l)

  def appSp(v: Val, sp: Spine): Val = sp.reverse.foldLeft(v)(elim)

  /** Unfolds solved metas at the head, and re-tries stuck function applications (an argument may have
   *  become a constructor application since, through a meta solution or a newly elaborated function). */
  def force(v: Val): Val = v match
    case Flex(m, sp) =>
      metas(m).solution match
        case Some(s) => force(appSp(s, sp))
        case None => v
    case Rigid(Head.Glob(id), sp) =>
      globals(id).kind match
        // a global defined after the value was computed (a formula function defined by its clauses)
        case GlobalKind.Definition(_, d) => force(appSp(d, sp))
        case _ => reduceFunction(id, sp).map(force).getOrElse(v)
    case Rigid(Head.Module(b, env), sp) if closedEnv(env).isDefined => force(appSp(evalModule(b, env), sp))
    // compile-time arithmetic stuck on an application that may reduce now
    case Arith(op, a, b, Stage.S1) => arith(op, force(a), force(b), Stage.S1)
    case Negate(a, Stage.S1) => negate(force(a), Stage.S1)
    case Persist(t) => persist(force(t))
    case other => other

  // ------------------------------------------------------------------ records

  /** The field types of a record type, each instantiated with the given values of the earlier fields. */
  def fieldTypes(rt: RecTy, values: Name => Val): List[(Name, Val)] =
    var e = rt.env
    rt.labels.zip(rt.tys).map { (lb, ty) =>
      val v = eval(e, ty)
      e = values(lb) :: e
      (lb, v)
    }

  /** The type of field `lb` of `r : rt`. */
  def fieldType(rt: RecTy, r: Val, lb: Name): Option[Val] =
    fieldTypes(rt, l => proj(r, l)).find(_._1 == lb).map(_._2)

  def isMetaPrim(v: Val): Option[BaseType] = force(v) match
    case Base(b, Stage.S1) => Some(b)
    case _ => None

  def literalOf(v: Val): Option[Literal] = force(v) match
    case Lit(l, _) => Some(l)
    case _ => None
