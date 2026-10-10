package hugin.core

/** The strict evaluation of applications as a machine with an explicit continuation stack (issue #129).
 *
 *  A meta function recursing over a list (`mirror (I :: Rest) = I :: mirror Rest`) nests one call per
 *  element: evaluating the body evaluates the recursive call in argument position, which runs the case
 *  tree and evaluates the body again. As native recursion (`eval` -> `app` -> `reduceFunction` ->
 *  `runTree` -> `eval`, ~17 JVM frames per element) that overflowed a 1 MiB stack from a few hundred
 *  elements, at a depth that varied with the JIT. Here the steps that recur per element are a loop, and
 *  what remains to be done after a value (apply it, evaluate the argument, memoise it) is a [[Frame]] on
 *  the heap: application (`Tm.App`), `let`, the body of a λ applied, a function defined by clauses run by
 *  its case tree ([[Matching.matchFunction]]), and a folded definition applied ([[Val.Top]]). Every other
 *  term is a step of [[Evaluation.evalNode]], whose recursion is bounded by the size of the term, not by
 *  the depth of a computation.
 *
 *  The order of evaluation, and so the order of effects (fresh object variables, observed staging), is
 *  that of the recursive evaluator: the function, then the argument, then the application; the result of
 *  a function is memoised before the arguments beyond its arity are applied. */
trait Machine:
  self: Core =>
  import Val.*
  import Machine.*

  /** The value of `t` in `env`. */
  def eval(env: List[Val], t: Tm): Val = t match
    case _: Tm.App | _: Tm.Let => run(env, t, null, null, null, null)
    case _ => evalNode(env, t)

  /** `f` applied to `a`. */
  def app(f: Val, a: Val, i: Icit): Val = run(Nil, null, f, a, i, null)

  /** The body of a function defined by clauses, matched by its case tree, evaluated and memoised. */
  protected def evalReduct(r: Reduct): Val = run(Nil, null, null, null, null, r)

  /** A term that evaluates without effects and without evaluating a subterm. */
  private def atomic(t: Tm): Boolean = t match
    case _: Tm.Var | _: Tm.Global | _: Tm.Meta | _: Tm.Lam | _: Tm.Lit => true
    case _ => false

  /** Starts by evaluating `t0` in `env0` (`t0` not null), by applying `f0` to `a0` (`f0` not null), or by
   *  evaluating the body of `r0`. */
  private def run(env0: List[Val], t0: Tm | Null, f0: Val | Null, a0: Val | Null, i0: Icit | Null, r0: Reduct | Null): Val =
    var k: Frame | Null = null
    var env = env0
    var t: Tm = t0.asInstanceOf[Tm]
    var f: Val = f0.asInstanceOf[Val]
    var a: Val = a0.asInstanceOf[Val]
    var i: Icit = i0.asInstanceOf[Icit]
    var v: Val = null.asInstanceOf[Val]
    var mode = if t0 != null then Eval else Apply
    if r0 != null then
      // a memo hit is not a reduct to evaluate ([[Matching.reduceFunction]] handles it)
      k = r0.frames(null)
      env = r0.env
      t = r0.body
      mode = Eval
    while mode != Done do
      mode match
        case Eval =>
          t match
            case Tm.App(fn, arg, ic) =>
              if atomic(fn) then
                val fv = evalNode(env, fn)
                if atomic(arg) then
                  f = fv
                  a = evalNode(env, arg)
                  i = ic
                  mode = Apply
                else
                  k = KApp(fv, ic, k)
                  t = arg
              else
                k = KArg(env, arg, ic, k)
                t = fn
            case Tm.Let(_, _, d, b) =>
              k = KLet(env, b, k)
              t = d
            case _ =>
              v = evalNode(env, t)
              mode = Return
        case Apply =>
          f match
            case Lam(_, _, cl) =>
              env = a :: cl.env
              t = cl.body
              mode = Eval
            case Obj(ObjForm.Loc(_), List(g)) => f = g
            case Rigid(h @ Head.Glob(id), sp) =>
              val sp1 = Elim.EApp(a, i) :: sp
              matchFunction(id, sp1) match
                case r: Reduct =>
                  k = r.frames(k)
                  if r.hit != null then
                    v = r.hit.nn
                    mode = Return
                  else
                    env = r.env
                    t = r.body
                    mode = Eval
                case Matching.NotClauses =>
                  v = reduceFunction(id, sp1).getOrElse(Rigid(h, sp1))
                  mode = Return
                case Matching.Stuck =>
                  v = Rigid(h, sp1)
                  mode = Return
            case Rigid(h, sp) =>
              v = Rigid(h, Elim.EApp(a, i) :: sp)
              mode = Return
            case Flex(m, sp) =>
              v = Flex(m, Elim.EApp(a, i) :: sp)
              mode = Return
            case Top(id, sp, u) =>
              k = KTop(id, Elim.EApp(a, i) :: sp, k)
              f = u.value
            case other => throw Impossible(s"application of a non-function value $other")
        case _ =>
          if k == null then mode = Done
          else
            val fr = k.nn
            k = fr.next
            fr match
              case KArg(e, arg, ic, _) =>
                if atomic(arg) then
                  f = v
                  a = evalNode(e, arg)
                  i = ic
                  mode = Apply
                else
                  k = KApp(v, ic, k)
                  env = e
                  t = arg
                  mode = Eval
              case KApp(fv, ic, _) =>
                f = fv
                a = v
                i = ic
                mode = Apply
              case KLet(e, b, _) =>
                env = v :: e
                t = b
                mode = Eval
              case KMemo(key, _) => memoise(key, v)
              case KElim(Elim.EApp(x, ic), _) =>
                f = v
                a = x
                i = ic
                mode = Apply
              case KElim(e, _) => v = elim(v, e)
              case KTop(id, sp, _) => v = Top(id, sp, Unfold(v))
    v

object Machine:
  private inline val Eval = 0
  private inline val Apply = 1
  private inline val Return = 2
  private inline val Done = 3

  /** What remains to be done with a value: a continuation, as a linked stack. */
  sealed abstract class Frame(val next: Frame | Null)

  /** Evaluate the argument `arg` in `env`, then apply the value (the function) to it. */
  final case class KArg(env: List[Val], arg: Tm, i: Icit, override val next: Frame | Null) extends Frame(next)

  /** Apply `f` to the value. */
  final case class KApp(f: Val, i: Icit, override val next: Frame | Null) extends Frame(next)

  /** Evaluate `body` in `env` extended with the value. */
  final case class KLet(env: List[Val], body: Tm, override val next: Frame | Null) extends Frame(next)

  /** Memoise the value of a function's application under `key`. */
  final case class KMemo(key: (Int, List[Int]), override val next: Frame | Null) extends Frame(next)

  /** Apply the elimination to the value (an argument beyond a function's arity). */
  final case class KElim(e: Elim, override val next: Frame | Null) extends Frame(next)

  /** Fold the value as the unfolding of the definition `id` applied to `sp`. */
  final case class KTop(id: Int, sp: Spine, override val next: Frame | Null) extends Frame(next)

  /** `later` (a spine, innermost first) as frames on `k`: the outermost elimination is applied first. */
  private[core] def elimFrames(later: Spine, k: Frame | Null): Frame | Null =
    var r = k
    var l = later
    while l.nonEmpty do
      r = KElim(l.head, r)
      l = l.tail
    r
