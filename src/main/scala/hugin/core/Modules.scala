package hugin.core

import hugin.util.Span
import scala.collection.mutable

/** A member of a module body: an object constant, created fresh for each instance of the body, or a meta
 *  definition. `ty` is the type of the member as a field of the module (`⇑τ` for an object constant),
 *  in the context of the body's environment and the members before it. */
final case class Member(name: Name, kind: MemberKind, ty: Tm, span: Span, declSpan: Span)

enum MemberKind:
  case Object(decl: ObjDecl)
  case Defined(value: Tm)

/** A module body `{ items }` (REDESIGN §6.7): its members (a telescope, whose types and definitions see
 *  the body's environment and the members before them) and its object items (rules, queries,
 *  directives, edges, in the context of the environment, the members and their own variables). */
final case class ModuleBody(id: Int, span: Span, members: List[Member], items: List[CoreItem])

/** An instance of a module body: its environment, with the members' values innermost, and the prefix of
 *  the names of its object constants. */
final case class ModuleInstance(body: ModuleBody, env: List[Val], prefix: String, position: Int, origin: hugin.util.Origin)

/** Module bodies are **generative** (REDESIGN §6.7): evaluating a body creates fresh object constants for
 *  its object members, and its object items are staged for them ([[handover.Handover]]). To give each
 *  evaluation in the source one instance although normalisation by evaluation may evaluate a term
 *  several times, instances are memoised per body, closed environment and *site*, the top-level item
 *  whose elaboration or staging evaluates it: within an item a body applied to the same arguments is one
 *  instance, in different items they are different instances (`a = tc g.  b = tc g.` are two). A body in
 *  an environment that is not closed (under a binder) is not instantiated: its value is neutral.
 *
 *  The object constants of an instance are named after the definition that evaluates it (`hops.r` for
 *  `hops = lib.reach …`), as the old meta evaluator named them; anonymous instances are `_m1`, `_m2`, …. */
trait Modules:
  self: Core =>

  private var bodyIds = 0
  def nextBodyId(): Int =
    bodyIds += 1
    bodyIds

  /** The item whose elaboration or staging evaluates terms now (see above), and its position: an
   *  instance's object constants and items are placed there in the object program. */
  var site: Int = 0
  var position: Int = 0

  /** The name of the definition being elaborated or staged, the prefix of the instances it creates. */
  var hint: String = ""

  private val memo = mutable.HashMap.empty[(Int, Int, List[Tm]), Val]
  private val prefixes = mutable.HashSet.empty[String]
  private var anonymous = 0
  val moduleInstances: mutable.ListBuffer[ModuleInstance] = mutable.ListBuffer.empty

  /** Reserves a prefix (the qualifier of a file's object constants). */
  def reservePrefix(p: String): Unit = prefixes += p

  def evalModule(body: ModuleBody, env: List[Val]): Val = closedEnv(env) match
    case None => Val.Rigid(Head.Module(body, env), Nil)
    case Some(key) => memo.getOrElseUpdate((body.id, site, key.map(stripPositions)), instantiate(body, env))

  /** The normal forms of an environment's values if they have no free variables and no unknowns
   *  (functions, such as formula functions passed to a functor, are fine). */
  def closedEnv(env: List[Val]): Option[List[Tm]] =
    val tms = env.map(quote(0, _))
    Option.when(tms.forall(noFreeVariables(_, 0)))(tms)

  private def noFreeVariables(t: Tm, depth: Int): Boolean = t match
    case Tm.Var(ix) => ix >= 0 && ix < depth // read back at level 0, a free variable has a negative index
    case Tm.Meta(_) | Tm.AppPruning(_, _) => false
    case Tm.Lam(_, _, b) => noFreeVariables(b, depth + 1)
    case Tm.Pi(_, _, a, b) => noFreeVariables(a, depth) && noFreeVariables(b, depth + 1)
    case Tm.Let(_, a, d, b) => noFreeVariables(a, depth) && noFreeVariables(d, depth) && noFreeVariables(b, depth + 1)
    case Tm.RecTy(fs, _, _) => fs.zipWithIndex.forall((f, k) => noFreeVariables(f._2, depth + k))
    case Tm.Fresh(ns, b) => noFreeVariables(b, depth + ns.length)
    case other => Tm.children(other).forall(noFreeVariables(_, depth))

  private def instantiate(body: ModuleBody, env: List[Val]): Val =
    val prefix = freshPrefix()
    var e = env
    val fields = body.members.map { m =>
      val v = m.kind match
        case MemberKind.Object(decl) => objectMember(m, decl, e, prefix)
        case MemberKind.Defined(t) => eval(e, t)
      e = v :: e
      (m.name, v)
    }
    moduleInstances += ModuleInstance(body, e, prefix, position, origin)
    Val.Rec(fields)

  private def objectMember(m: Member, decl: ObjDecl, env: List[Val], prefix: String): Val =
    val ty = force(eval(env, m.ty)) match
      case Val.Lift(t) => t
      case other => throw Impossible(s"object member of type $other")
    val tyTm = quote(0, ty)
    val name = if prefix.isEmpty then m.name else s"$prefix.${m.name}"
    val id = addGlobal(GlobalEntry(name, eval(Nil, tyTm), tyTm, Stage.S0, GlobalKind.Object(decl), m.span, m.declSpan, order = position))
    Val.Quote(Val.Rigid(Head.Glob(id), Nil))

  private def freshPrefix(): String =
    val base =
      if hint.nonEmpty then hint
      else
        anonymous += 1
        s"_m$anonymous"
    val p = Iterator.from(1).map(k => if k == 1 then base else s"$base#$k").find(p => !prefixes(p)).get
    prefixes += p
    p

  /** The functor applications being evaluated (innermost first). */
  var origin: hugin.util.Origin = hugin.util.Origin.Source

  def traced[A](frame: hugin.util.TraceFrame)(f: => A): A =
    val saved = origin
    origin = origin.push(frame)
    try f
    finally origin = saved

  private val fileRanks = mutable.LinkedHashMap.empty[String, Int]

  /** The position of a span in the program: the files in the order they are elaborated (the prelude, the
   *  imported files, the program), then the offset. */
  def positionOf(span: Span): Int =
    val rank = fileRanks.getOrElseUpdate(span.source.path, fileRanks.size)
    rank * 10_000_000 + span.start

  /** Runs `f` as part of the item at `span`, a definition named `newHint` (or ""). */
  def at[A](span: Span, newHint: String)(f: => A): A =
    val (s, p, h) = (site, position, hint)
    site = (span.source.path, span.start).hashCode
    position = positionOf(span)
    hint = newHint
    try f
    finally
      site = s
      position = p
      hint = h
