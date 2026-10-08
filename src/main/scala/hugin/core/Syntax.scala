package hugin.core

import hugin.obj.{ArithOp, BaseType}
import hugin.syntax.Literal

/** Core syntax of the new meta level (docs/REDESIGN.md §6): a two-level type theory in the style of
 *  Kovács, *Staged Compilation with Two-Level Type Theory* (ICFP 2022), with de Bruijn indices.
 *
 *  Stage 0 (`S0`) is the object level (Datalog terms, relations and formulas), stage 1 (`S1`) the meta
 *  level (a total dependent type theory evaluated at compile time). Both stages share one term language;
 *  the stage of a term is the stage of the universe its type lives in.
 */
enum Stage:
  case S0, S1
  def show: String = this match
    case S0 => "object"
    case S1 => "meta"

/** A requirement of a signature on the relation passed for one of its fields: `%complete l` (it is not
 *  open), `%mode l m̄` (it has the mode), `%fact l : …` (a fact constructor, readable as a relation). */
enum SigReq:
  case Complete(label: String, span: hugin.util.Span)
  case HasMode(label: String, inputs: Vector[Boolean], span: hugin.util.Span)
  case Fact(label: String)

  def label: String

/** Observes how code crosses the stages where the handover stages it (for tooling): object code at a
 *  position quoted into meta code, meta code spliced into object code, a persisted primitive value. */
trait StagingObserver:
  def quoted(span: hugin.util.Span, code: Val): Unit
  def spliced(span: hugin.util.Span, code: Val): Unit
  def persisted(span: hugin.util.Span, value: Val): Unit

/** Explicit or implicit binders and applications. */
enum Icit:
  case Expl, Impl

/** A universe level `v + k` of the meta hierarchy `Type₀ : Type₁ : …`. `v` is a level variable (an index
 *  into [[Levels]]), or [[Level.NoVar]] for the constant `k`. Levels are inferred and never written
 *  (REDESIGN §11, Q1). */
final case class Level(v: Int, k: Int):
  def succ: Level = Level(v, k + 1)
  def isConst: Boolean = v == Level.NoVar

object Level:
  val NoVar: Int = -1
  val zero: Level = Level(NoVar, 0)
  def const(k: Int): Level = Level(NoVar, k)

type Name = String

/** A pruning of a context: for each bound variable (innermost first), whether a meta is applied to it. */
type Pruning = List[Option[Icit]]

/** Core terms. Variables are de Bruijn indices; top-level entities are [[Tm.Global]]s. */
enum Tm:
  case Var(ix: Int)
  case Global(id: Int)
  case Meta(m: Int)

  /** A meta applied to the bound variables selected by a pruning (as in elaboration-zoo). */
  case AppPruning(t: Tm, pr: Pruning)
  case Lam(x: Name, i: Icit, body: Tm)
  case App(f: Tm, a: Tm, i: Icit)
  case Pi(x: Name, i: Icit, dom: Tm, cod: Tm)
  case Let(x: Name, ty: Tm, defn: Tm, body: Tm)

  /** `type`, the universe of object types (2LTT's U₀). It is classified by itself; the object level is
   *  simply typed (no object-level binders over types and no object lambdas), so this is harmless. */
  case U0

  /** `Type`, the meta universe at a level. */
  case U1(l: Level)

  /** `⇑A`: object terms of the object type `A` as meta values. */
  case Lift(a: Tm)

  /** `⟨t⟩`: quoting object code. */
  case Quote(t: Tm)

  /** `$t`: splicing meta code of type `⇑A` into object code. */
  case Splice(t: Tm)

  /** A record type `{ l₁ : A₁, … }`: a telescope, field `i` is in the scope of fields `0 … i-1`. As the
   *  type of a functor's parameter, a signature may require things of the relations passed for its
   *  fields (`reqs`), checked where the functor is applied ([[Tm.Require]]). `decls` are the positions of
   *  the fields' names and declarations where they are written (for tooling; empty if unknown). */
  case RecTy(fields: List[(Name, Tm)], reqs: List[SigReq] = Nil, decls: List[(hugin.util.Span, hugin.util.Span)] = Nil)

  /** `t`, the application of a functor: evaluation records the frame for the object code of the module
   *  instances it creates (diagnostics show the application chain, `in application of tc`). */
  case Trace(frame: hugin.util.TraceFrame, t: Tm)

  /** `t`, a record passed for a signature with requirements at `use`: evaluation records the
   *  requirements for the relations of the record ([[Requirements]]). */
  case Require(reqs: List[SigReq], use: hugin.util.Span, t: Tm)

  /** A record value `{ l₁ = e₁, … }`. */
  case Rec(fields: List[(Name, Tm)])
  case Proj(t: Tm, label: Name)

  /** A literal at a stage: an object literal of a base type, or a meta literal of a meta primitive type. */
  case Lit(l: Literal, st: Stage)

  /** A base type at a stage: `int : type` at stage 0, the meta primitive `int : Type₀` at stage 1. */
  case Base(b: BaseType, st: Stage)

  /** `rel` and `prop`, the object sorts of relations and formulas. */
  case RelT
  case PropT

  /** Arithmetic: object code at stage 0, computed at compile time at stage 1. */
  case Arith(op: ArithOp, a: Tm, b: Tm, st: Stage)
  case Negate(a: Tm, st: Stage)

  /** `fresh X̄. t`: object variables local to the object code `t` (the variables of a formula function's
   *  clause that are not its parameters). Evaluation binds them to fresh named object variables
   *  (`X#k`), so every application of a formula function gets its own (hygiene, REDESIGN §6.7). */
  case Fresh(names: List[Name], body: Tm)

  /** A module body with its environment given explicitly (`env`, innermost first: the terms its free
   *  variables stand for). Elaborated as `Module(body, x̄)` with the context's variables. */
  case Module(body: ModuleBody, env: List[Tm])

  /** Object syntax (stage 0 only): formulas, patterns, object types beyond constants, positions. */
  case Obj(form: ObjForm, args: List[Tm])

  /** Cross-stage persistence of a meta primitive value (a literal) into object code. */
  case Persist(t: Tm)

  /** The fact type of an object relation (`listed : item -> rel` uses the relation `item` as a type). */
  case FactTy(r: Tm)

object Tm:
  /** `_` in object code. */
  val Wild: Tm = Obj(ObjForm.Wild, Nil)

  /** `t` at a source position (only object terms and formulas carry positions). */
  def loc(span: hugin.util.Span, t: Tm): Tm = if span.exists then Obj(ObjForm.Loc(span), List(t)) else t

  /** `t` without the positions around it. */
  def unloc(t: Tm): Tm = t match
    case Obj(ObjForm.Loc(_), List(u)) => unloc(u)
    case u => u

  def apps(f: Tm, args: List[(Tm, Icit)]): Tm = args.foldLeft(f)((acc, a) => App(acc, a._1, a._2))

  /** The immediate subterms (those under binders included). */
  def children(t: Tm): List[Tm] = t match
    case AppPruning(f, _) => List(f)
    case Lam(_, _, b) => List(b)
    case App(f, a, _) => List(f, a)
    case Pi(_, _, a, b) => List(a, b)
    case Let(_, a, d, b) => List(a, d, b)
    case Lift(a) => List(a)
    case Quote(a) => List(a)
    case Splice(a) => List(a)
    case RecTy(fs, _, _) => fs.map(_._2)
    case Require(_, _, a) => List(a)
    case Trace(_, a) => List(a)
    case Rec(fs) => fs.map(_._2)
    case Proj(a, _) => List(a)
    case Arith(_, a, b, _) => List(a, b)
    case Negate(a, _) => List(a)
    case Obj(_, as) => as
    case Fresh(_, b) => List(b)
    case Module(_, env) => env
    case Persist(a) => List(a)
    case FactTy(a) => List(a)
    case Var(_) | Global(_) | Meta(_) | U0 | U1(_) | Lit(_, _) | Base(_, _) | RelT | PropT => Nil

  /** `t` with `f` applied to its immediate subterms (those under binders included); a module body's own
   *  terms are not subterms (its environment is). */
  def mapChildren(t: Tm)(f: Tm => Tm): Tm = t match
    case AppPruning(g, pr) => AppPruning(f(g), pr)
    case Lam(x, i, b) => Lam(x, i, f(b))
    case App(g, a, i) => App(f(g), f(a), i)
    case Pi(x, i, a, b) => Pi(x, i, f(a), f(b))
    case Let(x, a, d, b) => Let(x, f(a), f(d), f(b))
    case Lift(a) => Lift(f(a))
    case Quote(a) => Quote(f(a))
    case Splice(a) => Splice(f(a))
    case RecTy(fs, rs, ds) => RecTy(fs.map((l, a) => (l, f(a))), rs, ds)
    case Require(rs, u, a) => Require(rs, u, f(a))
    case Trace(fr, a) => Trace(fr, f(a))
    case Rec(fs) => Rec(fs.map((l, a) => (l, f(a))))
    case Proj(a, l) => Proj(f(a), l)
    case Arith(op, a, b, st) => Arith(op, f(a), f(b), st)
    case Negate(a, st) => Negate(f(a), st)
    case Obj(form, as) => Obj(form, as.map(f))
    case Fresh(ns, b) => Fresh(ns, f(b))
    case Module(b, env) => Module(b, env.map(f))
    case Persist(a) => Persist(f(a))
    case FactTy(a) => FactTy(f(a))
    case Var(_) | Global(_) | Meta(_) | U0 | U1(_) | Lit(_, _) | Base(_, _) | RelT | PropT => t

  /** `t` with its globals and metas renamed by `g` and `m`. */
  def rename(t: Tm, g: Int => Int, m: Int => Int): Tm = t match
    case Global(id) => Global(g(id))
    case Meta(x) => Meta(m(x))
    case other => mapChildren(other)(rename(_, g, m))

  /** Whether some subterm (`t` included) satisfies `p`. */
  def exists(t: Tm)(p: Tm => Boolean): Boolean = p(t) || children(t).exists(exists(_)(p))

  /** Shifts the free variables of `t` (indices `≥ cutoff`) by `by`. */
  def shift(t: Tm, by: Int, cutoff: Int = 0): Tm =
    def go(t: Tm, k: Int): Tm = t match
      case Var(ix) => if ix >= k then Var(ix + by) else t
      case AppPruning(f, pr) =>
        // the pruning is aligned with the context (innermost first): the new variables are not selected
        AppPruning(f, pr.take(k) ++ List.fill(by)(None) ++ pr.drop(k))
      case Lam(x, i, b) => Lam(x, i, go(b, k + 1))
      case App(f, a, i) => App(go(f, k), go(a, k), i)
      case Pi(x, i, a, b) => Pi(x, i, go(a, k), go(b, k + 1))
      case Let(x, a, d, b) => Let(x, go(a, k), go(d, k), go(b, k + 1))
      case Lift(a) => Lift(go(a, k))
      case Quote(a) => Quote(go(a, k))
      case Splice(a) => Splice(go(a, k))
      case RecTy(fs, rs, ds) => RecTy(fs.zipWithIndex.map((f, j) => (f._1, go(f._2, k + j))), rs, ds)
      case Require(rs, u, a) => Require(rs, u, go(a, k))
      case Trace(f, a) => Trace(f, go(a, k))
      case Rec(fs) => Rec(fs.map((l, x) => (l, go(x, k))))
      case Proj(a, l) => Proj(go(a, k), l)
      case Arith(op, a, b, st) => Arith(op, go(a, k), go(b, k), st)
      case Negate(a, st) => Negate(go(a, k), st)
      case Obj(f, as) => Obj(f, as.map(go(_, k)))
      case Fresh(ns, b) => Fresh(ns, go(b, k + ns.length))
      case Module(b, env) => Module(b, env.map(go(_, k)))
      case Persist(a) => Persist(go(a, k))
      case FactTy(a) => FactTy(go(a, k))
      case other => other
    go(t, cutoff)

  /** `⟨$t⟩ = t` and `$⟨t⟩ = t`. */
  def quote(t: Tm): Tm = t match
    case Splice(u) => u
    case u => Quote(u)
  def splice(t: Tm): Tm = t match
    case Quote(u) => u
    case u => Splice(u)
