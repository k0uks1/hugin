package hugin.core

import hugin.obj.ArithOp

/** Printing of core terms in Hugin's surface notation: `[x] e` lambdas, `(x : A) -> B` and `{x : A} -> B`
 *  Π types, `⇑A`, quotes `⟨t⟩` and splices `$t` (REDESIGN §6.9). Unsolved metas print as `?n`. */
trait Printing:
  self: Core =>

  private val subscripts = "₀₁₂₃₄₅₆₇₈₉"

  def showLevel(l: Level): String =
    val v = levels.value(l)
    if v == 0 then "Type" else "Type" + v.toString.map(c => subscripts(c - '0'))

  def showVal(names: List[Name], v: Val): String = showTm(names, quote(names.length, v))

  def showTm(names: List[Name], t: Tm): String = go(names, t, 0)

  /** A term without its implicit applications (patterns, as written by users). */
  def explicitOnly(t: Tm): Tm = t match
    case Tm.App(f, _, Icit.Impl) => explicitOnly(f)
    case Tm.App(f, a, i) => Tm.App(explicitOnly(f), explicitOnly(a), i)
    case other => other

  /** As an argument of an application (parenthesised unless atomic). */
  def showArg(names: List[Name], t: Tm): String = go(names, t, 6)

  /** Whether the variable with index `ix` occurs in `t`. */
  def occurs(ix: Int, t: Tm): Boolean = t match
    case Tm.Var(i) => i == ix
    case Tm.AppPruning(f, pr) => occurs(ix, f) || pr.lift(ix).exists(_.isDefined)
    case Tm.Lam(_, _, b) => occurs(ix + 1, b)
    case Tm.App(f, a, _) => occurs(ix, f) || occurs(ix, a)
    case Tm.Pi(_, _, a, b) => occurs(ix, a) || occurs(ix + 1, b)
    case Tm.Let(_, a, d, b) => occurs(ix, a) || occurs(ix, d) || occurs(ix + 1, b)
    case Tm.Lift(a) => occurs(ix, a)
    case Tm.Quote(a) => occurs(ix, a)
    case Tm.Splice(a) => occurs(ix, a)
    case Tm.RecTy(fs) => fs.zipWithIndex.exists((f, k) => occurs(ix + k, f._2))
    case Tm.Rec(fs) => fs.exists(f => occurs(ix, f._2))
    case Tm.Proj(a, _) => occurs(ix, a)
    case Tm.Arith(_, a, b, _) => occurs(ix, a) || occurs(ix, b)
    case Tm.Negate(a, _) => occurs(ix, a)
    case Tm.Obj(_, as) => as.exists(occurs(ix, _))
    case Tm.Fresh(ns, b) => occurs(ix + ns.length, b)
    case Tm.Module(_, env) => env.exists(occurs(ix, _))
    case Tm.Persist(a) => occurs(ix, a)
    case Tm.FactTy(a) => occurs(ix, a)
    case _ => false

  private def fresh(names: List[Name], x: Name): Name =
    if x == "_" then "_"
    else
      var n = x
      while names.contains(n) do n = n + "'"
      n

  // precedence: 0 binders and arrows, 1 formulas, 2 comparisons, 3 additive and 4 multiplicative
  // arithmetic, 5 application, 6 projections, 7 atoms (the operands of `$` and `⇑`)
  private def par(p: Int, q: Int, s: String) = if p > q then s"($s)" else s

  private def go(ns: List[Name], t: Tm, p: Int): String = t match
    case Tm.Var(ix) => ns.lift(ix).getOrElse(s"#$ix")
    case Tm.Global(id) => globals(id).name
    case Tm.Meta(m) => s"?$m"
    case Tm.AppPruning(f, pr) =>
      val args = ns.zip(pr).reverse.collect { case (n, Some(i)) => if i == Icit.Impl then s"{$n}" else n }
      if args.isEmpty then go(ns, f, p) else par(p, 5, (go(ns, f, 5) :: args).mkString(" "))
    case Tm.Lam(x, i, b) =>
      val y = fresh(ns, x)
      val bind = if i == Icit.Impl then s"{$y}" else y
      par(p, 0, s"[$bind] ${go(y :: ns, b, 0)}")
    case Tm.App(f, a, i) =>
      val arg = if i == Icit.Impl then s"{${go(ns, a, 0)}}" else go(ns, a, 6)
      par(p, 5, s"${go(ns, f, 5)} $arg")
    case Tm.Pi(x, i, a, b) =>
      val y = fresh(ns, x)
      val dom =
        if i == Icit.Impl then s"{$y : ${go(ns, a, 0)}}"
        else if x == "_" then go(ns, a, 1)
        else s"($y : ${go(ns, a, 0)})"
      par(p, 0, s"$dom -> ${go(y :: ns, b, 0)}")
    case Tm.Let(x, a, d, b) =>
      val y = fresh(ns, x)
      par(p, 0, s"let $y : ${go(ns, a, 0)} = ${go(ns, d, 0)} in ${go(y :: ns, b, 0)}")
    case Tm.U0 => "type"
    case Tm.U1(l) => showLevel(l)
    case Tm.Lift(a) => s"⇑${go(ns, a, 7)}"
    case Tm.Quote(a) => s"⟨${go(ns, a, 0)}⟩"
    case Tm.Splice(a) => s"$$${go(ns, a, 7)}"
    case Tm.RecTy(fs) =>
      var names = ns
      fs.map { (l, ty) =>
        val s = s"$l : ${go(names, ty, 0)}"
        names = l :: names
        s
      }.mkString("{ ", ", ", " }")
    case Tm.Rec(fs) => if fs.isEmpty then "{ }" else fs.map((l, x) => s"$l = ${go(ns, x, 0)}").mkString("{ ", ", ", " }")
    case Tm.Proj(a, l) => par(p, 6, s"${go(ns, a, 7)}.$l")
    case Tm.Lit(l, _) => l.show
    case Tm.Base(b, _) => b.show
    case Tm.RelT => "rel"
    case Tm.PropT => "prop"
    case Tm.Arith(op, a, b, _) =>
      val q = op match
        case ArithOp.Mul | ArithOp.Div => 4
        case _ => 3
      par(p, q, s"${go(ns, a, q)} ${op.show} ${go(ns, b, q + 1)}")
    case Tm.Negate(a, _) => s"-${go(ns, a, 6)}"
    case Tm.Obj(f, as) => goObj(ns, f, as, p)
    case Tm.Module(b, _) => s"{ ${b.members.map(_.name).mkString(", ")} }"
    case Tm.Fresh(xs, b) => par(p, 0, s"fresh ${xs.mkString(" ")}. ${go(xs.reverse ++ ns, b, 0)}")
    case Tm.Persist(a) => go(ns, a, p)
    case Tm.FactTy(r) => go(ns, r, p)

  private def goObj(ns: List[Name], f: ObjForm, as: List[Tm], p: Int): String = (f, as) match
    case (ObjForm.Loc(_), List(a)) => go(ns, a, p)
    case (ObjForm.Compare(op), List(a, b)) => par(p, 2, s"${go(ns, a, 3)} ${op.show} ${go(ns, b, 3)}")
    case (ObjForm.And, Nil) => "true"
    case (ObjForm.And, as) => par(p, 1, as.map(go(ns, _, 1)).mkString(", "))
    case (ObjForm.Or, Nil) => "false"
    case (ObjForm.Or, as) => par(p, 0, as.map(go(ns, _, 0)).mkString(" ; "))
    case (ObjForm.Named(x), Nil) => x
    case (ObjForm.Not, List(a)) => par(p, 5, s"not ${go(ns, a, 6)}")
    case (ObjForm.Wild, Nil) => "_"
    case (ObjForm.As, List(a, x)) => par(p, 5, s"${go(ns, a, 6)} as ${go(ns, x, 6)}")
    case (ObjForm.Ascribe, List(a, t)) => s"(${go(ns, a, 0)} : ${go(ns, t, 0)})"
    case (ObjForm.Proj(l), List(a)) => par(p, 6, s"${go(ns, a, 7)}.$l")
    case (ObjForm.With(ls), a :: es) =>
      val fields = ls.map(_._1).zip(es).map((l, e) => s"$l = ${go(ns, e, 0)}").mkString(", ")
      par(p, 5, s"${go(ns, a, 6)} with { $fields }")
    case (ObjForm.Agg(k), List(x, t, b)) => par(p, 2, s"${go(ns, x, 3)} = ${k.show} { ${go(ns, t, 0)} | ${go(ns, b, 0)} }")
    case (ObjForm.Union, ms) => par(p, 1, ms.map(go(ns, _, 2)).mkString(" | "))
    case (ObjForm.BoundCol(k), List(a)) => par(p, 5, s"${k.show} ${go(ns, a, 6)}")
    case _ => s"<malformed ${f.toString}>"
