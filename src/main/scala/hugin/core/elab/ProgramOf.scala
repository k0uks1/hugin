package hugin.core
package elab

import hugin.obj.{ArithOp, BaseType, CmpOp}
import hugin.syntax.{Literal, Tree, TreeOps}
import hugin.syntax.Trees.{Apply, Ident, Parens}
import hugin.util.*

import scala.collection.mutable

/** `programOf P` (reference: std/quote, "Programs as values"; #186 P7a): the rules of a module body as a
 *  `program` of `std/semantics`, a value the meta level can prove things about. `P` is
 *
 *  - a functor application `f a₁ … aₙ` (the arguments may be variables): the program of `f`'s body, its
 *    parameters' relations as `arg l`, their types as the arguments give them;
 *  - a functor `f`: the function `[x̄] programOf (f x̄)` from its parameters to programs;
 *  - a module or an instance `m`: the program of its body at the arguments of the application that made it
 *    (the instance's recorded environment), so `programOf m` is `programOf (f ā)`.
 *
 *  The body is evaluated with its environment and its object members abstract (fresh variables), as
 *  staging would evaluate it, which runs the meta code its rules splice and inlines formula functions;
 *  the normal forms are read as data: the body's own relations (relations, structs, constructors, in
 *  source order) are `own i`, the relations of its environment `arg l` by their path in it (`edge` for
 *  `g.edge`, `g.edge` if the body has several variables), other relations `ext s`. A rule's variables are
 *  typed by object typing, a wildcard or a variable of a formula function by the column it stands in.
 *  The program's inputs are the relations of its environment and outside it, and its own relations
 *  without rules (the extensional relations); its strata are the strongly connected components of its own
 *  relations, dependencies first. The data is built in the context of the body's environment and applied
 *  to it, so it is a meta term in the parameters, as a functor's body is. No code is generated. */
trait ProgramOf:
  self: Elaborator =>
  import core.*

  /** Whether `t` is `programOf e …`: the name is not bound otherwise (a contextual keyword). */
  def isProgramOf(c: Cxt, t: Tree): Boolean = TreeOps.flattenApp(t) match
    case (Ident("programOf"), _ :: _) => !c.scope.contains("programOf") && lookupGlobal("programOf").isEmpty
    case _ => false

  /** The globals `programOf` builds its data with. */
  private final case class Vocabulary(sem: Map[Name, Int], inputOf: Int, nat: Int, nil: Int, cons: Int, some: Int, none: Int)

  private def vocabulary(span: Span): Vocabulary =
    def module(n: String): Map[Name, Int] =
      val path = hugin.compiler.SourceLoader.resolve(file.path, n)
      file.imports.get(path).map(_.value).collect { case Tm.Rec(fs) => fs }.toList.flatten.collect { case (k, Tm.Global(id)) => k -> id }.toMap
    val quoteLib = module("std/quote")
    val sem = module("std/semantics")
    val r = reflectiveGlobals
    (quoteLib.get("inputOf"), sem.get("own"), r, coreName("some"), coreName("none")) match
      case (Some(inputOf), Some(own), Some(rg), Some(some), Some(none)) if sem.contains("program") =>
        val nat = telescope(globals(own).ty)._1.collectFirst { case (_, Icit.Expl, d) => d }.map(forceData) match
          case Some(Val.Rigid(Head.Glob(id), Nil)) => id
          case other => throw Impossible(s"own over $other")
        Vocabulary(sem, inputOf, nat, rg.nil, rg.cons, some, none)
      case _ => fail(ProgramOfProblem.NoLibrary(span))

  // ---------------------------------------------------------------- the forms of `programOf P`

  def inferProgramOf(c: Cxt, t: Tree): (Tm, Val, Stage) =
    val (_, args) = TreeOps.flattenApp(t)
    val p = args.tail.foldLeft(args.head)((f, a) => Apply(f, a)(f.span.to(a.span)))
    val voc = vocabulary(t.span)
    val programTy = eval(Nil, Tm.Global(voc.sem("program")))
    def notAModule(shown: Tree): Nothing =
      val here = shown match
        case Ident("here") | Parens(Ident("here")) => true
        case _ => false
      fail(ProgramOfProblem.NotAModule(hugin.syntax.Printer.show(shown), here, shown.span))
    p match
      case Ident("here") | Parens(Ident("here")) => notAModule(p)
      case _ =>
    val (head, written) = TreeOps.flattenApp(p)
    val (hTm, hTy, hSt) = infer(c, head)
    if hSt != Stage.S1 then notAModule(p)
    if written.nonEmpty then
      // a functor applied: its arguments checked against its parameters
      var ty = hTy
      val argTms = written.map { a =>
        force(ty) match
          case Val.Pi(_, Icit.Expl, d, cl) =>
            val tm = check(c, a, d, Stage.S1)
            ty = inst(cl, ev(c, tm))
            tm
          case _ => notAModule(p)
      }
      (applied(c, voc, hTm, argTms, p), programTy, Stage.S1)
    else
      force(hTy) match
        case Val.Pi(_, Icit.Expl, _, _) =>
          // a functor: the function from its parameters to the programs of its applications
          var cx = c
          var ty = hTy
          val doms = mutable.ListBuffer.empty[(Name, Tm)]
          var more = true
          while more do
            force(ty) match
              case Val.Pi(x, Icit.Expl, d, cl) =>
                doms += ((x, quote(cx.lvl, d)))
                cx = bind(cx, x, d, Stage.S1)
                ty = inst(cl, Val.local(cx.lvl - 1))
              case _ => more = false
          val k = doms.length
          val inner = applied(cx, voc, Tm.shift(hTm, k), (0 until k).map(j => Tm.Var(k - 1 - j)).toList, p)
          val tm = doms.foldRight(inner)((d, acc) => Tm.Lam(d._1, Icit.Expl, acc))
          val tyTm = doms.foldRight(Tm.Global(voc.sem("program")): Tm)((d, acc) => Tm.Pi(d._1, Icit.Expl, d._2, acc))
          (tm, eval(c.env, tyTm), Stage.S1)
        case _ =>
          moduleOf(ev(c, hTm)) match
            case Some((body, env)) =>
              val reified = reify(voc, body, env.length, p.span)
              (Tm.apps(lams(env.length, reified), env.reverse.map(v => (quote(c.lvl, v), Icit.Expl))), programTy, Stage.S1)
            case None => notAModule(p)

  /** The program of the functor `f` applied to `args` (terms in `c`): the body is found by applying `f` to
   *  fresh variables, so that no instance is created. */
  private def applied(c: Cxt, voc: Vocabulary, f: Tm, args: List[Tm], p: Tree): Tm =
    val k = args.length
    val probes = (0 until k).map(j => Val.local(c.lvl + j)).toList
    val v = probes.foldLeft(ev(c, f))((g, a) => app(g, a, Icit.Expl))
    force(v) match
      case Val.Rigid(Head.Module(body, env), Nil) =>
        val reified = reify(voc, body, env.length, p.span)
        val inner = Tm.apps(lams(env.length, reified), env.reverse.map(e => (quote(c.lvl + k, e), Icit.Expl)))
        Tm.apps(lams(k, inner), args.map((_, Icit.Expl)))
      case _ => fail(ProgramOfProblem.NotAModule(hugin.syntax.Printer.show(p), false, p.span))

  private def lams(n: Int, body: Tm): Tm = (0 until n).foldLeft(body)((acc, i) => Tm.Lam(s"x$i", Icit.Expl, acc))

  /** The body and environment of a module value: a module in an open environment, or an instance. */
  private def moduleOf(v: Val): Option[(ModuleBody, List[Val])] = forceData(v) match
    case Val.Rigid(Head.Module(body, env), Nil) => Some((body, env))
    case Val.Rec(fields) =>
      val ids = fields.collect { case (n, f) => n -> forceData(f) }.collect { case (n, Val.Quote(code)) => n -> forceData(code) }.collect {
        case (n, Val.Rigid(Head.Glob(id), Nil)) => n -> id
      }.toMap
      moduleInstances.find { i =>
        val members = i.body.members
        val values = i.env.take(members.length).reverse
        members.nonEmpty && members.zip(values).forall { (m, mv) =>
          m.kind match
            case MemberKind.Object(_) =>
              forceData(mv) match
                case Val.Quote(code) =>
                  forceData(code) match
                    case Val.Rigid(Head.Glob(id), Nil) => ids.get(m.name).contains(id)
                    case _ => false
                case _ => false
            case _ => true
        } && members.exists(_.kind.isInstanceOf[MemberKind.Object])
      }.map(i => (i.body, i.env.drop(i.body.members.length)))
    case _ => None

  // ---------------------------------------------------------------- reading a body

  /** A relation reference of `std/semantics`. */
  private enum Ref:
    case Own(i: Int)
    case Arg(label: String)
    case Ext(id: Int)

  /** The head of an atom or a constructor term: its reference, its object type, and its code as a term
   *  in the body's environment (absent for a constant of the body, which has no code outside an
   *  instance). */
  private final case class HeadInfo(ref: Ref, ty: Val, code: Option[Val])

  /** A term of a rule: a variable (its position), closed code, a constructor term, arithmetic. */
  private enum RT:
    case V(i: Int)
    case C(code: Val, ty: Val)
    case App(h: HeadInfo, args: List[RT], code: Val, closed: Boolean)
    case Ar(op: ArithOp, a: RT, b: RT)
    case Ng(a: RT)

  private final case class RA(ref: Ref, args: List[RT])

  private enum RB:
    case Pos(a: RA)
    case Cmp(op: CmpOp, l: RT, r: RT)

  private final case class ReadRule(head: Int, label: Option[Name], vars: List[Val], heads: List[RA], body: List[RB], span: Span)

  /** The program of `body` in an environment of `n` variables, as a term in that environment. */
  private def reify(voc: Vocabulary, body: ModuleBody, n: Int, span: Span): Tm =
    val ctxVals = (0 until n).reverse.map(Val.local).toList
    // the types of the environment's variables, where the body records them
    val ctxTypes: Map[Int, Val] =
      if body.context.length != n then Map.empty
      else
        var e = List.empty[Val]
        body.context.zipWithIndex.map { case ((_, ty), i) =>
          val v = eval(e, ty)
          e = Val.local(i) :: e
          i -> v
        }.toMap
    val ctxNames: Map[Int, Name] = if body.context.length == n then body.context.map(_._1).zipWithIndex.map(_.swap).toMap else Map.empty
    // the members: object constants abstract (fresh variables), definitions evaluated
    var e = ctxVals
    var level = n
    val memberAt = mutable.LinkedHashMap.empty[Int, (Member, Val)]
    for m <- body.members do
      val v = m.kind match
        case MemberKind.Object(_) =>
          val ty = eval(e, m.ty)
          memberAt(level) = (m, ty)
          level += 1
          Val.local(level - 1)
        case MemberKind.Defined(t) => eval(e, t)
      e = v :: e
    val total = level
    val relationLike = memberAt.toList.filter { case (_, (m, _)) =>
      m.kind match
        case MemberKind.Object(ObjDecl.Relation | ObjDecl.Struct | ObjDecl.Constructor) => true
        case _ => false
    }.sortBy(_._2._1.span.start)
    val ownIndex: Map[Int, Int] = relationLike.map(_._1).zipWithIndex.toMap
    val reader = BodyReader(n, total, e, ctxTypes, ctxNames, memberAt.toMap, ownIndex, span)
    val rules = body.items.collect { case r: CoreItem.RuleItem => r }.map(reader.rule)
    emit(voc, n, total, relationLike.map(_._2._1.name), rules, span)

  /** Reads the rules of a body: `n` variables of the environment, `total` with the object members, `env`
   *  the body's environment with its members. */
  private final class BodyReader(
      n: Int,
      total: Int,
      env: List[Val],
      ctxTypes: Map[Int, Val],
      ctxNames: Map[Int, Name],
      memberAt: Map[Int, (Member, Val)],
      ownIndex: Map[Int, Int],
      use: Span
  ):
    private var current: CoreItem.RuleItem = null.asInstanceOf[CoreItem.RuleItem]
    private def no(reason: String): Nothing = fail(ProgramOfProblem.CannotReify(reason, current.span, use))

    // the variables of the rule being read: their names (markers of the rule's own, the names of a formula
    // function's variables, wildcards) and types
    private val names = mutable.ArrayBuffer.empty[String]
    private val types = mutable.ArrayBuffer.empty[Option[Val]]
    private val shown = mutable.ArrayBuffer.empty[String]

    private def variable(name: String, display: String): Int =
      val i = names.indexOf(name)
      if i >= 0 then i
      else
        names += name
        types += None
        shown += display
        names.length - 1

    private var wilds = 0

    def rule(r: CoreItem.RuleItem): ReadRule =
      current = r
      names.clear(); types.clear(); shown.clear(); wilds = 0
      val markers = r.vars.zipWithIndex.map((v, i) => s"${v._1}#p$i")
      var e2 = env
      for ((x, tyTm), i) <- r.vars.zipWithIndex do
        variable(markers(i), x)
        // the type object typing gave the variable, if it solved it
        types(i) = force(eval(e2, tyTm)) match
          case Val.Flex(_, _) => None
          case ty => Some(ty)
        e2 = Val.Obj(ObjForm.Named(markers(i)), Nil) :: e2
      val heads = r.heads.flatMap(h => headAtoms(forceData(eval(e2, h))))
      val body = r.body.toList.flatMap(b => formula(forceData(eval(e2, b))))
      val first = heads.headOption.map(_.ref) match
        case Some(Ref.Own(i)) => i
        case _ => no("its head is not a relation of the module")
      val vars = types.toList.zip(shown).map {
        case (Some(ty), _) => ty
        case (None, x) => no(s"the type of the variable `${x.takeWhile(_ != '#')}` is not known")
      }
      ReadRule(first, r.name, vars, heads, body, r.span)

    /** The relation, type and code of an applied head, with its arguments. */
    private def headOf(v: Val): Option[(HeadInfo, List[Val])] = v match
      case Val.Rigid(Head.Glob(id), sp) if globals(id).stage == Stage.S0 && globals(id).kind.isInstanceOf[GlobalKind.Object] =>
        applications(sp).map(as => (HeadInfo(Ref.Ext(id), globals(id).ty, Some(Val.Rigid(Head.Glob(id), Nil))), as))
      case Val.Rigid(Head.Local(l), sp) =>
        val rs = sp.reverse
        val projs = rs.takeWhile(_.isInstanceOf[Elim.EProj]).collect { case Elim.EProj(lb) => lb }
        rs.drop(projs.length) match
          case Elim.ESplice :: rest =>
            applications(rest.reverse).flatMap { as =>
              if memberAt.contains(l) && projs.isEmpty then
                ownIndex.get(l).map(i => (HeadInfo(Ref.Own(i), lifted(memberAt(l)._2), None), as))
              else if l < n then
                val path = projs.mkString(".")
                val label =
                  if n == 1 && path.nonEmpty then path
                  else (ctxNames.getOrElse(l, s"x$l") :: projs).mkString(".")
                val meta = projs.foldLeft(Val.local(l))((acc, lb) => proj(acc, lb))
                typeAlong(l, projs).map(ty => (HeadInfo(Ref.Arg(label), ty, Some(vSplice(meta))), as))
              else None
            }
          case _ => None
      case _ => None

    private def applications(sp: Spine): Option[List[Val]] =
      Option.when(sp.forall {
        case Elim.EApp(_, Icit.Expl) => true
        case _ => false
      })(sp.reverse.collect { case Elim.EApp(a, _) => a })

    private def lifted(ty: Val): Val = force(ty) match
      case Val.Lift(t) => t
      case other => other

    /** The object type of the relation at the path `projs` of the environment's variable `l`. */
    private def typeAlong(l: Int, projs: List[Name]): Option[Val] =
      var v = Val.local(l)
      var ty = ctxTypes.get(l)
      for lb <- projs do
        ty = ty.flatMap(t =>
          force(t) match
            case rt: Val.RecTy => fieldType(rt, v, lb)
            case _ => None
        )
        v = proj(v, lb)
      ty.map(lifted)

    /** The type of the column `j` of an object constant of type `ty`. */
    private def column(ty: Val, j: Int): Option[Val] = objectColumns(ty).lift(j).map(_._2)

    /** The type the constructor of type `ty` builds. */
    private def codomain(ty: Val): Val = force(ty) match
      case Val.Pi(_, _, d, cl) => codomain(inst(cl, Val.Wild))
      case Val.Lift(t) => codomain(t)
      case other => other

    /** The type of the identity of a fact of `h`: a relation's fact type, a constructor's type. */
    private def factType(h: HeadInfo): Val = codomain(h.ty) match
      case Val.RelT => h.code.map(Val.FactTy(_)).getOrElse(Val.RelT)
      case other => other

    private def setType(t: RT, ty: Option[Val]): Unit = t match
      case RT.V(i) if types(i).isEmpty => types(i) = ty
      case _ =>

    /** A term; in a head, a constructor term of closed code is kept as such, since its nested facts are
     *  heads. */
    private def term(v0: Val, inHead: Boolean): RT =
      val v = forceData(v0)
      v match
        case Val.Obj(ObjForm.Named(x), Nil) => RT.V(variable(x, x))
        case Val.Obj(ObjForm.Wild, Nil) =>
          wilds += 1
          RT.V(variable(s"_#w$wilds", "_"))
        case Val.Lit(_, Stage.S0) | Val.Persist(_) => RT.C(v, typeOfCode(v).get)
        case Val.Arith(ArithOp.Concat, _, _, Stage.S0) => no("string concatenation `^` is not interpreted by `std/semantics`")
        case Val.Arith(op, a, b, Stage.S0) => RT.Ar(op, intTerm(a), intTerm(b))
        case Val.Negate(a, Stage.S0) => RT.Ng(intTerm(a))
        case Val.Obj(ObjForm.As, _) => no("`as` in a term")
        case Val.Obj(ObjForm.Ascribe, _) => no("an ascription")
        case Val.Obj(ObjForm.Proj(_), _) => no("a projection")
        case Val.Obj(ObjForm.With(_), _) => no("a functional update")
        case _ =>
          headOf(v) match
            case Some((h, as)) =>
              val args = as.map(term(_, inHead))
              args.zipWithIndex.foreach((t, j) => setType(t, column(h.ty, j)))
              val closed = args.forall {
                case RT.C(_, _) => true
                case RT.App(_, _, _, c) => c
                case _ => false
              }
              if closed && !inHead && h.code.isDefined then RT.C(v, codomain(h.ty))
              else
                if h.code.isEmpty then
                  no("a constructor term of a constant that the module declares, which has no code outside an instance")
                RT.App(h, args, v, closed)
            case None => no(s"`${showValPlain(Nil, v)}` is not object code that `std/semantics` models")

    private def intTerm(v: Val): RT =
      val t = term(v, inHead = false)
      val int = Val.Base(BaseType.IntT, Stage.S0)
      t match
        case RT.V(i) =>
          types(i) match
            case None => types(i) = Some(int)
            case Some(ty) if forceData(ty) == int =>
            case Some(_) => no("arithmetic on a variable that is not an `int`")
        case RT.C(_, ty) if forceData(ty) == int =>
        case RT.Ar(_, _, _) | RT.Ng(_) =>
        case _ => no("arithmetic on a term that is not an `int` (floats are not interpreted by `std/semantics`)")
      t

    private def typeOfCode(code: Val): Option[Val] = forceData(code) match
      case Val.Lit(l, Stage.S0) => Some(Val.Base(BaseType.of(l), Stage.S0))
      case Val.Persist(x) =>
        forceData(x) match
          case Val.Lit(l, _) => Some(Val.Base(BaseType.of(l), Stage.S0))
          case _ => Some(Val.Base(BaseType.IntT, Stage.S0))
      case Val.Arith(_, _, _, _) | Val.Negate(_, _) => Some(Val.Base(BaseType.IntT, Stage.S0))
      case other => headOf(other).map((h, _) => codomain(h.ty))

    /** The atom of a head, then its nested facts (its constructor terms, outermost first). */
    private def headAtoms(v: Val): List[RA] = headOf(v) match
      case Some((h, as)) =>
        val args = as.map(term(_, inHead = true))
        args.zipWithIndex.foreach((t, j) => setType(t, column(h.ty, j)))
        def nested(t: RT): List[RA] = t match
          case RT.App(h2, as2, _, _) => RA(h2.ref, as2) :: as2.flatMap(nested)
          case _ => Nil
        RA(h.ref, args) :: args.flatMap(nested)
      case None => no(s"its head `${showValPlain(Nil, v)}` is not an atom")

    private def formula(v: Val): List[RB] = v match
      case Val.Obj(ObjForm.And, as) => as.flatMap(a => formula(forceData(a)))
      case Val.Obj(ObjForm.Compare(op), List(a, b)) => List(RB.Cmp(op, term(a, inHead = false), term(b, inHead = false)))
      case Val.Obj(ObjForm.As, List(a, x)) =>
        // `(r t̄ as X)`: the atom, and `X` the identity of its fact
        val atom = forceData(a)
        val (pos, fact) = headOf(atom) match
          case Some((h, as)) if h.code.isDefined =>
            val args = as.map(term(_, inHead = false))
            args.zipWithIndex.foreach((t, j) => setType(t, column(h.ty, j)))
            (List(RB.Pos(RA(h.ref, args))), RT.App(h, args, atom, false))
          case _ => no("`as` on an atom of a relation that the module declares")
        val xv = term(x, inHead = false)
        fact match
          case RT.App(h, _, _, _) => setType(xv, Some(factType(h)))
          case _ =>
        pos :+ RB.Cmp(CmpOp.Eq, xv, fact)
      case Val.Obj(ObjForm.Not, _) => no("negation is not in the positive fragment of `std/semantics`")
      case Val.Obj(ObjForm.Or, _) => no("disjunction is not in the positive fragment of `std/semantics`")
      case Val.Obj(ObjForm.Agg(_), _) => no("aggregates are not in the positive fragment of `std/semantics`")
      case _ =>
        headOf(v) match
          case Some((h, as)) =>
            val args = as.map(term(_, inHead = false))
            args.zipWithIndex.foreach((t, j) => setType(t, column(h.ty, j)))
            List(RB.Pos(RA(h.ref, args)))
          case None => no(s"`${showValPlain(Nil, v)}` is not an atom or a comparison")

  // ---------------------------------------------------------------- building the data

  /** `t` (a term in an environment of `total` variables) without the variables at levels `n … total-1`
   *  (the object members), in an environment of `n`; `None` if it mentions one of them or an unknown. */
  private def strengthen(t: Tm, n: Int, total: Int): Option[Tm] =
    val by = total - n
    var ok = true
    def go(t: Tm, d: Int): Tm = t match
      case Tm.Var(ix) =>
        if ix < d then t
        else if ix - d < by then
          ok = false
          t
        else Tm.Var(ix - by)
      case Tm.Meta(_) | Tm.AppPruning(_, _) =>
        ok = false
        t
      case Tm.Lam(x, i, b) => Tm.Lam(x, i, go(b, d + 1))
      case Tm.Pi(x, i, a, b) => Tm.Pi(x, i, go(a, d), go(b, d + 1))
      case Tm.Let(x, a, df, b) => Tm.Let(x, go(a, d), go(df, d), go(b, d + 1))
      case Tm.RecTy(fs, rs, ds) => Tm.RecTy(fs.zipWithIndex.map((f, j) => (f._1, go(f._2, d + j))), rs, ds)
      case Tm.Fresh(ns, b) => Tm.Fresh(ns, go(b, d + ns.length))
      case Tm.Module(_, _) =>
        ok = false
        t
      case other => Tm.mapChildren(other)(go(_, d))
    val out = go(t, 0)
    Option.when(ok)(out)

  private def emit(voc: Vocabulary, n: Int, total: Int, relations: List[Name], rs: List[ReadRule], span: Span): Tm =
    def g(name: Name): Tm = Tm.Global(voc.sem(name))
    def app(f: Tm, args: (Tm, Icit)*): Tm = Tm.apps(f, args.toList)
    def impl(t: Tm) = (t, Icit.Impl)
    def expl(t: Tm) = (t, Icit.Expl)
    def nat(k: Int): Tm = Tm.Nat(voc.nat, BigInt(k))
    def str(s: String): Tm = Tm.Lit(Literal.StrL(s), Stage.S1)
    def list(elem: Tm, xs: List[Tm]): Tm =
      xs.foldRight(app(Tm.Global(voc.nil), impl(elem)))((x, acc) => app(Tm.Global(voc.cons), impl(elem), expl(x), expl(acc)))
    val stringT = Tm.Base(BaseType.StringT, Stage.S1)
    val codeT = Tm.Lift(Tm.U0) // ⇑type
    val natT = Tm.Global(voc.nat)
    def fail0(reason: String, rule: Span): Nothing = fail(ProgramOfProblem.CannotReify(reason, rule, span))
    var at = span
    def closed(t: Tm, what: => String): Tm = strengthen(t, n, total).getOrElse(fail0(what, at))
    def typeTm(ty: Val): Tm = closed(quote(total, ty), "a variable of a type that the module declares")
    def codeTm(v: Val): Tm = closed(quote(total, v), "code of a constant that the module declares")
    def refTm(r: Ref): Tm = r match
      case Ref.Own(i) => app(g("own"), expl(nat(i)))
      case Ref.Arg(l) => app(g("arg"), expl(str(l)))
      case Ref.Ext(id) => app(g("ext"), expl(Tm.Quote(Tm.Global(id))))
    // the proof that position `i` of `tys` (codes of types) holds `tys(i)`
    def member(tys: List[Tm], i: Int): Tm =
      if i == 0 then app(g("here"), impl(codeT), impl(tys.head), impl(list(codeT, tys.tail)))
      else app(g("there"), impl(codeT), impl(tys(i)), impl(tys.head), impl(list(codeT, tys.tail)), expl(member(tys.tail, i - 1)))
    val opName = Map(ArithOp.Add -> "oadd", ArithOp.Sub -> "osub", ArithOp.Mul -> "omul", ArithOp.Div -> "odiv")
    val cmpName = Map(CmpOp.Eq -> "ceq", CmpOp.Ne -> "cne", CmpOp.Lt -> "clt", CmpOp.Le -> "cle", CmpOp.Gt -> "cgt", CmpOp.Ge -> "cge")
    val crules = rs.zipWithIndex.map { (r, k) =>
      at = r.span
      val tys = r.vars.map(ty => Tm.quote(typeTm(ty)))
      val ts = list(codeT, tys)
      def typeOfRT(t: RT): Tm = t match
        case RT.V(i) => tys(i)
        case RT.C(_, ty) => Tm.quote(typeTm(ty))
        case RT.App(h, _, _, _) =>
          Tm.quote(typeTm(codomainOf(h.ty) match
            case Val.RelT => h.code.map(Val.FactTy(_)).getOrElse(Val.RelT)
            case other => other
          ))
        case RT.Ar(_, _, _) | RT.Ng(_) => Tm.Quote(Tm.Base(BaseType.IntT, Stage.S0))
      def term(t: RT): Tm = t match
        case RT.V(i) => app(g("cv"), impl(ts), impl(tys(i)), expl(member(tys, i)))
        case RT.C(code, _) => app(g("cc"), impl(ts), impl(typeOfRT(t)), expl(Tm.quote(codeTm(code))))
        case RT.App(_, _, code, true) => app(g("cc"), impl(ts), impl(typeOfRT(t)), expl(Tm.quote(codeTm(code))))
        case RT.App(h, args, _, false) =>
          val ss = args.map(typeOfRT)
          val head = codeTm(h.code.get)
          // `[e] ⟨h $(valueAt e 0) … $(valueAt e (n-1))⟩`, under the binder of `e`
          val ss1 = ss.map(Tm.shift(_, 1))
          val built = args.indices.foldLeft(Tm.shift(head, 1)) { (acc, j) =>
            Tm.App(
              acc,
              Tm.splice(app(g("valueAt"), impl(list(codeT, ss1)), impl(ss1(j)), expl(Tm.Var(0)), expl(member(ss1, j)))),
              Icit.Expl
            )
          }
          val f = Tm.Lam("e", Icit.Expl, Tm.quote(built))
          app(g("capp"), impl(ts), impl(list(codeT, ss)), impl(typeOfRT(t)), expl(f), expl(terms(args, ss)))
        case RT.Ar(op, a, b) => app(g("carith"), impl(ts), expl(Tm.Global(reflective(span).ctor(opName(op)))), expl(term(a)), expl(term(b)))
        case RT.Ng(a) => app(g("cneg"), impl(ts), expl(term(a)))
      def terms(args: List[RT], ss: List[Tm]): Tm =
        args.zip(ss).zipWithIndex.foldRight(app(g("tnil"), impl(ts))) { case (((a, s), j), acc) =>
          app(g("tcons"), impl(ts), impl(list(codeT, ss.drop(j + 1))), impl(s), expl(term(a)), expl(acc))
        }
      def atom(a: RA): Tm =
        val ss = a.args.map(typeOfRT)
        app(g("cat"), impl(ts), impl(list(codeT, ss)), expl(refTm(a.ref)), expl(terms(a.args, ss)))
      def literal(b: RB): Tm = b match
        case RB.Pos(a) => app(g("cpos"), impl(ts), expl(atom(a)))
        case RB.Cmp(op, l, r) =>
          val (lt, rt) = (typeOfRT(l), typeOfRT(r))
          if stripPositions(lt) != stripPositions(rt) then fail0("a comparison of terms of different object types", at)
          app(g("ccmp"), impl(ts), impl(lt), expl(Tm.Global(reflective(span).ctor(cmpName(op)))), expl(term(l)), expl(term(r)))
      val index = rs.take(k).count(_.head == r.head) + 1
      val label = r.label match
        case Some(l) => app(Tm.Global(voc.some), impl(stringT), expl(str(l)))
        case None => app(Tm.Global(voc.none), impl(stringT))
      Tm.Rec(
        List(
          "head" -> nat(r.head),
          "index" -> nat(index),
          "label" -> label,
          "vars" -> ts,
          "heads" -> list(app(g("catom"), expl(ts)), r.heads.map(atom)),
          "body" -> list(app(g("cbody"), expl(ts)), r.body.map(literal))
        )
      )
    }
    // the own relations without rules are the inputs; the strata are the components of the dependencies
    val heads = rs.flatMap(_.heads.collect { case RA(Ref.Own(i), _) => i }).toSet
    val inputs = relations.indices.filterNot(heads).toList
    val deps = relations.indices.map { i =>
      i -> rs.filter(_.heads.exists(_.ref == Ref.Own(i))).flatMap(_.body.collect { case RB.Pos(RA(Ref.Own(j), _)) => j }).toSet
    }.toMap
    val strata = components(relations.length, deps)
    Tm.Rec(
      List(
        "relations" -> list(stringT, relations.map(str)),
        "rules" -> list(g("crule"), crules),
        "input" -> app(Tm.Global(voc.inputOf), expl(list(natT, inputs.map(nat)))),
        "strata" -> list(app(Tm.Global(reflective(span).list), expl(natT)), strata.map(s => list(natT, s.map(nat))))
      )
    )

  private def codomainOf(ty: Val): Val = force(ty) match
    case Val.Pi(_, _, _, cl) => codomainOf(inst(cl, Val.Wild))
    case Val.Lift(t) => codomainOf(t)
    case other => other

  /** The strongly connected components of a graph on `0 … n-1`, dependencies first (Tarjan). */
  private def components(n: Int, deps: Map[Int, Set[Int]]): List[List[Int]] =
    var index = 0
    val idx = mutable.Map.empty[Int, Int]
    val low = mutable.Map.empty[Int, Int]
    val stack = mutable.Stack.empty[Int]
    val on = mutable.Set.empty[Int]
    val out = mutable.ListBuffer.empty[List[Int]]
    def visit(v: Int): Unit =
      idx(v) = index; low(v) = index; index += 1
      stack.push(v); on += v
      for w <- deps.getOrElse(v, Set.empty).toList.sorted do
        if !idx.contains(w) then
          visit(w)
          low(v) = low(v) min low(w)
        else if on(w) then low(v) = low(v) min idx(w)
      if low(v) == idx(v) then
        val comp = mutable.ListBuffer.empty[Int]
        var w = -1
        while w != v do
          w = stack.pop(); on -= w; comp += w
        out += comp.toList.sorted
    for v <- 0 until n if !idx.contains(v) do visit(v)
    out.toList
