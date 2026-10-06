package hugin.ir

import hugin.compiler.*
import hugin.obj.*
import hugin.obj.typing.{Moding, TypeOps}
import hugin.syntax.Literal
import scala.collection.mutable

/** Compiles core rules into the register-based IR of Section 9.3. Bodies are compiled in canonical order. */
final class Lowering(p: ObjProgram, ops: TypeOps)(using Context):
  private val compOf: Map[RelSym, Int] = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
  val indexes: mutable.HashMap[Int, mutable.Set[Vector[Int]]] = mutable.HashMap.empty

  def lit(l: Literal): Any = l match
    case Literal.IntL(v) => java.lang.Long.valueOf(v)
    case Literal.FloatL(v) => java.lang.Double.valueOf(v)
    case Literal.StrL(v) => v

  def tags(t: OType): Set[Int] = ops.members(t).map(_.tag)

  /** Per-rule compilation state. */
  private final class RuleCompiler(currentComp: Option[Int]):
    val regOf = mutable.HashMap.empty[String, Int]
    var nregs = 0
    var recAtoms = 0
    def fresh(): Int = { nregs += 1; nregs - 1 }
    def bound(v: String): Boolean = regOf.contains(v)

    def expr(t: Term): Expr = t match
      case Term.Var(n) => Expr.Reg(regOf(n))
      case Term.Lit(l) => Expr.Const(lit(l))
      case Term.Arith(op, l, r) => Expr.Arith(op, expr(l), expr(r))
      case Term.Neg(x) => Expr.Neg(expr(x))
      case Term.App(RelRef.Sym(c), as) => Expr.Make(c.tag, as.map(expr).toArray)
      case Term.As(x, _) => expr(x)
      case Term.Ascr(x, _) => expr(x)
      case other => throw IllegalStateException(s"cannot lower term ${ObjPrinter.term(other)}")

    /** The value of a bound term in a body. The value of a constructor term is an existing fact, also
     *  nested (`cons 1 nil`), so it is looked up rather than built. An ascription of a constructor term
     *  accepted by the typer always holds (the fact type is a subtype of the ascribed type, or equal to
     *  it), so it is dropped. */
    def operand(t: Term, out: mutable.ListBuffer[BodyOp]): Expr = t match
      case Term.App(RelRef.Sym(c), as) =>
        val args = as.map(operand(_, out)).toArray
        val y = fresh()
        out += BodyOp.Lookup(y, c.tag, args)
        Expr.Reg(y)
      case Term.Ascr(x: Term.App, _) => operand(x, out)
      case other => expr(other)

    /** Whether a term is fully bound (it can be compared as a value). */
    def isBound(t: Term): Boolean = Moding.vars(t).forall(bound)

    /** Match term `t` against the word in register `y`. */
    def matchReg(t: Term, y: Int, out: mutable.ListBuffer[BodyOp]): Unit = t match
      case Term.Var(n) =>
        regOf.get(n) match
          case Some(r) => out += BodyOp.Test(CmpOp.Eq, Expr.Reg(r), Expr.Reg(y))
          case None => regOf(n) = y
      case Term.Lit(l) => out += BodyOp.Test(CmpOp.Eq, Expr.Reg(y), Expr.Const(lit(l)))
      case Term.App(RelRef.Sym(c), as) =>
        val (binds, checks, nested) = columns(as)
        out += BodyOp.Deref(y, c.tag, binds, checks)
        nested.foreach((t2, r) => matchReg(t2, r, out))
      case Term.As(x, v) =>
        regOf.get(v) match
          case Some(r) => out += BodyOp.Test(CmpOp.Eq, Expr.Reg(r), Expr.Reg(y))
          case None => regOf(v) = y
        matchReg(x, y, out)
      case Term.Ascr(x, tp) =>
        out += BodyOp.Tag(y, tags(tp))
        matchReg(x, y, out)
      case other =>
        out += BodyOp.Test(CmpOp.Eq, Expr.Reg(y), expr(other))

    /** Column constraints of an atom: bindings `k := r`, checks `k == e`, and nested patterns. Checks are
     *  evaluated before the bindings of the same atom, so a column that depends on a variable bound by an
     *  earlier column of this atom (`p X X`, `p X (X + 1)`) is bound and then matched as a nested pattern. */
    def columns(args: List[Term]): (Array[(Int, Int)], Array[(Int, Expr)], List[(Term, Int)]) =
      val binds = mutable.ArrayBuffer.empty[(Int, Int)]
      val checks = mutable.ArrayBuffer.empty[(Int, Expr)]
      val nested = mutable.ListBuffer.empty[(Term, Int)]
      val local = mutable.Set.empty[String]
      def dependsOnLocal(t: Term) = Moding.vars(t).exists(local)
      for (a, k) <- args.zipWithIndex do
        a match
          case Term.Var(n) if local(n) =>
            val r = fresh()
            binds += ((k, r))
            nested += ((a, r))
          case Term.Var(n) =>
            regOf.get(n) match
              case Some(r) => checks += ((k, Expr.Reg(r)))
              case None =>
                val r = fresh()
                regOf(n) = r
                local += n
                binds += ((k, r))
          case Term.Lit(l) => checks += ((k, Expr.Const(lit(l))))
          case _: Term.Arith | _: Term.Neg if !dependsOnLocal(a) => checks += ((k, expr(a)))
          case other =>
            // nested patterns, `as` and ascriptions: bind the column, then match against it
            val r = fresh()
            binds += ((k, r))
            nested += ((other, r))
      (binds.toArray, checks.toArray, nested.toList)

    def atom(a: Formula.Atom, out: mutable.ListBuffer[BodyOp], versioned: Boolean): Unit =
      val c = a.rel.sym
      a.as.flatMap(regOf.get) match
        case Some(src) =>
          val (binds, checks, nested) = columns(a.args)
          out += BodyOp.Deref(src, c.tag, binds, checks)
          nested.foreach((t, r) => matchReg(t, r, out))
        case None =>
          val asReg = a.as.map { v =>
            val r = fresh(); regOf(v) = r; r
          }.getOrElse(-1)
          val (binds, checks, nested) = columns(a.args)
          val recIdx =
            if versioned && currentComp.isDefined && compOf.get(c) == currentComp then { recAtoms += 1; recAtoms - 1 }
            else -1
          if checks.nonEmpty then indexes.getOrElseUpdate(c.tag, mutable.Set.empty) += checks.map(_._1).toVector.sorted
          out += BodyOp.Scan(c.tag, recIdx, asReg, binds, checks.sortBy(_._1))
          nested.foreach((t, r) => matchReg(t, r, out))

    def formula(f: Formula, out: mutable.ListBuffer[BodyOp], versioned: Boolean): Unit = f match
      case a: Formula.Atom => atom(a, out, versioned)
      case Formula.Cmp(CmpOp.Eq, l, r) if !(isBound(l) && isBound(r)) =>
        val (pat, value) = if isBound(r) then (l, r) else (r, l)
        operand(value, out) match
          case Expr.Reg(y) if !value.isInstanceOf[Term.Var] => matchReg(pat, y, out)
          case e =>
            val y = fresh()
            out += BodyOp.Eval(y, e)
            matchReg(pat, y, out)
      case Formula.Cmp(op, l, r) =>
        val a = operand(l, out)
        val b = operand(r, out)
        out += BodyOp.Test(op, a, b)
      case Formula.Not(a) =>
        val saved = regOf.clone()
        val inner = mutable.ListBuffer.empty[BodyOp]
        atom(a, inner, versioned = false)
        regOf.clear(); regOf ++= saved
        out += BodyOp.NotIn(inner.toArray)
      case Formula.Agg(res, k, t, b) =>
        val saved = regOf.clone()
        val inner = mutable.ListBuffer.empty[BodyOp]
        val ordered = Moding.canonical(b, regOf.keySet.toSet).map(_._1).getOrElse(b)
        ordered.foreach(formula(_, inner, versioned = false))
        val locals = (regOf.keySet.toSet -- saved.keySet).toList.sorted.map(regOf).toArray
        val te = expr(t)
        regOf.clear(); regOf ++= saved
        regOf.get(res) match
          case Some(r) =>
            val y = fresh()
            out += BodyOp.Agg(y, k, te, locals, inner.toArray)
            out += BodyOp.Test(CmpOp.Eq, Expr.Reg(r), Expr.Reg(y))
          case None =>
            val y = fresh()
            regOf(res) = y
            out += BodyOp.Agg(y, k, te, locals, inner.toArray)
      case other => throw IllegalStateException(s"cannot lower formula ${ObjPrinter.formula(other)}")

    def body(b: List[Formula], versioned: Boolean): Array[BodyOp] =
      val ordered = Moding.canonical(b, Set.empty).map(_._1).getOrElse(b)
      val out = mutable.ListBuffer.empty[BodyOp]
      ordered.foreach(formula(_, out, versioned))
      out.toArray

  def lowerRule(r: Rule): CompiledRule =
    val Term.App(RelRef.Sym(h), hargs) = r.heads.head: @unchecked
    val rc = RuleCompiler(compOf.get(h))
    val body = rc.body(r.body, versioned = true)
    val head = hargs.map(rc.expr).toArray
    CompiledRule(r, rc.nregs, body, h.tag, head, rc.recAtoms)

  def lowerQuery(q: Query): CompiledQuery =
    val alts = q.body match
      case List(Formula.Disj(as)) => as
      case b => List(b)
    def userVars(b: List[Formula]): Set[String] = b.flatMap {
      case Formula.Not(_) => Nil
      case Formula.Agg(res, _, _, _) => List(res)
      case Formula.Disj(as) => as.flatMap(x => userVars(x))
      case f => Moding.formulaVars(f)
    }.toSet.filter(v => !v.contains('#') && !v.contains('.'))
    val vars = alts.map(userVars).reduce(_ intersect _).toList.sortBy(v => firstOccurrence(q, v))
    var nregs = 0
    val compiled = alts.map { b =>
      val rc = RuleCompiler(None)
      val ops = rc.body(b, versioned = false)
      nregs = nregs.max(rc.nregs)
      (ops, vars.map(rc.regOf).toArray)
    }
    CompiledQuery(q, nregs, compiled.map(_._1).toArray, vars, compiled.map(_._2).toArray)

  private def firstOccurrence(q: Query, v: String): Int =
    val s = ObjPrinter.query(q)
    val i = ("\\b" + java.util.regex.Pattern.quote(v) + "\\b").r.findFirstMatchIn(s).map(_.start).getOrElse(Int.MaxValue)
    i

/** Phase: compile to the core IR. */
final class LowerPhase extends Phase:
  def phaseName = "lower"
  def description = "compile core rules to the IR of Section 9.3"
  override def runsAfterErrors: Boolean = false
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    p.rels.zipWithIndex.foreach((r, i) => r.tag = i)
    val ops = TypeOps(p)
    val low = Lowering(p, ops)
    val rules = p.rules.map(low.lowerRule)
    val queries = p.queries.map(low.lowerQuery)
    val comps = ctx.unit.components.map(_.map(_.tag).toVector).toVector
    ctx.unit.core = CoreProgram(p.rels, comps, rules, queries, low.indexes.view.mapValues(_.toSet).toMap)
  override def show(using Context): String = IRPrinter.show(ctx.unit.core.nn)
