package hugin.fuzz

import org.scalacheck.{Gen, Shrink}
import scala.collection.mutable
import scala.util.Random

/** A generated program, one item per line: declarations, base facts, rules and directives. `inputs` are
 *  the facts of the `%input` relations, given in a facts file. `derived` are the relations defined by
 *  rules (all of them `%output`). `demand` is a derived relation that no rule calls, which can be moded
 *  `+-…-` (`%demand`) and queried. */
final case class Generated(
    decls: Vector[String],
    facts: Vector[String],
    rules: Vector[String],
    inputs: Vector[String],
    derived: Vector[String],
    demand: Option[ProgramGen.Rel] = None
):
  // `len` is the relation of `std/list`
  def items: Vector[String] = ("%use \"std/list\"." +: decls) ++ facts ++ rules ++ derived.map(d => s"%output $d.")
  def code: String = items.mkString("\n") + "\n"
  def program: Program = Program(code, Option.when(inputs.nonEmpty)(inputs.mkString("\n") + "\n"))
  override def toString: String = program.toString

object Generated:
  /** Shrinking removes facts and rules (which keeps a program well-typed, well-moded and stratified). */
  given Shrink[Generated] = Shrink { g =>
    given Shrink[String] = Shrink.shrinkAny
    Shrink.shrink(g.rules).map(rs => g.copy(rules = rs)) #:::
      Shrink.shrink(g.facts).map(fs => g.copy(facts = fs)) #:::
      Shrink.shrink(g.inputs).map(is => g.copy(inputs = is))
  }

/** Generation of well-typed, well-moded, stratified and terminating programs (issue #7, part 2): a few
 *  base relations with facts (some as `%input`), then derived relations in strata. A rule of a derived
 *  relation uses positive atoms of earlier relations and of itself (recursion), negation and aggregates
 *  (with disjunctions inside) of earlier relations, comparisons, disjunctions of tests, arithmetic (outside
 *  recursion), constructors of a user type and of the prelude families `option` and `list`, `len` from
 *  the prelude, and a bounded counter with `%terminates`. Every head variable is bound by the body. */
object ProgramGen:
  enum Ty(val decl: String):
    case IntT extends Ty("int")
    case StrT extends Ty("string")
    case ColorT extends Ty("color")
    case OptT extends Ty("option int")
    case BoxT extends Ty("box")
    case ListT extends Ty("list int")

    /** Values of the fact constructor `pt` (`pt : int -> point.`), whose facts are base facts only.
     *  Not a column type: variables of this type are bound by binding equations `V = pt X` (existence
     *  checks) and compared structurally. */
    case PointT extends Ty("point")

  import Ty.*

  final case class Rel(name: String, cols: Vector[Ty])

  object Rel:
    /** The name of a column of a derived relation. */
    def column(i: Int): String = ('a' + i).toChar.toString

  /** A few values of a read type (for queries). */
  def values(t: Ty): Vector[String] = t match
    case IntT => Vector("0", "1", "2", "3", "4")
    case StrT => Vector("\"a\"", "\"b\"", "\"\"")
    case ColorT => Vector("red", "green", "blue")
    case ListT => Vector("nil", "(cons 0 nil)")
    case OptT | BoxT | PointT => Vector.empty

  /** Constructor facts of a type are either read or built by derived relations, never both: a rule that
   *  constructs `c` in its head is a dependency of every rule that matches `c` (Section 6.4), which would
   *  merge the relations into growing components (rejected by the termination check) or negation cycles.
   *  Facts of read types (`color`, `list int`) come from base facts and appear as constants and patterns in
   *  bodies; facts of built types (`option int`, `box`) are constructed in heads and only bound to
   *  variables in bodies. */
  def read(t: Ty): Boolean = t != OptT && t != BoxT

  val programs: Gen[Generated] = Gen.long.map(seed => Builder(Random(seed)).build())

  private final class Builder(rnd: Random):
    /** The derived relations that depend on `len` (call it, or read a relation that does). */
    private val lenDependent = mutable.Set.empty[String]

    private def chance(p: Double) = rnd.nextDouble() < p
    private def pick[A](xs: Seq[A]): A = xs(rnd.nextInt(xs.length))
    private def between(lo: Int, hi: Int) = lo + rnd.nextInt(hi - lo + 1)

    /** A column type, mostly `int` (for joins and arithmetic). */
    private def ty(): Ty = pick(Seq.fill(6)(IntT) ++ Seq(StrT, ColorT, ColorT, OptT, BoxT, ListT))

    private def int(): String = if chance(0.1) then s"(-${between(1, 3)})" else between(0, 4).toString

    private def list(n: Int): String = if n == 0 then "nil" else s"(cons ${between(0, 3)} ${list(n - 1)})"

    private def const(t: Ty): String = t match
      case IntT => int()
      case StrT => pick(Seq("\"a\"", "\"b\"", "\"c\"", "\"\""))
      case ColorT => pick(Seq("red", "green", "blue"))
      case OptT => if chance(0.3) then "none" else s"(some ${int()})"
      case BoxT => s"(mk ${int()})"
      case ListT => list(between(0, 3))
      case PointT => s"(pt ${int()})"

    private def atom(r: Rel, args: Seq[String]) = (r.name +: args).mkString(" ")

    def build(): Generated =
      val decls = mutable.ArrayBuffer(
        "color : type.",
        "red : color.",
        "green : color.",
        "blue : color.",
        "box : type.",
        "mk : int -> box.",
        "point : type.",
        "pt : int -> point."
      )
      val facts = mutable.ArrayBuffer.empty[String]
      for _ <- 0 until between(0, 3) do facts += s"pt ${int()}."
      val inputs = mutable.ArrayBuffer.empty[String]
      val rules = mutable.ArrayBuffer.empty[String]
      def declare(r: Rel, named: Boolean) =
        val cols = r.cols.zipWithIndex.map((t, i) => if named then s"(${Rel.column(i)} : ${t.decl})" else t.decl)
        decls += s"${r.name} : ${(cols :+ "rel").mkString(" -> ")}."

      val base = Vector.tabulate(between(1, 3))(i => Rel(s"e$i", Vector.fill(between(1, 3))(ty())))
      for r <- base do
        declare(r, named = false)
        val input = chance(0.3)
        if input then decls += s"%input ${r.name}."
        for _ <- 0 until between(1, 8) do (if input then inputs else facts) += atom(r, r.cols.map(const)) + "."

      val derived = mutable.ArrayBuffer.empty[Rel]
      var demand = Option.empty[Rel]
      for i <- 0 until between(1, 4) do
        // the heads of a recursive relation construct only terms that take finitely many values: ground
        // terms (`none`, `mk 1`) or terms over variables bound by atoms of earlier relations (`some V`);
        // others are constructive (Definition 10.1 as refined in docs/NOTES.md) and the termination check
        // rejects the component without `%terminates`
        val recursive = chance(0.4)
        val lower = base ++ derived
        // a column of a read type needs a relation to read its values from
        def colTy(types: => Ty): Ty = Iterator.continually(types).find(t => !read(t) || lower.exists(_.cols.contains(t))).get
        val r = Rel(
          s"d$i",
          Vector.fill(between(1, 3))(if recursive then colTy(pick(Seq(IntT, IntT, IntT, StrT, ColorT, OptT, BoxT))) else colTy(ty()))
        )
        declare(r, named = true)
        val calls =
          for k <- 0 until between(1, 3) yield
            val self = recursive && k > 0 && chance(0.7)
            val rb = RuleBuilder(r, lower, recursive, self)
            val rule = rb.build()
            if rb.dependsOnLen(rule) then lenDependent += r.name
            rules += rule
            self
        derived += r
        demand = Option.when(!calls.contains(true))(r)

      if chance(0.3) then // a bounded integer counter (arithmetic in a recursive rule, checked by %terminates)
        val c = Rel("counter", Vector(IntT))
        declare(c, named = false)
        decls += "%terminates N (counter N)."
        facts += s"counter ${between(0, 2)}."
        rules += s"counter M :- counter N, N < ${between(0, 8)}, M = N + ${between(1, 2)}."
        derived += c
      if chance(0.4) then boundColumns(decls, facts, rules, derived)
      if chance(0.3) then existenceChain(decls, facts, rules, derived)
      Generated(decls.toVector, facts.toVector, rules.toVector, inputs.toVector, derived.map(_.name).toVector, demand)

    /** Recursive existence checks (issue #83): `xr N` holds for the steps `xs M N` whose source `some M`
     *  is a fact, and `xm (some N)` builds `some N` for every `xr N`, so `xr` and `some[int]` form one
     *  component and the check `_X = some M` is a recursive read. Nothing else reads `xr` or `xm`, and
     *  no other rule checks `some`, so no negation or aggregate joins the component. */
    private def existenceChain(
        decls: mutable.ArrayBuffer[String],
        facts: mutable.ArrayBuffer[String],
        rules: mutable.ArrayBuffer[String],
        derived: mutable.ArrayBuffer[Rel]
    ): Unit =
      decls ++= Seq("xs : int -> int -> rel.", "xr : int -> rel.", "xm : option int -> rel.")
      for _ <- 0 until between(1, 6) do facts += s"xs ${between(0, 4)} ${between(0, 4)}."
      facts += s"xm (some ${between(0, 4)})."
      rules += "xr N :- xs M N, _X = some M."
      rules += "xm (some N) :- xr N."
      derived += Rel("xr", Vector(IntT)) += Rel("xm", Vector(OptT))

    /** Relations with bound columns (reference: object/bound-columns) over a small weighted graph `wg` with seeds
     *  `ws`: `w0` keeps the best value per node (`min` or `max`), propagated along edges by type-consistent
     *  rules (a positive multiple of the value plus the weight, guards in the improving direction), so
     *  cycles may diverge to `∞`; sometimes `w1` of the other kind mirrors `w0` with a negative
     *  coefficient (the two feed each other); `wr` reads `w0` from a later component as plain values. */
    private def boundColumns(
        decls: mutable.ArrayBuffer[String],
        facts: mutable.ArrayBuffer[String],
        rules: mutable.ArrayBuffer[String],
        derived: mutable.ArrayBuffer[Rel]
    ): Unit =
      val min = chance(0.5)
      val (kind, other) = if min then ("min", "max") else ("max", "min")
      decls ++= Seq("wg : int -> int -> int -> rel.", "ws : int -> int -> rel.", s"w0 : (a : int) -> (b : $kind int) -> rel.")
      for _ <- 0 until between(1, 6) do facts += s"wg ${between(0, 4)} ${between(0, 4)} ${int()}."
      for _ <- 0 until between(1, 2) do facts += s"ws ${between(0, 4)} ${int()}."
      rules += "w0 K V :- ws K V."
      for _ <- 0 until between(1, 2) do
        val scale = if chance(0.2) then "2 * " else ""
        // a guard keeps the comparison true when the value improves: `V <= c` for `min`, `V >= c` for `max`
        val guard = if !chance(0.4) then "" else if min then s", V <= ${between(0, 6)}" else s", V >= ${int()}"
        rules += s"w0 L (${scale}V + C) :- w0 K V, wg K L C$guard."
      if chance(0.3) then
        decls += s"w1 : (a : int) -> (b : $other int) -> rel."
        rules += "w1 K (0 - V) :- w0 K V."
        rules += s"w0 K (${int()} - V) :- w1 K V."
        derived += Rel("w1", Vector(IntT, IntT))
      decls += "wr : int -> int -> rel."
      rules += s"wr K V :- w0 K V, V ${if min then "<" else ">"} ${int()}."
      derived += Rel("w0", Vector(IntT, IntT)) += Rel("wr", Vector(IntT, IntT))

    /** One rule of `head`; positive atoms over `lower` (and `head` if `recursive`), negation and aggregates
     *  over `lower` only. In the rules of a relation with recursive rules (`inRecursion`), heads compute
     *  nothing and construct terms only over variables bound by atoms of `lower` (the termination check
     *  rejects growing components without `%terminates`). */
    private final class RuleBuilder(head: Rel, lower: Vector[Rel], inRecursion: Boolean, recursive: Boolean):
      /** Whether the rule depends on `len`: it calls it, or mentions a relation that does. */
      def dependsOnLen(rule: String): Boolean =
        rule.contains(" len ") || raw"\b(d\d+)\b".r.findAllIn(rule).exists(lenDependent)

      private val bound = mutable.LinkedHashMap.empty[String, Ty]
      private var fresh = 0
      private def newVar(): String = { fresh += 1; s"V$fresh" }
      private def boundOf(t: Ty): Vector[String] = bound.collect { case (v, `t`) => v }.toVector
      private def bind(t: Ty): String = { val v = newVar(); bound(v) = t; v }

      /** An argument of a positive atom of type `t`; may bind new variables. */
      private def arg(t: Ty): String =
        val r = rnd.nextDouble()
        val old = boundOf(t)
        if old.nonEmpty && r < 0.35 then pick(old)
        else if r < 0.6 then bind(t)
        else if r < 0.72 then "_"
        else if r < 0.85 then pattern(t)
        else if t == ListT then if chance(0.5) then s"(cons ${arg(IntT)} ${arg(ListT)})" else "nil"
        else bind(t)

      /** A constant in a body: of a read type, otherwise `_`. */
      private def pattern(t: Ty): String = if read(t) then const(t) else "_"

      /** An argument of a negated atom or a test: bound variables, constants, `_`. */
      private def closedArg(t: Ty): String =
        val old = boundOf(t)
        if old.nonEmpty && chance(0.5) then pick(old) else if chance(0.5) then "_" else pattern(t)

      /** Variables that occur in positive atoms of `lower` relations (bound without the recursion). */
      private val lowerVars = mutable.HashSet.empty[String]

      /** A rule may call `len` (the prelude's, which measures the lists that are facts) on a list of a
       *  relation it reads; negations and aggregates in it often read relations that depend on `len`. */
      private val callsLen = !recursive && chance(0.4) && lower.exists(_.cols.contains(ListT))
      private val readable: Vector[Rel] = lower

      private def positive(): String =
        val r = if recursive && chance(0.5) then head else pick(readable)
        val a = atom(r, r.cols.map(arg))
        if r != head then lowerVars ++= raw"V\d+".r.findAllIn(a)
        a

      /** The `color` and `list int` variables of the rule equated with a constant, and the constant. */
      private val fixed = mutable.Map.empty[String, String]

      private def comparison(): Option[String] =
        val ints = boundOf(IntT)
        val others = Seq(StrT, ColorT, ListT, PointT).flatMap(t => boundOf(t).map(_ -> t))
        if ints.nonEmpty && (others.isEmpty || chance(0.7)) then
          val op = pick(Seq("<", "<=", ">", ">=", "=", "<>"))
          val rhs = if ints.length > 1 && chance(0.4) then pick(ints) else int()
          Some(s"${pick(ints)} $op $rhs")
        else if others.nonEmpty then
          val (v, t) = pick(others)
          val same = boundOf(t).filter(_ != v)
          // an equation narrows the variable's type to the constant's fact type (reference: object/types),
          // so a variable equated with two constants of different constructors (`red` and `green`, `nil`
          // and `cons 1 nil`), or two such variables equated with each other, would be a rule that never
          // fires (E0401): `fixed` remembers the constants
          val sameOk = if t == ColorT || t == ListT then same.filter(w => !(fixed.contains(v) && fixed.contains(w))) else same
          if sameOk.nonEmpty && chance(0.4) then
            val w = pick(sameOk)
            val op = pick(Seq("=", "<>"))
            if op == "=" && (t == ColorT || t == ListT) then fixed.get(v).orElse(fixed.get(w)).foreach(k => { fixed(v) = k; fixed(w) = k })
            Some(s"$v $op $w")
          // a constant that was never built differs from every value, also under `%demand`
          else if t == ListT then
            val op = pick(Seq("=", "<>"))
            val c = if op == "=" then fixed.getOrElseUpdate(v, const(t)) else const(t)
            val rhs = if c == "nil" && chance(0.3) then "(nil : list int)" else c
            Some(if chance(0.5) then s"$v $op $rhs" else s"$rhs $op $v")
          else if t == ColorT then
            val op = pick(Seq("=", "<>"))
            val k = if op == "=" then fixed.getOrElseUpdate(v, const(t)) else const(t)
            Some(s"$v $op $k")
          else Some(s"$v ${pick(Seq("=", "<>"))} ${const(t)}")
        else None

      /** A relation to negate or aggregate over: in a rule calling `len`, often one that depends on `len`
       *  (its demand then reads `len`'s answers through the negation or aggregate). */
      private def negated(rs: Vector[Rel]): Rel =
        val deps = rs.filter(r => lenDependent(r.name))
        if callsLen && deps.nonEmpty && chance(0.6) then pick(deps) else pick(rs)

      private def negation(): String =
        val r = negated(lower)
        "not " + atom(r, r.cols.map(closedArg))

      /** `N = agg { V | alternatives }`: each alternative binds `V` in an atom over `lower`, the others
       *  columns are outer variables (grouping), `_`, constants or local variables. */
      private def aggregate(): String =
        val withInt = lower.filter(_.cols.contains(IntT))
        val numeric = withInt.nonEmpty && chance(0.6)
        val vt = if numeric then IntT else negated(lower).cols.head
        val kind = if numeric then pick(Seq("count", "sum", "min", "max")) else if vt == StrT && chance(0.5) then "min" else "count"
        val v = newVar()
        // A disjunction with inputs (outer variables) becomes a moded auxiliary relation; its demand is
        // built from the formulas that do not depend on the rule's head. In a recursive rule an outer
        // variable bound only by the recursive atom would make the demand read the head: a cycle through
        // the aggregate (E0601, `tests/neg/f_aggregate_disjunction_cycle.hgn`).
        val n = if chance(0.3) then 2 else 1
        def outer(v: String) = !(recursive && n > 1) || lowerVars(v)
        def alternative(): String =
          val r = negated(lower.filter(_.cols.contains(vt)))
          val at = between(0, r.cols.length - 1)
          val col = r.cols.indexOf(vt, at) match
            case -1 => r.cols.indexOf(vt)
            case c => c
          val args = r.cols.zipWithIndex.map { (t, c) =>
            if c == col then v
            else
              val old = boundOf(t).filter(outer)
              if old.nonEmpty && chance(0.3) then pick(old)
              else if chance(0.4) then "_"
              else if chance(0.4) then pattern(t)
              else newVar() // local to the aggregate
          }
          val a = atom(r, args)
          if vt == IntT && chance(0.25) then s"($a, $v ${pick(Seq("<", ">", "<>"))} ${int()})" else a
        val alts = List.fill(n)(alternative())
        val res = bind(if kind == "min" || kind == "max" then vt else IntT)
        s"$res = $kind { $v | ${alts.mkString(" ; ")} }"

      private def arithmetic(): Option[String] =
        val ints = boundOf(IntT)
        Option.when(ints.nonEmpty) {
          val rhs = if ints.length > 1 && chance(0.4) then pick(ints) else int()
          val e = s"${pick(ints)} ${pick(Seq("+", "-", "*"))} $rhs"
          s"${bind(IntT)} = $e"
        }

      /** A binding equation `V = c X`: an existence check (reference: object/facts), which holds if `c X`
       *  is a fact. Only constructors of read types (`cons X nil`) and `pt` (`V = pt X`): a check of a
       *  built type (`V = some X`) reads its facts, which heads of later relations build, so the rule's
       *  relation would depend on those relations, closing cycles through their negations and aggregates
       *  (E0601; issue #83). Recursive existence checks have their own shape ([[existenceChain]]). In a
       *  recursive relation the term's variables come from atoms of `lower`. */
      private def equation(): Option[String] =
        val ints = boundOf(IntT).filter(v => !inRecursion || lowerVars(v))
        Option.when(ints.nonEmpty) {
          val x = pick(ints)
          if chance(0.5) then s"${bind(ListT)} = cons $x nil" else s"${bind(PointT)} = pt $x"
        }

      private def disjunction(): Option[String] =
        val ints = boundOf(IntT)
        val colors = boundOf(ColorT)
        if ints.nonEmpty then Some(s"(${pick(ints)} < ${int()} ; ${pick(ints)} = ${int()})")
        else if colors.nonEmpty then
          val c = pick(colors)
          Some(s"($c = ${const(ColorT)} ; $c = ${const(ColorT)})")
        else None

      private def length(): Option[String] =
        val lists = boundOf(ListT)
        Option.when(callsLen && lists.nonEmpty) {
          s"len ${pick(lists)} ${bind(IntT)}"
        }

      def build(): String =
        val body = mutable.ArrayBuffer.empty[String]
        for _ <- 0 until between(1, 3) do body += positive()
        if recursive && !body.exists(_.startsWith(head.name + " ")) then body += atom(head, head.cols.map(arg))
        for _ <- 0 until between(0, 3) do
          rnd.nextInt(8) match
            case 0 => body ++= comparison()
            case 1 => body += negation()
            case 2 => body += aggregate()
            case 3 => if !inRecursion then body ++= arithmetic()
            case 4 => body ++= disjunction()
            case 5 => body ++= length()
            case 6 => body ++= equation()
            case _ => body ++= comparison()
        // a rule that may call `len` often calls it after a negation or an aggregate (over a relation that
        // may depend on `len`), whose demand then reads the negation or the aggregate
        if callsLen && chance(0.6) then
          if chance(0.6) then body += (if chance(0.5) then negation() else aggregate())
          body ++= length()
        // values of read types in the head come from the body
        for t <- head.cols.distinct if read(t) && t != IntT && t != StrT && boundOf(t).isEmpty do
          val r = pick(readable.filter(_.cols.contains(t)))
          val at = r.cols.indexOf(t)
          body += atom(r, r.cols.zipWithIndex.map((u, c) => if c == at then bind(u) else arg(u)))
        val args = head.cols.map { t =>
          val old = boundOf(t)
          // a constructor term over a variable bound only through the recursion (or computed) can grow
          val ints = boundOf(IntT).filter(v => !inRecursion || lowerVars(v))
          if t == OptT && ints.nonEmpty && chance(0.3) then s"(some ${pick(ints)})"
          else if t == BoxT && ints.nonEmpty && chance(0.3) then s"(mk ${pick(ints)})"
          else if old.nonEmpty && (t == ColorT || t == ListT || chance(0.9)) then pick(old)
          else const(t)
        }
        s"${atom(head, args)} :- ${body.mkString(", ")}."
