package hugin.runtime

import hugin.compiler.{CompilationUnit, SourceLoader}
import hugin.core.{Core, Elim, Head, Icit, Stage, Val}
import hugin.ir.{CoreProgram, Id}
import hugin.obj.*
import hugin.obj.transform.ProofRule
import hugin.syntax.Literal
import hugin.util.{Diagnostic, Span}
import hugin.util.diagnostics.*
import scala.collection.mutable
import scala.language.implicitConversions

/** `--certify` (reference: std/certify; #186 P8b): a certified run. After the run, the program the engine
 *  ran, its input facts and its output with a derivation of every fact are reified as meta data, and the
 *  checker of `std/certify` is evaluated on them: `certifyPositive` for a program without negation,
 *  `certifyStrata` otherwise. The checker builds the derivation of every fact it accepts and checks that
 *  the facts are closed under the rules, so an accepted run reports exactly the least (perfect) model of
 *  the reified program from the reified input facts, without trusting the engine.
 *
 *  The program is reified from the rules the engine evaluated, as the proof export exports them
 *  ([[ProofExport]]): one rule per head, its variables numbered heads first, each typed by the column of
 *  its first positive occurrence (as the facts' values are), the local variables of a negated atom first.
 *  The relations are the relations of the rules and of the facts, in the order of their tags, and the
 *  strata are the engine's components. The certificate lists the input facts (the facts of input
 *  relations without a derivation), then the derived facts in the order the export settled them, with
 *  the positions of their positive premises; the stratified checker gets them stratum by stratum. The
 *  fragment is the proof export's: function-free rules with negated atoms and comparisons (E0956). */
object Certify:
  /** The diagnostics, and the summary line of an accepted run. */
  final case class Outcome(diagnostics: List[Diagnostic], summary: Option[String])

  val LibraryPath: String = SourceLoader.StdlibPrefix + "std/certify.hgn"

  def apply(unit: CompilationUnit, prog: CoreProgram, engine: Engine): Outcome =
    val elaborated = unit.elaborated
    val at = Span(unit.source, 0, 0)
    if elaborated == null || !unit.libraries.contains(LibraryPath) then
      return Outcome(List(CertifyProblem.NoLibrary(at).toDiagnostic), None)
    val omitted = unit.proofOmitted.toList.map((r, why) =>
      CertifyProblem.OutsideFragment(s"this rule is outside the certified fragment, because $why", r.span)
    )
    if omitted.nonEmpty then return Outcome(omitted.map(_.toDiagnostic), None)
    val core = elaborated.nn.core
    // the checker reads no declarations of the program that a later edit could change: no observer
    val observer = core.reads
    core.observe(null)
    try Reifier(unit, core, prog, engine).run()
    catch case Outside(why, span) => Outcome(List(CertifyProblem.OutsideFragment(why, if span.exists then span else at).toDiagnostic), None)
    finally core.observe(observer)

  /** A part of the run outside the certified fragment. */
  private final case class Outside(why: String, span: Span) extends Exception(why, null, false, false)

  private final class Reifier(unit: CompilationUnit, core: Core, prog: CoreProgram, engine: Engine):
    private val at = Span(unit.source, 0, 0)

    /** The globals of the libraries, by file and name. */
    private val byName: Map[(String, String), Int] =
      core.globals.indices.flatMap { i =>
        val g = core.globals(i)
        // the meta-level constants (the shared lists and options are also object constants)
        val meta = g.kind match
          case _: hugin.core.GlobalKind.Object | _: hugin.core.GlobalKind.Family => false
          case _ => true
        Option.when(meta && g.declSpan.exists)((g.declSpan.source.path, g.name) -> i)
      }.toMap

    private def global(file: String, name: String): Int =
      byName.getOrElse((SourceLoader.StdlibPrefix + file, name), throw IllegalStateException(s"no `$name` in $file"))

    private def certify(name: String): Val = core.globalValue(global("std/certify.hgn", name))
    private def semantics(name: String): Val = core.globalValue(global("std/semantics.hgn", name))
    private def reflect(name: String): Val = core.globalValue(global("std/reflect.hgn", name))
    private val natFamily = global("std/nat.hgn", "nat")

    private def app(f: Val, args: (Val, Icit)*): Val = args.foldLeft(f)((h, a) => core.app(h, a._1, a._2))
    private def expl(f: Val, args: Val*): Val = app(f, args.map(_ -> Icit.Expl)*)
    private def nat(n: Int): Val = Val.Nat(natFamily, BigInt(n))
    private def str(s: String): Val = Val.Lit(Literal.StrL(s), Stage.S1)

    private def list(elem: Val, xs: Seq[Val]): Val =
      xs.foldRight(app(reflect("nil"), elem -> Icit.Impl))((x, acc) =>
        app(reflect("cons"), elem -> Icit.Impl, x -> Icit.Expl, acc -> Icit.Expl)
      )

    private def listOf(elem: Val): Val = expl(reflect("list"), elem)
    private lazy val natT = core.globalValue(natFamily)
    private lazy val codeT = certify("codeType")

    // ------------------------------------------------------------------ values

    private def metaId(s: AnyRef, what: => String, span: Span): Int =
      val id = unit.objectGlobals.get(s)
      if id == null then throw Outside(s"$what has no meta-level constant", span)
      id

    /** The code of an object type. */
    private def typeCode(t: OType, span: Span): Val = t match
      case OType.Base(b) => Val.Quote(Val.Base(b, Stage.S0))
      case OType.Con(sym, _) => Val.Quote(Val.Rigid(Head.Glob(metaId(sym, s"the type `${sym.name}`", span)), Nil))
      case other => throw Outside(s"a value of the type `${other.show}` is not modelled", span)

    private def literalCode(l: Literal): Val = Val.Quote(Val.Lit(l, Stage.S0))

    private def constantCode(c: RelSym, span: Span): Val =
      Val.Quote(Val.Rigid(Head.Glob(metaId(c, s"the constant `${c.displayName}`", span)), Nil))

    /** The code of a value of the run. */
    private def wordCode(w: Any, span: Span): Val = w match
      case l: java.lang.Long => literalCode(Literal.IntL(l))
      case s: String => literalCode(Literal.StrL(s))
      case d: java.lang.Double => literalCode(Literal.FloatL(d))
      case Id(rel, n) if engine.store(rel).tuples(n).isEmpty => constantCode(engine.store(rel).sym, span)
      case other => throw Outside(s"the value `${engine.show(other)}` is a fact or an infinity, which are not modelled", span)

    private def value(ty: Val, code: Val): Val = app(semantics("v"), ty -> Icit.Impl, code -> Icit.Expl)

    // ------------------------------------------------------------------ the program

    private val proofRules = unit.proofRules

    private def relsOf(f: Formula): List[RelSym] = f match
      case Formula.Atom(r, _, _) => List(r.sym)
      case Formula.Not(a) => List(a.rel.sym)
      case _ => Nil

    private val derivations = ProofExport.derivations(unit, prog, engine)

    /** The relations: those of the rules and of the facts, by tag. */
    private val own: Vector[RelSym] =
      val ruleRels = proofRules.flatMap(pr => pr.rel.premises.collect { case Premise.Pos(r) => r } ++ pr.rule.body.flatMap(relsOf)) ++
        proofRules.collect { case ProofRule(_, _, Term.App(RelRef.Sym(c), _)) => c }
      val factRels = derivations.order.map(id => prog.rels(id.rel))
      (ruleRels ++ factRels).distinct.sortBy(prog.tag)

    private val ownIndex: Map[RelSym, Int] = own.zipWithIndex.toMap

    private def ownOf(r: RelSym, span: Span): Int =
      ownIndex.getOrElse(r, throw Outside(s"the relation `${r.displayName}` is not reified", span))

    private def isInput(r: RelSym): Boolean =
      val d = prog.directives(prog.tag(r))
      d.input || d.open

    private val strata: Vector[Vector[Int]] =
      prog.components.map(_.flatMap(t => ownIndex.get(prog.rels(t)))).filter(_.nonEmpty)

    private val stratumOf: Map[Int, Int] = (for (s, k) <- strata.zipWithIndex; i <- s yield i -> k).toMap

    private def cmpOp(op: CmpOp): Val = reflect(op match
      case CmpOp.Eq => "ceq"
      case CmpOp.Ne => "cne"
      case CmpOp.Lt => "clt"
      case CmpOp.Le => "cle"
      case CmpOp.Gt => "cgt"
      case CmpOp.Ge => "cge"
    )

    private def termVars(t: Term): List[String] = hugin.obj.transform.DerivationsPhase.vars(t)

    /** A rule's terms: a variable by its position in `vars`, a literal or a constant by its value. */
    private def uterm(t: Term, vars: Map[String, Int], span: Span): Val = t match
      case Term.Var(n) => expl(certify("uvar"), nat(vars(n)))
      case Term.Lit(l) => expl(certify("ucon"), value(typeCode(OType.Base(BaseType.of(l)), span), literalCode(l)))
      case Term.Neg(Term.Lit(Literal.IntL(n))) => expl(certify("ucon"), value(typeCode(OType.Int, span), literalCode(Literal.IntL(-n))))
      case Term.App(c, Nil) =>
        val ty = c.sym.result.getOrElse(throw Outside(s"`${c.sym.displayName}` is not a constant", span))
        expl(certify("ucon"), value(typeCode(ty, span), constantCode(c.sym, span)))
      case other => throw Outside(s"the term `${ObjPrinter.term(other)}` is not a variable or a constant", span)

    private def uatom(rel: RelSym, args: List[Term], vars: Map[String, Int], span: Span): Val =
      expl(certify("uat"), expl(semantics("own"), nat(ownOf(rel, span))), list(certify("uterm"), args.map(uterm(_, vars, span))))

    private def urule(pr: ProofRule, index: Int): Val =
      val r = pr.rule
      val span = r.span
      val Term.App(RelRef.Sym(head), headArgs) = pr.head: @unchecked
      val outer = r.body.flatMap {
        case Formula.Atom(_, args, _) => args.flatMap(termVars)
        case Formula.Cmp(_, l, rt) => termVars(l) ++ termVars(rt)
        case _ => Nil
      }.toSet
      val vars = (headArgs.flatMap(termVars) ++ r.body.flatMap {
        case Formula.Atom(_, args, _) => args.flatMap(termVars)
        case Formula.Cmp(_, l, rt) => termVars(l) ++ termVars(rt)
        case _ => Nil
      }).distinct
      val types = Option(unit.varTypes.get(r)).getOrElse(Map.empty)
      // the column of a variable's first positive occurrence, as the values of the facts are typed
      def columnOf(x: String): Option[OType] =
        r.body.iterator.collect { case Formula.Atom(RelRef.Sym(rel), args, _) => args.zip(rel.cols) }.flatten.collectFirst {
          case (Term.Var(`x`), col) => col.tpe
        }
      def typeOf(x: String): Val =
        typeCode(columnOf(x).orElse(types.get(x)).getOrElse(throw Outside(s"the variable `${Var.display(x)}` has no type", span)), span)
      val index0 = vars.zipWithIndex.toMap
      val body = r.body.map {
        case Formula.Atom(RelRef.Sym(rel), args, None) => expl(certify("upos"), uatom(rel, args, index0, span))
        case Formula.Cmp(op, l, rt) => expl(certify("ucmp"), cmpOp(op), uterm(l, index0, span), uterm(rt, index0, span))
        case Formula.Not(a) =>
          val locals = a.args.flatMap(termVars).distinct.filterNot(outer)
          val localTypes = locals.map { x =>
            a.args.zip(a.rel.sym.cols).collectFirst { case (Term.Var(`x`), col) => typeCode(col.tpe, span) }
              .getOrElse(throw Outside(s"the variable `${Var.display(x)}` has no type", span))
          }
          val inner = locals.zipWithIndex.toMap ++ index0.map((x, i) => x -> (i + locals.length))
          expl(certify("unot"), list(codeT, localTypes), uatom(a.rel.sym, a.args, inner, span))
        case other => throw Outside(s"the literal `${ObjPrinter.formula(other)}` is not modelled", span)
      }
      expl(
        certify("urul"),
        nat(ownOf(head, span)),
        nat(index),
        list(codeT, vars.map(typeOf)),
        list(certify("uatom"), List(uatom(head, headArgs, index0, span))),
        list(certify("ulit"), body)
      )

    private def uprogram: Val =
      val counts = mutable.HashMap.empty[RelSym, Int]
      val rules = proofRules.map { pr =>
        val Term.App(RelRef.Sym(head), _) = pr.head: @unchecked
        counts(head) = counts.getOrElse(head, 0) + 1
        urule(pr, counts(head))
      }
      expl(
        certify("uprog"),
        list(Val.Base(BaseType.StringT, Stage.S1), own.map(r => str(r.displayName))),
        list(certify("urule"), rules),
        list(natT, own.indices.filter(i => isInput(own(i))).map(nat)),
        list(listOf(natT), strata.map(s => list(natT, s.map(nat))))
      )

    // ------------------------------------------------------------------ the certificate

    private def gatom(id: Id): Val =
      val r = engine.store(id.rel)
      val span = r.sym.span
      val args = r.tuples(id.n).toList.zip(r.sym.cols).map((w, col) => value(typeCode(col.tpe, span), wordCode(w, span)))
      expl(semantics("atom"), expl(semantics("own"), nat(ownOf(r.sym, span))), list(semantics("value"), args))

    // ------------------------------------------------------------------ the run

    def run(): Outcome =
      val proof = derivations.proof
      val (leaves, derived) = derivations.order.partition(proof(_).isEmpty)
      val (inputs, assumed) = leaves.partition(id => isInput(prog.rels(id.rel)))
      assumed.headOption.foreach { id =>
        throw Outside(s"the fact `${engine.show(id)}` has no derivation by the rules", prog.rels(id.rel).span)
      }
      val stratified = proofRules.exists(_.rule.body.exists(_.isInstanceOf[Formula.Not]))
      val blocks: Vector[Vector[Id]] =
        if stratified then strata.indices.toVector.map(k => derived.filter(id => stratumOf(ownOf(prog.rels(id.rel), at)) == k))
        else Vector(derived)
      val inputIndex = inputs.zipWithIndex.toMap
      val pushIndex = blocks.flatten.zipWithIndex.toMap
      def cfact(id: Id): Val =
        val j = pushIndex(id)
        val offsets = proof(id).get.facts.map { c =>
          inputIndex.get(c).map(_ + j).getOrElse {
            val jc = pushIndex(c)
            if jc >= j then throw IllegalStateException(s"premise ${engine.show(c)} after ${engine.show(id)}")
            j - 1 - jc
          }
        }
        expl(certify("cf"), gatom(id), list(natT, offsets.map(nat)))
      val cfactT = certify("cfact")
      val ins = list(semantics("gatom"), inputs.map(gatom))
      val verdict =
        if stratified then expl(certify("certifyStrata"), uprogram, ins, list(listOf(cfactT), blocks.map(b => list(cfactT, b.map(cfact)))))
        else expl(certify("certifyPositive"), uprogram, ins, list(cfactT, blocks.flatten.map(cfact)))
      val total = inputs.length + derived.length
      core.force(verdict) match
        case Val.Rigid(Head.Glob(c), List(Elim.EApp(n, _))) if c == global("std/certify.hgn", "accepted") =>
          val model = if stratified then "the perfect model" else "the least model"
          Outcome(
            Nil,
            Some(
              s"certified: the $total facts of the run are $model of the program (${proofRules.length} rules, ${strata.length} strata) from its ${inputs.length} input facts"
            )
          )
        case Val.Rigid(Head.Glob(c), List(Elim.EApp(f, _))) if c == global("std/certify.hgn", "rejected") =>
          val (reason, span) = failure(f)
          Outcome(List(CertifyProblem.Rejected(reason, if span.exists then span else at).toDiagnostic), None)
        case other => throw IllegalStateException(s"the checker of std/certify is stuck: ${core.quote(0, other)}")

    /** What a failure of the checker says, and the declaration of the relation of the fact it names. */
    private def failure(f: Val): (String, Span) = core.force(f) match
      case Val.Rigid(Head.Glob(c), sp) =>
        core.globals(c).name match
          case "badProgram" => ("the reified program is not well typed (a comparison of values of two types)", at)
          case "badShape" => ("the certificate does not have a part for every stratum", at)
          case "badInput" =>
            val (fact, span) = showAtom(sp)
            (s"the input fact `$fact` is not of an input relation", span)
          case "badFact" =>
            val (fact, span) = showAtom(sp)
            (s"`$fact` is not derived by a rule from the facts given as its premises", span)
          case "notClosed" => ("the facts are not closed under the rules: a rule derives a fact that the run does not report", at)
          case other => (other, at)
      case other => (core.quote(0, other).toString, at)

    /** A fact of a failure, as the run prints it, and the declaration of its relation. */
    private def showAtom(sp: List[Elim]): (String, Span) =
      def code(v: Val): String = core.force(v) match
        case Val.Quote(c) =>
          core.force(c) match
            case Val.Lit(l, _) => l.show
            case Val.Rigid(Head.Glob(id), Nil) => core.globals(id).name
            case other => core.quote(0, other).toString
        case other => core.quote(0, other).toString
      def values(v: Val): List[String] = core.force(v) match
        case Val.Rigid(_, List(Elim.EApp(rest, _), Elim.EApp(x, _), _*)) =>
          core.force(x) match
            case Val.Rigid(_, Elim.EApp(c, _) :: _) => code(c) :: values(rest)
            case _ => values(rest)
        case _ => Nil
      def relation(r: Val): Option[RelSym] = core.force(r) match
        case Val.Rigid(_, List(Elim.EApp(i, _))) =>
          core.force(i) match
            case Val.Nat(_, n) if n < own.length => Some(own(n.toInt))
            case _ => None
        case _ => None
      sp match
        case List(Elim.EApp(a, _)) =>
          core.force(a) match
            case Val.Rigid(_, List(Elim.EApp(vs, _), Elim.EApp(r, _))) =>
              val rel = relation(r)
              ((rel.fold("?")(_.displayName) :: values(vs)).mkString(" "), rel.fold(at)(_.span))
            case other => (core.quote(0, other).toString, at)
        case _ => ("?", at)

/** The problems of `--certify` (reference: std/certify): `std/certify` is not loaded (E0955), a rule or a
 *  value of the run is outside the certified fragment (E0956), the checker rejects the run (E0957). */
enum CertifyProblem extends Problem:
  case NoLibrary(at: Span)
  case OutsideFragment(reason: String, at: Span)
  case Rejected(reason: String, at: Span)

  def code: Code = this match
    case _: NoLibrary => Code.E0955
    case _: OutsideFragment => Code.E0956
    case _: Rejected => Code.E0957

  def primary: Span = this match
    case NoLibrary(s) => s
    case OutsideFragment(_, s) => s
    case Rejected(_, s) => s

  def message: Msg = this match
    case _: NoLibrary => msg"`--certify` needs the library `std/certify`"
    case OutsideFragment(reason, _) => msg"cannot certify the run: " ++ Msg.text(reason)
    case Rejected(reason, _) => msg"the run is not certified: " ++ Msg.text(reason)

  override def notes: List[Msg] = this match
    case _: NoLibrary => List(msg"the checker of a certified run is the meta code of `std/certify`, which the program loads")
    case _: OutsideFragment =>
      List(msg"a certified run is checked for function-free rules with negated atoms and comparisons, the fragment of the proof export")
    case _: Rejected =>
      List(msg"the checker interprets the comparisons `<`, `<=`, `>`, `>=` on integers only; any other rejection is a fault of the engine")

  override def helps: List[Msg] = this match
    case _: NoLibrary => List(msg"add `%use \"std/certify\".` to the program")
    case _ => Nil
