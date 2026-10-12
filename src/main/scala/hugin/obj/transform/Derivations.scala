package hugin.obj
package transform

import hugin.compiler.*
import scala.collection.mutable

/** A proof relation of `--export-proofs`: the instances of the head `head` of `rule` are recorded in `rel`
 *  (columns: the derived fact, then [[RelSym.premises]]). */
final case class ProofRule(rel: RelSym, rule: Rule, head: Term)

/** Section 7.4: derivation relations for rules under `%derivations`, and with `--export-proofs` the proof
 *  relations of the rules in the exported fragment ([[ProofFragment]]). */
final class DerivationsPhase extends ObjProgramPhase:
  def phaseName = "derivations"
  def description = "introduce derivation relations (Section 7.4)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val proofs = if ctx.settings.exportProofs || ctx.settings.certify then proofRelations(p) else Vector.empty
    val names = ctx.unit.derivationRules
    val facts = ctx.unit.facts
    def baseName(n: String): String = n.indexOf('[') match
      case -1 => n
      case i => n.substring(0, i)
    def wanted(r: Rule): Boolean = r.name.exists { n =>
      !n.endsWith("^d") && (names.contains(baseName(n)) || r.heads.exists {
        case Term.App(RelRef.Sym(c), _) => facts(c).derivations
        case _ => false
      })
    }
    val groups = p.rules.filter(wanted).groupBy(_.name.get)
    // by identity: two rules may be equal (spans are not part of a rule's equality) and still each get
    // their own derivation relation
    val replaced = java.util.IdentityHashMap[Rule, List[Rule]]()
    val newRels = mutable.ArrayBuffer.empty[RelSym]
    for (name, rs) <- groups.toList.sortBy(_._1); (r, i) <- rs.zipWithIndex do
      val rn = if rs.length == 1 then s"@$name" else s"@$name#${i + 1}"
      val d = RelSym(rn, RelKind.Derivation(name), r.span, r.origin)
      val (body, r2) = DerivationsPhase.instances(r, r.heads.head, d, Some(rn), comparisons = false)
      ctx.unit.facts = ctx.unit.facts.updated(d)(_.copy(output = true))
      newRels += d
      val r1 = r.withParts(body = body)
      DerivationsPhase.copyTypes(r, r1)
      replaced.put(r, List(r1, r2))
    p.rules = p.rules.flatMap(r => Option(replaced.get(r)).getOrElse(List(r))) ++ proofs.map(_._2)
    p.rels = p.rels ++ newRels ++ proofs.map(_._1.rel)
    ctx.unit.proofRules = proofs.map(_._1)

  /** The proof relation and its rule for every head of every rule in the exported fragment; the other
   *  rules are recorded in `proofOmitted`. */
  private def proofRelations(p: ObjProgram)(using Context): Vector[(ProofRule, Rule)] =
    val omitted = mutable.ArrayBuffer.empty[(Rule, String)]
    val out = mutable.ArrayBuffer.empty[(ProofRule, Rule)]
    for r <- p.rules; h <- r.heads do
      ProofFragment.outside(r, h) match
        case Some(reason) => if !omitted.exists(_._1 eq r) then omitted += ((r, reason))
        case None =>
          val d = RelSym(s"proof#${out.length + 1}", RelKind.Proof, r.span, r.origin)
          val (_, rule) = DerivationsPhase.instances(r, h, d, None, comparisons = true)
          out += ((ProofRule(d, r, h), rule))
    ctx.unit.proofOmitted = omitted.toVector
    out.toVector

object DerivationsPhase:
  /** The body of `r` with every positive atom bound to a variable (`as`), and the rule that derives into
   *  `d` the instances of `r`'s head `head`: the derived fact, the identities of the positive premises,
   *  the values of the variables of each negated atom that the rest of the body binds, and with
   *  `comparisons` the values of the variables of each comparison. Fills in `d`'s columns and premises. */
  def instances(r: Rule, head: Term, d: RelSym, name: Option[String], comparisons: Boolean)(using Context): (List[Formula], Rule) =
    val Term.App(RelRef.Sym(c), _) = head: @unchecked
    val types = Option(ctx.unit.varTypes.get(r)).getOrElse(Map.empty)
    val outer = r.body.flatMap {
      case Formula.Atom(_, args, as) => args.flatMap(vars) ++ as
      case Formula.Cmp(_, l, rt) => vars(l) ++ vars(rt)
      case Formula.Agg(res, _, _, _) => List(res)
      case _ => Nil
    }.toSet
    var k = 0
    val premises = mutable.ListBuffer.empty[(Premise, List[Term])]
    val body = r.body.map {
      case a @ Formula.Atom(RelRef.Sym(rel), args, as) =>
        k += 1
        val v = as.getOrElse(s"I#$k")
        premises += ((Premise.Pos(rel), List(Term.Var(v)(r.span))))
        Formula.Atom(RelRef.Sym(rel), args, Some(v))(a.span)
      case f @ Formula.Not(a) =>
        val vs = a.args.flatMap(vars).distinct.filter(outer)
        premises += ((Premise.Neg(a, vs), vs.map(Term.Var(_)(r.span))))
        f
      case f: Formula.Cmp if comparisons =>
        val vs = (vars(f.l) ++ vars(f.r)).distinct
        premises += ((Premise.Cmp(f, vs), vs.map(Term.Var(_)(r.span))))
        f
      case other => other
    }
    d.premises = premises.map(_._1).toVector
    d.cols = (Column(None, OType.Fact(c, Nil)) +: d.premises.flatMap {
      case Premise.Pos(rel) => Vector(Column(None, OType.Fact(rel, Nil)))
      case Premise.Neg(_, vs) => vs.map(v => Column(None, types.getOrElse(v, OType.Err)))
      case Premise.Cmp(_, vs) => vs.map(v => Column(None, types.getOrElse(v, OType.Err)))
    })
    val dh = Term.App(RelRef.Sym(d), head :: premises.toList.flatMap(_._2))(r.span)
    val rule = Rule(name, List(dh), body)(r.span, r.origin, r.expansions)
    copyTypes(r, rule)
    (body, rule)

  /** The variables of a term, in order of occurrence. */
  def vars(t: Term): List[String] = t match
    case Term.Var(n) => List(n)
    case Term.Lit(_) => Nil
    case Term.App(_, as) => as.flatMap(vars)
    case Term.As(x, v) => v :: vars(x)
    case Term.Ascr(x, _) => vars(x)
    case Term.Proj(x, _) => vars(x)
    case Term.With(x, fs) => vars(x) ++ fs.flatMap(f => vars(f._2))
    case Term.Arith(_, l, r) => vars(l) ++ vars(r)
    case Term.Neg(x) => vars(x)

  def copyTypes(from: Rule, to: Rule)(using Context): Unit =
    Option(ctx.unit.varTypes.get(from)).foreach(ctx.unit.varTypes.put(to, _))

/** The fragment of the object language that `--export-proofs` exports as rules of Tantow et al.'s format
 *  (reference: object/io, "Proof export"): function-free Datalog whose atoms have variables and constants
 *  as arguments, with negated atoms and comparisons of variables and constants, both exported as atoms of
 *  assumption relations. */
object ProofFragment:
  /** A variable or a constant: a literal, a negated number literal or a constant of an open type. */
  def simple(t: Term): Boolean = t match
    case Term.Var(_) | Term.Lit(_) | Term.App(_, Nil) | Term.Neg(Term.Lit(_)) => true
    case _ => false

  /** Why the head `head` of `r` is outside the exported fragment, if it is. */
  def outside(r: Rule, head: Term): Option[String] = head match
    case Term.App(RelRef.Sym(c), args) =>
      if c.isDerivation then Some("it is a derivation rule")
      else if c.boundColumn.isDefined then Some(s"`${c.displayName}` has a bound column")
      else if !args.forall(simple) then Some("its head has an argument that is a constructor term or an expression")
      else r.body.iterator.map(reason).collectFirst { case Some(m) => m }
    case _ => Some("its head is not an atom")

  private def reason(f: Formula): Option[String] = f match
    case Formula.Atom(_, _, Some(_)) => Some("it binds the identity of a fact with `as`")
    case Formula.Atom(_, args, None) =>
      if args.forall(simple) then None else Some("a body atom has an argument that is a pattern or an expression")
    case Formula.Not(a) =>
      if a.as.isEmpty && a.args.forall(simple) then None
      else Some("a negated atom has an argument that is a pattern or an expression")
    case Formula.Cmp(_, l, r) =>
      if simple(l) && simple(r) then None else Some("a comparison has an argument that is a constructor term or an expression")
    case _: Formula.Agg => Some("it has an aggregate")
    case _: Formula.Disj => Some("it has a disjunction")
