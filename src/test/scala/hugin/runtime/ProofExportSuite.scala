package hugin.runtime

import com.google.gson.{JsonElement, JsonObject, JsonParser}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The proofs exported by `--export-proofs` (reference: object/io, "Proof export"), checked on the goldens
 *  `tests/proofs/X.json` (written by `GoldenTests`):
 *
 *  - against the JSON schema of the format, `reference/src/object/proof-export.schema.json`, derived from
 *    the Lean structures of Tantow et al.'s checker (`knowsys/CertifyingDatalog` v0.2.0, `Parsing.lean`);
 *  - by a model of that checker: the relation symbols and arities that its parser requires, the proof
 *    validity of `checkTreeListValidityWithUnivDatabase` / `checkOrderedGraphValidityWithUnivDatabase`
 *    (every node with children is an instance of a rule, with the children in the order of the body), and
 *    the model check of its option `-c` (the facts of the proofs satisfy every rule);
 *  - and beyond the checker: every leaf is a fact stated by a rule without body, an assumed fact, or an
 *    atom of an assumption relation that holds in the run (no fact matches a negated atom, a comparison is
 *    true). */
class ProofExportSuite extends munit.FunSuite:
  private val schema = parse(Path.of("reference/src/object/proof-export.schema.json"))

  private val goldens: List[Path] =
    Files.list(Path.of("tests/proofs")).iterator.asScala.filter(_.toString.endsWith(".json")).toList.sortBy(_.toString)

  private def parse(p: Path): JsonObject = JsonParser.parseString(Files.readString(p)).getAsJsonObject

  test("there are goldens with proof trees, with an ordered proof graph, with negation and with omitted rules") {
    val all = goldens.map(parse)
    assert(all.exists(_.has("trees")) && all.exists(_.has("graph")), goldens)
    assert(all.exists(j => assumptionSymbols(j).exists(_.startsWith("not "))), "no golden with a negated atom")
    assert(all.exists(_.getAsJsonObject("hugin").getAsJsonArray("omittedRules").size > 0), "no golden with an omitted rule")
  }

  for p <- goldens do
    test(s"${p.getFileName}: valid against the schema of the format") {
      assertEquals(validate(parse(p), schema, "$"), Nil)
    }
    test(s"${p.getFileName}: accepted by a model of the checker, with every leaf justified") {
      val j = parse(p)
      assertEquals(problems(j), Nil)
    }

  test("the model of the checker rejects a proof whose node is not an instance of a rule") {
    val j = parse(Path.of("tests/proofs/tc.json"))
    val inner = j.getAsJsonArray("trees").asScala.map(_.getAsJsonObject.getAsJsonObject("node"))
      .find(_.getAsJsonArray("children").size > 0).get
    inner.getAsJsonObject("label").getAsJsonArray("terms").get(0).getAsJsonObject.addProperty("constant", "zz")
    assert(problems(j).exists(_.contains("no rule")), problems(j))
  }

  test("the schema rejects a term that is neither a constant nor a variable") {
    val j = parse(Path.of("tests/proofs/tc.json"))
    j.getAsJsonArray("program").get(0).getAsJsonObject.getAsJsonObject("head").getAsJsonArray("terms")
      .get(0).getAsJsonObject.addProperty("value", "a")
    assert(validate(j, schema, "$").nonEmpty)
  }

  // ------------------------------------------------------------------ the schema

  /** The violations of the part of JSON Schema (draft 2020-12) that the schema uses; an unknown keyword is
   *  itself a violation, so that nothing is ignored silently. */
  private def validate(v: JsonElement, s: JsonObject, at: String): List[String] =
    s.entrySet.asScala.toList.flatMap { e =>
      val (k, x) = (e.getKey, e.getValue)
      k match
        case "$schema" | "$id" | "title" | "description" | "$defs" => Nil
        case "$ref" =>
          val name = x.getAsString.stripPrefix("#/$defs/")
          validate(v, schema.getAsJsonObject("$defs").getAsJsonObject(name), at)
        case "type" =>
          val ok = x.getAsString match
            case "object" => v.isJsonObject
            case "array" => v.isJsonArray
            case "string" => v.isJsonPrimitive && v.getAsJsonPrimitive.isString
            case "integer" => v.isJsonPrimitive && v.getAsJsonPrimitive.isNumber && v.getAsBigDecimal.scale <= 0
            case t => fail(s"type $t is not supported by the validator")
          if ok then Nil else List(s"$at: expected a value of type ${x.getAsString}")
        case "properties" if v.isJsonObject =>
          x.getAsJsonObject.entrySet.asScala.toList.flatMap { p =>
            Option(v.getAsJsonObject.get(p.getKey)).toList.flatMap(validate(_, p.getValue.getAsJsonObject, s"$at.${p.getKey}"))
          }
        case "required" if v.isJsonObject =>
          x.getAsJsonArray.asScala.map(_.getAsString).filterNot(v.getAsJsonObject.has).map(r => s"$at: missing `$r`").toList
        case "additionalProperties" if v.isJsonObject =>
          assert(!x.getAsBoolean, "only `additionalProperties: false` is supported")
          val known = s.getAsJsonObject("properties").keySet.asScala
          v.getAsJsonObject.keySet.asScala.filterNot(known).map(k => s"$at: unexpected `$k`").toList
        case "items" if v.isJsonArray =>
          v.getAsJsonArray.asScala.toList.zipWithIndex.flatMap((y, i) => validate(y, x.getAsJsonObject, s"$at[$i]"))
        case "oneOf" =>
          val matching = x.getAsJsonArray.asScala.count(alt => validate(v, alt.getAsJsonObject, at).isEmpty)
          if matching == 1 then Nil else List(s"$at: matches $matching alternatives of oneOf, not one")
        case "const" => if v == x then Nil else List(s"$at: expected $x")
        case "enum" => if x.getAsJsonArray.asScala.exists(_ == v) then Nil else List(s"$at: expected one of $x")
        case "minimum" => if v.getAsLong >= x.getAsLong then Nil else List(s"$at: below $x")
        case "properties" | "required" | "additionalProperties" | "items" => Nil
        case other => List(s"the validator does not support the keyword `$other`")
    }

  // ------------------------------------------------------------------ the checker

  private enum T:
    case Var(name: String)
    case Const(text: String)

  private final case class Atom(symbol: String, terms: List[T]):
    def ground: List[String] = terms.collect { case T.Const(c) => c }
    override def toString: String = s"$symbol(${terms.map { case T.Var(v) => s"?$v"; case T.Const(c) => c }.mkString(", ")})"

  private final case class Rule(head: Atom, body: List[Atom])

  private def atom(j: JsonElement): Atom =
    val o = j.getAsJsonObject
    Atom(
      o.get("symbol").getAsString,
      o.getAsJsonArray("terms").asScala.toList.map { t =>
        val to = t.getAsJsonObject
        if to.has("variable") then T.Var(to.get("variable").getAsString) else T.Const(to.get("constant").getAsString)
      }
    )

  private def assumptionSymbols(j: JsonObject): Set[String] =
    j.getAsJsonObject("hugin").getAsJsonArray("assumptionSymbols").asScala.map(_.getAsString).toSet

  /** A substitution extending `s` that maps the rule atoms `pattern` to the ground atoms `ground`. */
  private def matchAll(pattern: List[Atom], ground: List[Atom], s: Map[String, String] = Map.empty): Option[Map[String, String]] =
    if pattern.length != ground.length then None
    else
      pattern.zip(ground).foldLeft(Option(s)) { case (acc, (p, g)) =>
        acc.flatMap { s0 =>
          if p.symbol != g.symbol || p.terms.length != g.terms.length then None
          else
            p.terms.zip(g.ground).foldLeft(Option(s0)) {
              case (Some(m), (T.Const(c), d)) => if c == d then Some(m) else None
              case (Some(m), (T.Var(v), d)) => m.get(v) match
                  case Some(e) => if e == d then Some(m) else None
                  case None => Some(m.updated(v, d))
              case (None, _) => None
            }
        }
      }

  /** A proof node: its label and the labels of its children, in order. */
  private final case class Step(label: Atom, children: List[Atom])

  /** What the checker and the extra checks find wrong with an export. */
  private def problems(j: JsonObject): List[String] =
    val program = j.getAsJsonArray("program").asScala.toList.map(r =>
      Rule(atom(r.getAsJsonObject.get("head")), r.getAsJsonObject.getAsJsonArray("body").asScala.toList.map(atom))
    )
    val steps: List[Step] =
      if j.has("trees") then
        def walk(n: JsonElement): List[Step] =
          val node = n.getAsJsonObject.getAsJsonObject("node")
          val children = node.getAsJsonArray("children").asScala.toList
          Step(atom(node.get("label")), children.map(c => atom(c.getAsJsonObject.getAsJsonObject("node").get("label")))) :: children.flatMap(
            walk
          )
        j.getAsJsonArray("trees").asScala.toList.flatMap(walk)
      else
        val edges = j.getAsJsonObject("graph").getAsJsonArray("edges").asScala.toVector.map(_.getAsJsonObject)
        val labels = edges.map(e => atom(e.get("label")))
        edges.zipWithIndex.toList.map { (e, i) =>
          val preds = e.getAsJsonArray("predecessors").asScala.toList.map(_.getAsInt)
          assert(preds.forall(_ < i), s"edge $i has a predecessor that does not come before it: $preds")
          Step(labels(i), preds.map(labels))
        }
    val model = steps.map(_.label).toSet
    val assumptions = assumptionSymbols(j)
    val assumed = j.getAsJsonObject("hugin").getAsJsonArray("assumedFacts").asScala.map(atom).toSet
    val facts = program.filter(_.body.isEmpty).map(_.head).toSet
    // the parser: one arity per relation symbol of the program; every label is ground, of such a symbol
    val arities = program.flatMap(r => r.head :: r.body).groupBy(_.symbol).view.mapValues(_.map(_.terms.length).distinct).toMap
    val arity = arities.collect { case (s, List(n)) => s -> n }
    val parsing = arities.collect { case (s, ns) if ns.length > 1 => s"mismatched arities of $s: $ns" }.toList ++
      steps.map(_.label).distinct.collect {
        case a if !arity.get(a.symbol).contains(a.terms.length) => s"unknown relation symbol or wrong arity: $a"
        case a if a.terms.exists(_.isInstanceOf[T.Var]) => s"a variable in a label: $a"
      }
    // validity with the universal database: a node with children is an instance of a rule
    val validity = steps.distinct.collect {
      case Step(l, cs) if cs.nonEmpty && !program.exists(r => matchAll(r.head :: r.body, l :: cs).isDefined) =>
        s"no rule derives $l from $cs"
    }
    // the model check of `-c`: every instance of a rule whose body holds in the model has its head in it
    def instances(body: List[Atom], s: Map[String, String]): List[Map[String, String]] = body match
      case Nil => List(s)
      case b :: rest => model.toList.flatMap(g => matchAll(List(b), List(g), s)).flatMap(instances(rest, _))
    val modelhood =
      for
        r <- program
        s <- instances(r.body, Map.empty)
        h = Atom(r.head.symbol, r.head.terms.map { case T.Var(v) => T.Const(s(v)); case c => c })
        if !model.contains(h)
      yield s"the facts of the proofs are not a model: $h is missing"
    // the leaves
    def holds(a: Atom): Boolean =
      if a.symbol.startsWith("not ") then
        val wildcard = (c: String) => c.startsWith("_") || c.headOption.exists(_.isUpper)
        !model.exists(f =>
          f.symbol == a.symbol.stripPrefix("not ") && f.ground.length == a.ground.length &&
            f.ground.zip(a.ground).forall((x, y) => wildcard(y) || x == y)
        )
      else
        val List(l, r) = a.ground
        val c = (l.toLongOption, r.toLongOption) match
          case (Some(x), Some(y)) => x.compare(y)
          case _ => l.compare(r)
        a.symbol match
          case "=" => c == 0
          case "<>" => c != 0
          case "<" => c < 0
          case "<=" => c <= 0
          case ">" => c > 0
          case ">=" => c >= 0
    val leaves = steps.filter(_.children.isEmpty).map(_.label).distinct.collect {
      case a if assumptions(a.symbol) && !holds(a) => s"the assumption $a does not hold"
      case a
          if !assumptions(a.symbol) && !facts(a) && !assumed(a) && !program.exists(r =>
            r.body.isEmpty && matchAll(List(r.head), List(a)).isDefined
          ) =>
        s"the leaf $a is neither a fact of the program, nor assumed, nor an assumption"
    }
    parsing ++ validity ++ modelhood ++ leaves
