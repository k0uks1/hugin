package hugin.fuzz

import hugin.compiler.Context
import hugin.obj.typing.TypeOps
import hugin.runtime.{Engine, Evaluation, FactLoader}
import hugin.util.*
import org.scalacheck.Prop

import scala.util.Random

/** Fuzzing with generated well-typed programs (issue #7, parts 2 and 3): the compiler accepts them, the
 *  semi-naive engine agrees with a naive reference evaluator on every relation, the output does not
 *  depend on the order of items, on unused relations or on the names of relations, the demand
 *  transformation preserves query answers, and the CLI handles them robustly. */
class GeneratedFuzzSuite extends FuzzSuite:
  override def shortCount: Int = 100

  private def rendered(c: Context): String =
    val r = DiagnosticRenderer(color = false)
    c.reporter.sorted.map(r.render).mkString("\n")

  /** Compiles a generated program; `Left` with the diagnostics if it is rejected (a generator or a
   *  compiler bug: generated programs are meant to be valid). */
  private def accepted(p: Program): Either[String, Context] =
    val c = Fuzz.compile(p)
    if c.reporter.hasErrors then Left(s"generated program rejected:\n${rendered(c)}") else Right(c)

  private def factFiles(p: Program): List[SourceFile] = p.facts.toList.map(SourceFile.virtual("gen.facts", _))

  /** Differences between the engine and the naive evaluator, relation by relation. */
  private def differential(p: Program): List[String] =
    accepted(p) match
      case Left(problem) => List(problem)
      case Right(c) =>
        val prog = c.unit.core.nn
        val engine = Engine(prog)
        val reporter = Reporter()
        val loader = FactLoader(engine, prog, TypeOps(c.unit.prog.nn), reporter)
        factFiles(p).foreach(loader.load)
        if reporter.hasErrors then return List(s"input facts rejected: ${reporter.sorted.map(_.message).mkString("; ")}")
        val naive = NaiveEvaluator(prog)
        naive.load(engine)
        engine.run()
        naive.run()
        for
          (r, tag) <- prog.rels.toList.zipWithIndex
          (actual, expected) = (engine.facts(tag), naive.shown(tag))
          if actual != expected
        yield s"relation ${r.name}: the engine derives\n  ${actual.mkString(" ")}\nthe naive evaluator\n  ${expected.mkString(" ")}"

  /** The output lines of `run` (sorted, if `sorted`), or the problem. */
  private def output(p: Program, sorted: Boolean = true): Either[String, List[String]] =
    accepted(p).flatMap { c =>
      val outcome = Evaluation.run(c, factFiles(p))
      outcome.result.map(r => if sorted then r.output.sorted else r.output).toRight(
        s"evaluation failed: ${outcome.diagnostics.map(_.message).mkString("; ")}"
      )
    }

  /** Variants of a program that must produce the same output (after renaming back). */
  private def variants(g: Generated): List[(String, Program, String => String)] =
    val rnd = Random(g.code.hashCode)
    val shuffled = Program(rnd.shuffle(g.items).mkString("\n") + "\n", g.program.facts)
    val unused = g.copy(decls = g.decls ++ Vector("unused_rel : int -> string -> rel.", "unused_rel 1 \"x\".")).program
    val relName = raw"\b([ed]\d+|counter)\b".r
    val renamed = Program(relName.replaceAllIn(g.code, "renamed_$1"), g.program.facts.map(relName.replaceAllIn(_, "renamed_$1")))
    List(
      ("items permuted", shuffled, identity),
      ("unused relation added", unused, identity),
      ("relations renamed", renamed, _.replaceAll(raw"\brenamed_", ""))
    )

  property("generated programs are accepted and the engine agrees with a naive evaluator") {
    Prop.forAll(ProgramGen.programs) { g =>
      verdict("differential", g.program, Fuzz.guarded(differential(g.program)).fold(f => List(f.describe), identity))
    }
  }

  property("the output does not depend on item order, unused relations or relation names") {
    Prop.forAll(ProgramGen.programs) { g =>
      val problems = Fuzz.guarded {
        output(g.program) match
          case Left(problem) => List(problem)
          case Right(expected) =>
            for
              (what, variant, back) <- variants(g)
              actual = output(variant).map(_.map(back).sorted)
              if actual != Right(expected)
            yield s"$what: expected\n  ${expected.mkString("\n  ")}\ngot\n  ${actual.fold(identity, _.mkString("\n  "))}\n----- variant\n${variant.code}"
      }
      verdict("metamorphic", g.program, problems.fold(f => List(f.describe), identity))
    }
  }

  /** Queries `?- d v X1 … Xn.` of the relation that can be moded, without and with `%mode d +a -b …`
   *  (and without `%output`, which would show only the demanded facts of a moded relation). */
  private def demandVariants(g: Generated): Option[(Program, Program)] =
    for
      d <- g.demand
      vs = ProgramGen.values(d.cols.head) if vs.nonEmpty
    yield
      val vars = d.cols.indices.tail.map(i => s"X$i")
      val queries = vs.map(v => s"?- ${(d.name +: v +: vars).mkString(" ")}.")
      val mode = d.cols.indices.map(i => (if i == 0 then "+" else "-") + ProgramGen.Rel.column(i)).mkString(s"%mode ${d.name} ", " ", ".")
      val plain = g.copy(derived = Vector.empty, rules = g.rules ++ queries)
      (plain.program, plain.copy(decls = plain.decls :+ mode).program)

  property("the demand transformation (%mode) preserves query answers") {
    Prop.forAll(ProgramGen.programs) { g =>
      val problems = demandVariants(g).toList.flatMap { (plain, moded) =>
        Fuzz.guarded {
          (output(plain, sorted = false), output(moded, sorted = false)) match
            case (Right(a), Right(b)) if a == b => Nil
            case (a, b) =>
              List(
                s"answers differ; without %mode\n  ${a.fold(identity, _.mkString("\n  "))}\nwith %mode\n  ${b.fold(identity, _.mkString("\n  "))}\n----- moded$moded"
              )
        }.fold(f => List(f.describe), identity)
      }
      verdict("demand", g.program, problems)
    }
  }

  property("generated programs are handled robustly by check and run") {
    Prop.forAll(ProgramGen.programs) { g =>
      verdict("robustness", g.program, Fuzz.robustness(g.program, mustRun = true))
    }
  }
