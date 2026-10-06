package hugin.fuzz

import org.scalacheck.Prop

/** Mutation fuzzing of the seed corpus (issue #7, part 1): no crash, exit code 0 or 1, `check` within the
 *  time limit, deterministic diagnostics, spans inside the file. */
class MutationFuzzSuite extends FuzzSuite:
  override def shortCount: Int = 150

  property("mutated corpus programs are handled robustly") {
    Prop.forAll(Mutations.mutants) { m =>
      verdict("mutants", m.program, Fuzz.robustness(m.program, budget = 3, mustRun = false))
    }
  }
