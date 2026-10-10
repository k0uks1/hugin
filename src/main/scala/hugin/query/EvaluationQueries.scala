package hugin.query

import hugin.runtime.{Evaluation, LoweredRules}
import hugin.util.*

/** What evaluating a compiled program reads of it, apart from its queries ([[LoweredRules]]); `None` if
 *  the program has errors. A projection of [[Compile]]: recomputed after every compilation, but cut off
 *  when the relations, types and lowered rules are equal, which is the case when only queries were
 *  added (as in the REPL; see [[Fixpoint]] for `%demand`). On a cut-off the database keeps the earlier
 *  value, whose program is the one the memoised fixpoint was computed for. */
object Lowered extends Query[CompileKey, Option[LoweredRules]]("lowered"):
  def compute(key: CompileKey)(using db: Database): Option[LoweredRules] =
    val c = db(Compile, key).context
    val core = c.unit.core
    if core == null || c.reporter.hasErrors || c.unit.prog == null then None
    else Some(LoweredRules.of(core.nn, c.unit.prog.nn))

/** A facts file parsed, once per text (also when the program changes). */
object FactsFile extends Query[String, Evaluation.ParsedFacts]("factsFile"):
  def compute(path: String)(using db: Database): Evaluation.ParsedFacts =
    Evaluation.parseFacts(SourceFile.virtual(path, db.get(SourceText, path)))

final case class FixpointKey(compile: CompileKey, facts: List[String])

/** A compiled program evaluated over facts files: the engine holding the fixpoint of its rules. It reads
 *  only [[Lowered]] and the facts files, so a query over an unchanged program and unchanged facts is
 *  answered against the memoised fixpoint ([[Evaluate]]) instead of evaluating from scratch.
 *
 *  `%demand` makes the rules depend on the queries: the demand transformation adds relations and rules
 *  for the bindings a query asks with. The fixpoint is keyed on the transformed program, as compiled,
 *  so a query that changes the transformed rules evaluates again, and one that leaves them equal reuses
 *  the fixpoint. (Reusing the fixpoint of the rules the transformation leaves unchanged and evaluating
 *  only what it adds is per-component reuse, issue #126, PR 4.) */
object Fixpoint extends Query[FixpointKey, Option[Evaluation.Fixpoint]]("fixpoint"):
  def compute(key: FixpointKey)(using db: Database): Option[Evaluation.Fixpoint] =
    db(Lowered, key.compile).map(l => Evaluation.fixpoint(l.prog, l.ops, key.facts.map(db(FactsFile, _))))

final case class EvaluateKey(compile: CompileKey, facts: List[String] = Nil, allRelations: Boolean = false)

/** Evaluates a compiled program over input facts: its output relations and the answers of its queries,
 *  read from the [[Fixpoint]] of its rules. Changing only a facts file re-evaluates without recompiling;
 *  adding queries recompiles without re-evaluating; an evaluation with an unchanged outcome does not
 *  invalidate its dependents. */
object Evaluate extends Query[EvaluateKey, Evaluation.Outcome]("evaluate"):
  def compute(key: EvaluateKey)(using db: Database): Evaluation.Outcome =
    val c = db(Compile, key.compile).context
    val core = c.unit.core
    if core == null || c.reporter.hasErrors then Evaluation.Outcome(None, Nil)
    else
      // the fixpoint's program has the same relation tags as this one ([[Lowered]]'s equality)
      db(Fixpoint, FixpointKey(key.compile, key.facts)) match
        case Some(fixpoint) => Evaluation.render(core.nn, fixpoint, key.allRelations)
        case None => Evaluation.Outcome(None, Nil)
