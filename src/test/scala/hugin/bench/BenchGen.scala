package hugin.bench

import hugin.fuzz.ProgramGen
import java.nio.file.{Files, Path}
import scala.util.Random

/** Writes the generated programs of the bench set (`sbt "Test/runMain hugin.bench.Bench gen"`). The
 *  output is deterministic (fixed seeds), and the files are committed, so the bench set stays fixed
 *  even if the generators change. */
object BenchGen:
  def writeAll(): Unit =
    write("bench/small/one.hgn", "p : int -> rel.\n")
    write("bench/datalog/tc.hgn", tcProgram)
    write("bench/datalog/tc.facts", tcFacts(nodes = 600, extra = 600, seed = 1))
    write("bench/datalog/sp.hgn", spProgram)
    write("bench/datalog/sp.facts", gridFacts(side = 60, seed = 2))
    write("bench/datalog/strata.hgn", strataProgram)
    write("bench/datalog/strata.facts", strataFacts(nodes = 20000, seed = 3))
    write("bench/meta/meta_scaled.hgn", metaScaled(copies = 8))
    val (code, facts) = large(programs = 150, seed = 4)
    write("bench/gen/large.hgn", code)
    write("bench/gen/large.facts", facts)

  private def write(path: String, text: String): Unit =
    val p = Path.of(path)
    Files.createDirectories(p.getParent)
    Files.writeString(p, text)
    println(s"wrote $path (${text.linesIterator.size} lines)")

  // ------------------------------------------------------------------ Datalog-heavy

  private val tcProgram =
    """(* bench: transitive closure over a chain with random forward edges (semi-naive evaluation, joins) *)
      |node : type = int.
      |edge : node -> node -> rel.
      |%input edge.
      |path : node -> node -> rel.
      |path X Y :- edge X Y.
      |path X Z :- path X Y, edge Y Z.
      |reach : node -> int -> rel.
      |reach X N :- edge X _, N = count { Y | path X Y }.
      |total : int -> rel.
      |total S :- S = sum { N | reach _ N }.
      |%output total.
      |""".stripMargin

  private def tcFacts(nodes: Int, extra: Int, seed: Long): String =
    val rnd = Random(seed)
    val chain = (0 until nodes - 1).map(i => s"edge $i ${i + 1}.")
    val more = (0 until extra).map { _ =>
      val a = rnd.nextInt(nodes - 1)
      s"edge $a ${a + 1 + rnd.nextInt(nodes - 1 - a)}."
    }
    (chain ++ more).mkString("", "\n", "\n")

  private val spProgram =
    """(* bench: shortest paths with a bound column (min) over a weighted grid *)
      |node : type = int.
      |edge : node -> node -> int -> rel.
      |source : node -> rel.
      |%input edge.  %input source.
      |dist : (v : node) -> (d : min int) -> rel.
      |dist S 0 :- source S.
      |dist W (D + C) :- dist V D, edge V W C.
      |far : int -> rel.
      |far M :- M = max { D | dist _ D }.
      |%output far.
      |""".stripMargin

  private def gridFacts(side: Int, seed: Long): String =
    val rnd = Random(seed)
    def id(r: Int, c: Int) = r * side + c
    val edges =
      for
        r <- 0 until side
        c <- 0 until side
        (dr, dc) <- List((0, 1), (1, 0), (0, -1), (-1, 0))
        if r + dr >= 0 && r + dr < side && c + dc >= 0 && c + dc < side
      yield s"edge ${id(r, c)} ${id(r + dr, c + dc)} ${1 + rnd.nextInt(9)}."
    ("source 0." +: edges).mkString("", "\n", "\n")

  private val strataProgram =
    """(* bench: stratified negation and aggregates over a large random graph *)
      |node : type = int.
      |edge : node -> node -> rel.
      |root : node -> rel.
      |%input edge.  %input root.
      |known : node -> rel.
      |known X :- edge X _.
      |known Y :- edge _ Y.
      |reach : node -> rel.
      |reach X :- root X.
      |reach Y :- reach X, edge X Y.
      |unreached : node -> rel.
      |unreached X :- known X, not reach X.
      |outdeg : node -> int -> rel.
      |outdeg X N :- known X, N = count { Y | edge X Y }.
      |sink : node -> rel.
      |sink X :- known X, not edge X _.
      |stats : int -> int -> int -> rel.
      |stats U S M :- U = count { X | unreached X }, S = count { X | sink X }, M = max { N | outdeg _ N }.
      |%output stats.
      |""".stripMargin

  private def strataFacts(nodes: Int, seed: Long): String =
    val rnd = Random(seed)
    val edges = (0 until nodes * 2).map(_ => s"edge ${rnd.nextInt(nodes)} ${rnd.nextInt(nodes)}.")
    (Vector("root 0.", "root 1.") ++ edges).mkString("", "\n", "\n")

  // ------------------------------------------------------------------ meta-heavy

  private val metaHeader =
    """(* bench: the meta level at scale: functors, families, %demand, reflection and a module-wide
      |   directive, repeated over many relations *)
      |%use "std/reflect".
      |graph : Type = { node : type, edge : node -> node -> rel }.
      |tc (g : graph) = {
      |  path : g.node -> g.node -> rel.
      |  path X Y :- g.edge X Y.
      |  path X Z :- g.edge X Y, path Y Z.
      |}.
      |city : type.  c0 : city.  c1 : city.  c2 : city.  c3 : city.
      |name : type = string.
      |expr : type.   ref : name -> expr.   lam : name -> typ -> expr -> expr.
      |               app : expr -> expr -> expr.
      |typ  : type.   base : string -> typ.   arrow : typ -> typ -> typ.
      |ctx  : type.   empty : ctx.   bind : ctx -> name -> typ -> ctx.
      |box A : type.
      |put : A -> box A.
      |edge : city -> city -> rel.
      |edge c0 c1.
      |mirror : module -> module.
      |mirror [] = [].
      |mirror ('( edge $X $Y :- $..B ) :: Rest) = '( edge $X $Y :- $..B ) :: '( edge $Y $X :- $..B ) :: mirror Rest.
      |mirror (I :: Rest) = I :: mirror Rest.
      |""".stripMargin

  private def metaCopy(i: Int): String =
    s"""road$i : city -> city -> rel.
       |road$i c0 c1.  road$i c1 c2.  road$i c2 c3.
       |r$i = tc { node = city, edge = road$i }.
       |%output r$i.path.
       |edge c${i % 4} c${(i + 1) % 4} :- road$i c0 c1.
       |boxed$i : box int -> box string -> rel.
       |boxed$i (put $i) (put "x$i").
       |%output boxed$i.
       |lookup$i : (g : ctx) -> (x : name) -> (t : typ) -> rel.
       |%demand lookup$i +g +x -t.
       |lookup$i (bind _ X T) X T.
       |lookup$i (bind G Y _) X T :- lookup$i G X T, X <> Y.
       |typed$i : (e : expr) -> (g : ctx) -> (t : typ) -> rel.
       |%demand typed$i +e +g -t.
       |typed$i (ref X) G T :- lookup$i G X T.
       |typed$i (lam X T1 B) G (arrow T1 T2) :- typed$i B (bind G X T1) T2.
       |typed$i (app F A) G T1 :- typed$i F G (arrow T0 T1), typed$i A G T0.
       |prog$i : expr -> rel.
       |prog$i (lam "x" (base "i") (ref "x")).
       |prog$i (app (lam "f" (arrow (base "i") (base "i")) (ref "f")) (lam "y" (base "i") (ref "y"))).
       |result$i : expr -> typ -> rel.
       |result$i E T :- prog$i E, typed$i E empty T.
       |%output result$i.
       |num$i : int -> rel.
       |data$i : module = '( num$i $i. num$i M :- num$i N, N < ${i + 3}, M = N + 1. ).
       |$$data$i.
       |%output num$i.
       |""".stripMargin

  private def metaScaled(copies: Int): String =
    metaHeader + (0 until copies).map(metaCopy).mkString("\n") + "\n%mirror.\n%output edge.\n"

  // ------------------------------------------------------------------ large generated programs

  /** Many programs of the fuzz generator ([[ProgramGen]]) in one file, the relations of each renamed
   *  apart (`g7_d0`); the shared declarations (`color`, `box`, `point`) are kept once. */
  private def large(programs: Int, seed: Long): (String, String) =
    val rnd = Random(seed)
    // the relations every generated program declares for itself (renamed apart), as opposed to the
    // shared declarations (`color`, `box`, `point`, …)
    val names = raw"\b(e\d+|d\d+|counter|w[01rgs]|x[srm])\b".r
    val shared = collection.mutable.LinkedHashSet.empty[String]
    val items = collection.mutable.ArrayBuffer.empty[String]
    val inputs = collection.mutable.ArrayBuffer.empty[String]
    for k <- 0 until programs do
      val g = ProgramGen.programs.pureApply(org.scalacheck.Gen.Parameters.default, org.scalacheck.rng.Seed(rnd.nextLong()))
      def rename(s: String) = names.replaceAllIn(s, m => s"g${k}_${m.matched}")
      val sharedDecls = g.decls.take(8)
      shared ++= sharedDecls
      items ++= (g.decls.drop(8) ++ g.facts ++ g.rules ++ g.derived.map(d => s"%output $d.")).map(rename)
      inputs ++= g.inputs.map(rename)
    // the generated programs use `len` of `std/list` (as `Generated.items` opens it)
    (("%use \"std/list\"." +: (shared.toVector ++ items)).mkString("", "\n", "\n"), inputs.mkString("", "\n", "\n"))
