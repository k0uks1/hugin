package hugin.core

import scala.collection.mutable

/** The assumptions of a meta constant (reference: meta/functions, "Postulates"; Lean's `#print axioms`,
 *  Rocq's `Print Assumptions`): the postulates `x : A = %postulate.` it depends on, through its type, its
 *  value or its clauses, and through those of every constant they mention, transitively. The primitive
 *  operations of the prelude and native arithmetic are trusted code, not assumptions. */
object Assumptions:
  /** The postulates of the program, in declaration order. */
  def postulates(core: Core): List[Int] = core.globals.indices.filter(core.globals(_).axiom).toList

  /** The postulates that the global `id` depends on (itself, if it is one), in declaration order. */
  def of(core: Core, id: Int): List[Int] =
    val seen = mutable.BitSet.empty
    val todo = mutable.Stack(id)
    while todo.nonEmpty do
      val g = todo.pop()
      if !seen(g) then
        seen += g
        todo.pushAll(mentioned(core.globals(g)).filterNot(seen))
    seen.toList.filter(core.globals(_).axiom)

  /** The globals that an entry's type, value, clauses, constructors or family mention. */
  private def mentioned(g: GlobalEntry): List[Int] =
    val out = mutable.ListBuffer.empty[Int]
    def tm(t: Tm): Unit =
      Tm.exists(t) {
        case Tm.Global(i) =>
          out += i
          false
        case _ => false
      }: Unit
    def tree(t: CaseTree): Unit = t match
      case CaseTree.Leaf(body, _, subst, _) =>
        tm(body)
        subst.foreach(tm)
      case CaseTree.Split(_, branches) =>
        for b <- branches do
          out += b.ctor
          tree(b.tree)
      case CaseTree.SplitAtom(_, branches, default) =>
        for (v, b) <- branches do
          tm(v)
          tree(b)
        tree(default)
      case CaseTree.SplitNat(_, fam, values, _, above, below) =>
        if fam >= 0 then out += fam
        values.foreach((_, b) => tree(b))
        tree(above)
        tree(below)
    tm(g.tyTm)
    g.kind match
      case GlobalKind.Definition(t, _) => tm(t)
      case GlobalKind.Function(_, Some(body)) =>
        tree(body.tree)
        for c <- body.clauses do
          c.body.foreach(tm)
          c.patterns.foreach(tm)
      case GlobalKind.Inductive(ctors) => out ++= ctors
      case GlobalKind.Constructor(family) => out += family
      case GlobalKind.Primitive(_, ctors) => out ++= ctors
      case _ =>
    g.instanceOf.foreach { (family, args) =>
      out += family
      args.foreach(tm)
    }
    out.toList

  /** The lines that `--print-assumptions name` prints: the postulates of the meta constant `name` of the
   *  file `root` (else of any file), each with its type and position. */
  def report(core: Core, root: String, name: String): List[String] =
    val candidates = core.globals.indices.filter { i =>
      val g = core.globals(i)
      g.name == name && g.stage == Stage.S1 && g.span.exists
    }
    val chosen = candidates.filter(core.globals(_).span.source.path == root).lastOption.orElse(candidates.lastOption)
    chosen match
      case None => List(s"note: assumptions of `$name`: no meta constant of that name")
      case Some(id) =>
        of(core, id) match
          case Nil => List(s"note: assumptions of `$name`: none")
          case ps =>
            s"note: assumptions of `$name`:" :: ps.map { p =>
              val g = core.globals(p)
              s"  ${g.name} : ${core.showPlain(Nil, g.tyTm)}  (postulate at ${g.span.show})"
            }
