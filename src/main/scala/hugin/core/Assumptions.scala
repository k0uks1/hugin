package hugin.core

import scala.collection.mutable

/** The assumptions of a meta constant (reference: meta/consistency; Lean's `#print axioms`, Rocq's
 *  `Print Assumptions`): the postulates `x : A = %postulate.` and the trusted primitives it depends on,
 *  through its type, its value or its clauses, and through those of every constant they mention,
 *  transitively. The trusted primitives are the operations `x : A = %builtin p.` of the library and the
 *  functions of `std/nat` that compute natively: code of the compiler that the program relies on
 *  without a proof, as Lean lists `Lean.ofReduceBool`. `--safe` rejects postulates, not primitives. */
object Assumptions:
  /** The postulates of the program, in declaration order. */
  def postulates(core: Core): List[Int] = core.globals.indices.filter(core.globals(_).axiom).toList

  /** Whether the global `id` is an assumption: a postulate or a trusted primitive. */
  def isAssumption(core: Core, id: Int): Boolean = trusted(core.globals(id)).isDefined || core.globals(id).axiom

  /** What makes an entry a trusted primitive, as shown: its primitive operation or native operation. */
  private def trusted(g: GlobalEntry): Option[String] = g.kind match
    case GlobalKind.Primitive(op, _) => Some(s"trusted primitive %builtin ${op.key}")
    case GlobalKind.Function(_, Some(body)) => body.native.map(n => s"trusted native operation ${n.op.key}")
    case GlobalKind.Opaque(_, Some((_, body))) => body.native.map(n => s"trusted native operation ${n.op.key}")
    case _ => None

  /** The assumptions that the global `id` depends on (itself, if it is one), in declaration order. */
  def of(core: Core, id: Int): List[Int] =
    val seen = mutable.BitSet.empty
    val todo = mutable.Stack(id)
    while todo.nonEmpty do
      val g = todo.pop()
      if !seen(g) then
        seen += g
        todo.pushAll(mentioned(core.globals(g)).filterNot(seen))
    seen.toList.sorted.filter(isAssumption(core, _))

  /** The globals that an entry's type, value, clauses, constructors or family mention. */
  private def mentioned(g: GlobalEntry): List[Int] =
    val out = mutable.ListBuffer.empty[Int]
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
    def moduleBody(b: ModuleBody): Unit =
      for m <- b.members do
        tm(m.ty)
        m.kind match
          case MemberKind.Defined(t) => tm(t)
          case MemberKind.Object(_) =>
      b.items.flatMap(CoreItem.terms).foreach(tm)
    def tm(t: Tm): Unit =
      Tm.exists(t) {
        case Tm.Global(i) =>
          out += i
          false
        case Tm.Module(b, _) =>
          moduleBody(b)
          false
        case _ => false
      }: Unit
    def function(body: FunctionBody): Unit =
      tree(body.tree)
      for c <- body.clauses do
        c.body.foreach(tm)
        c.patterns.foreach(tm)
    tm(g.tyTm)
    g.kind match
      case GlobalKind.Definition(t, _) => tm(t)
      case GlobalKind.Function(_, Some(body)) => function(body)
      // an opaque definition or function does not unfold, but its proof rests on what it mentions
      case GlobalKind.Opaque(term, fn) =>
        term.foreach(tm)
        fn.foreach((_, body) => function(body))
      case GlobalKind.Inductive(ctors) => out ++= ctors
      case GlobalKind.Constructor(family) => out += family
      case GlobalKind.Primitive(_, ctors) => out ++= ctors
      case _ =>
    g.instanceOf.foreach { (family, args) =>
      out += family
      args.foreach(tm)
    }
    out.toList

  /** The lines that `--print-assumptions name` and `%assumptions name.` print: the assumptions of the
   *  constant `name` of the file `root` (else of any file), each with its type and what it is. */
  def report(core: Core, root: String, name: String): List[String] =
    val candidates = core.globals.indices.filter { i =>
      val g = core.globals(i)
      g.name == name && g.span.exists
    }
    // the root file's last one, else any file's; a meta constant before an object constant of its name
    // (the two sides of a shared data declaration)
    val inRoot = candidates.filter(core.globals(_).span.source.path == root)
    val pool = if inRoot.nonEmpty then inRoot else candidates
    val chosen = pool.filter(core.globals(_).stage == Stage.S1).lastOption.orElse(pool.lastOption)
    chosen match
      case None => List(s"note: assumptions of `$name`: no constant of that name")
      case Some(id) =>
        of(core, id) match
          case Nil => List(s"note: assumptions of `$name`: none")
          case ps =>
            s"note: assumptions of `$name`:" :: ps.map { p =>
              val g = core.globals(p)
              val what = trusted(g).getOrElse(s"postulate at ${g.span.show}")
              s"  ${g.name} : ${core.showPlain(Nil, g.tyTm)}  ($what)"
            }
