package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import scala.collection.mutable

/** The order in which a file's declarations are elaborated (reference: meta/index, "Order of elaboration"):
 *  by the strongly connected components of their dependency graph, in topological order, independent
 *  components in source order (Haskell 2010 §4.5.1).
 *
 *  The nodes are the items that declare (declarations, definitions, `%use`, subtyping edges), the clause
 *  group of each function, the rules of each formula function, and the derived functions of the file's
 *  shared types. A function's signature (its declaration) and its body (its clause group) are separate
 *  nodes; a mention of a function, a definition or a formula function depends on its body, the body on
 *  the signature. Mentions are the names in an item's syntax, collected without regard to shadowing: an
 *  extra edge only orders an item later or merges components. */
object ElabOrder:

  enum Kind:
    /** A declaration, definition, `%use` or subtyping edge (or an item with a syntax error). */
    case Plain

    /** The clauses of the function `f`. */
    case Clauses(f: Name)

    /** The rules of the formula function `f` (none: it is false). */
    case Rules(f: Name)

    /** The derived functions `T.lift` and `T.reify` of the file's shared types. */
    case Derived

  /** A node: its items in source order and its position (the start of its first item). */
  final case class Node(kind: Kind, items: List[Item], pos: Int)

  /** What the order is computed from: the plain items in source order with the names each may declare;
   *  the clause groups and the formula functions' rules; the names the derived functions need (the
   *  shared types and their constructors) if there are any; the names every body needs although it may
   *  not mention them (the compiler-known names, when the file declares them itself); whether a name not
   *  declared in the file resolves outside it (to the prelude's, or a builtin type). */
  final case class Input(
      plain: List[(Item, List[Name])],
      clauses: List[(Name, List[Item])],
      rules: List[(Name, List[Item], Int)],
      derived: Option[Set[Name]],
      implicitNeeds: Set[Name],
      outside: Name => Boolean
  )

  /** The nodes, the dependencies of each (indices), and the components in elaboration order. */
  final case class Plan(nodes: Vector[Node], deps: Vector[Set[Int]], components: List[List[Int]]):
    /** The nodes that some plain node depends on, directly or not (the bodies a signature needs). */
    def neededBySignatures: Set[Int] =
      val seen = mutable.Set.empty[Int]
      val todo = mutable.Stack.from(nodes.indices.filter(nodes(_).kind == Kind.Plain).flatMap(deps))
      while todo.nonEmpty do
        val n = todo.pop()
        if seen.add(n) then todo.pushAll(deps(n))
      seen.toSet

  def plan(in: Input): Plan =
    val all = mutable.ArrayBuffer.empty[Node]
    for (item, _) <- in.plain do all += Node(Kind.Plain, List(item), item.span.start)
    for (f, items) <- in.clauses do all += Node(Kind.Clauses(f), items, items.head.span.start)
    for (f, items, pos) <- in.rules do all += Node(Kind.Rules(f), items, items.headOption.fold(pos)(_.span.start))
    in.derived.foreach(_ => all += Node(Kind.Derived, Nil, Int.MaxValue))
    val nodes = all.toVector
    val declaring = mutable.HashMap.empty[Name, List[Int]]
    for ((_, names), i) <- in.plain.zipWithIndex; n <- names do declaring(n) = declaring.getOrElse(n, Nil) :+ i
    val bodies = nodes.indices.collect { i =>
      nodes(i).kind match
        case Kind.Clauses(f) => f -> i
        case Kind.Rules(f) => f -> i
    }.toMap
    val derivedNode = in.derived.map(_ => nodes.length - 1)
    val uses = in.plain.zipWithIndex.collect { case ((Directive(_, u: DirArgs.Use), _), i) => (i, opens(u, in.plain)) }
    def signatures(n: Name) = declaring.getOrElse(n, Nil)
    def target(n: Name): List[Int] =
      bodies.get(n).map(List(_)).orElse(declaring.get(n)).getOrElse {
        // a path `T.lift` names a derived function; a name not declared here nor outside may be opened by
        // a `%use`
        if n.endsWith(".lift") || n.endsWith(".reify") then derivedNode.toList
        else if in.outside(n) then Nil
        else uses.collect { case (i, o) if o.forall(_(n)) => i }.toList
      }
    val deps = nodes.indices.map { i =>
      val node = nodes(i)
      val own: Set[Int] = node.kind match
        case Kind.Plain => Set.empty
        case Kind.Clauses(f) => (signatures(f) ++ derivedNode ++ in.implicitNeeds.flatMap(signatures)).toSet
        case Kind.Rules(f) => (signatures(f) ++ derivedNode ++ in.implicitNeeds.flatMap(signatures)).toSet
        case Kind.Derived => in.derived.get.flatMap(signatures) ++ in.implicitNeeds.flatMap(signatures)
      val declared = node.kind match
        case Kind.Plain => in.plain(i)._2.toSet
        case _ => Set.empty[Name]
      val mentioned = node.items.flatMap(it => mentions(it) -- declared).flatMap(target)
      (own ++ mentioned) - i
    }.toVector
    val order = nodes.indices.sortBy(i => (nodes(i).pos, i))
    Plan(nodes, deps, hugin.util.Graphs.components(order, deps(_).toSeq))

  /** The names a `%use` may open: those listed, the members of the module body that its module of the
   *  file evaluates to (also through a functor of the file), or any (`None`). */
  private def opens(u: DirArgs.Use, plain: List[(Item, List[Name])]): Option[Set[Name]] =
    def definition(m: Name): Option[hugin.syntax.Tree] = plain.collectFirst {
      case (Def(n, _, rhs), _) if n.name == m => rhs
      case (Decl(n, _, _, None, Some(rhs)), _) if n.name == m => rhs
    }
    def body(t: hugin.syntax.Tree, depth: Int): Option[Set[Name]] = if depth > 8 then None
    else
      t match
        case ModuleBody(items) => Some(members(items))
        case Parens(i) => body(i, depth + 1)
        case Lambda(_, _, b) => body(b, depth + 1)
        case Apply(f, _) => body(f, depth + 1)
        case Ident(m) => definition(m).flatMap(body(_, depth + 1))
        case _ => None
    u.names.map(_.map(_.name).toSet).orElse(body(u.module, 0))

  private def members(items: List[Item]): Set[Name] = items.collect {
    case d: Decl => d.name.name
    case d: Def => d.name.name
  }.toSet

  /** The names an item mentions: its identifiers (also in patterns, local definitions and quotes) and its
   *  paths `T.f`, except its own name and record labels. */
  def mentions(item: Item): Set[Name] =
    val out = mutable.Set.empty[Name]
    val todo = mutable.ArrayBuffer[Any](item match
      case d: Decl => (d.params, d.tpe, d.sup, d.defn)
      case d: Def => (d.params, d.rhs)
      case other => other
    )
    while todo.nonEmpty do
      todo.remove(todo.length - 1) match
        case Ident(n) => out += n
        case s @ Select(q, n) =>
          todo += q
          rootPath(s).foreach(out += _)
        // labels and binders are not mentions
        case Field(_, v) => todo += v
        case SigEntry.FieldDecl(_, t) => todo += t
        case _: SigEntry.Complete | _: ModeItem =>
        case Param.Typed(_, t, _) => todo += t
        case Lambda(_, t, b) => todo ++= t; todo += b
        case Arrow(_, d, c) => todo += d; todo += c
        case p: Product => todo ++= p.productIterator
        case it: Iterable[?] => todo ++= it
        case _ =>
    out.toSet

  private def rootPath(t: Tree): Option[Name] = t match
    case Ident(n) => Some(n)
    case Select(q, n) => rootPath(q).map(r => s"$r.$n")
    case _ => None

  /** The shared type a declaration's codomain names (`c : A -> T B.`), for the derived functions. */
  def codomainHead(d: Decl): Option[Name] = TreeOps.headName(TreeOps.codomain(d.tpe)).map(_.name)
