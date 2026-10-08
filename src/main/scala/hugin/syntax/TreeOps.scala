package hugin.syntax

import Trees.*

/** Generic operations on surface trees. */
object TreeOps:
  /** Every node of a surface tree in preorder, the tree itself first: the fields of case classes and
   *  enum cases, and the elements of lists, options and other collections, recursively. */
  def nodes(x: Any): Iterator[Any] = new Iterator[Any]:
    // the nodes still to visit, the next one last: an explicit stack, since nested iterators would make
    // every step cost the depth of the tree, and a list (a product `head :: tail`) is as deep as it is long
    private val pending = scala.collection.mutable.ArrayBuffer[Any](x)
    def hasNext: Boolean = pending.nonEmpty
    def next(): Any =
      val y = pending.remove(pending.length - 1)
      val children = y match
        case p: Product => p.productIterator.toVector
        case it: Iterable[?] => it.toVector
        case _ => Vector.empty
      pending ++= children.reverseIterator
      y

  /** The head and the arguments of an application `f a1 ... an`; parentheses around the whole
   *  application are dropped. */
  def flattenApp(t: Tree): (Tree, List[Tree]) =
    def go(t: Tree, acc: List[Tree]): (Tree, List[Tree]) = t match
      case Apply(f, a) => go(f, a :: acc)
      case Parens(i) if acc.isEmpty => go(i, acc)
      case other => (other, acc)
    go(t, Nil)

  /** The name an application `c a1 ... an` applies, if its head is a name. */
  def headName(t: Tree): Option[Ident] = t match
    case id: Ident => Some(id)
    case Apply(f, _) => headName(f)
    case _ => None

  /** The (labelled) domains and the codomain of an arrow type `d1 -> ... -> dn -> c`; parentheses around
   *  an arrow are dropped. */
  def flattenArrow(t: Tree): (List[(Option[Ident], Tree)], Tree) = t match
    case Arrow(l, d, c) =>
      val (ds, cod) = flattenArrow(c)
      ((l, d) :: ds, cod)
    case Parens(i @ Arrow(_, _, _)) => flattenArrow(i)
    case other => (Nil, other)

  /** The final codomain of an arrow type, ignoring labels and parentheses. */
  def codomain(t: Tree): Tree = t match
    case Arrow(_, _, c) => codomain(c)
    case Parens(i) => codomain(i)
    case other => other
