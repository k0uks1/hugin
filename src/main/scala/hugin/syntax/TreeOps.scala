package hugin.syntax

/** Generic operations on surface trees. */
object TreeOps:
  /** Every node of a surface tree in preorder, the tree itself first: the fields of case classes and
   *  enum cases, and the elements of lists, options and other collections, recursively. */
  def nodes(x: Any): Iterator[Any] =
    val children = x match
      case p: Product => p.productIterator.flatMap(nodes)
      case it: Iterable[?] => it.iterator.flatMap(nodes)
      case _ => Iterator.empty
    Iterator.single(x) ++ children
