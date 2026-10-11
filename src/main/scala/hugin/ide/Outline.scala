package hugin.ide

import hugin.compiler.SymKind
import hugin.query.{CompileKey, Database, DocumentSymbol, Ide}
import hugin.util.Span
import scala.collection.mutable

/** The document outline. */
object Outline:
  /** A declaration in the outline of a file: its symbol, its extent (the declaration and its children),
   *  and the declarations nested in it (those of a module body). */
  final case class Node(symbol: DocumentSymbol, extent: Span, children: List[Node])

  /** The declarations of the program file `key`, nested by their enclosing definitions (module bodies). */
  def of(key: CompileKey)(using Database): List[Node] =
    if Files.isFacts(key.path) then Nil
    else
      final class Builder(val sym: DocumentSymbol):
        val children = mutable.ListBuffer.empty[Builder]
        def node: Node =
          val cs = children.map(_.node).toList
          Node(sym, cs.foldLeft(sym.extent)((sp, c) => sp.to(c.extent)), cs)
      val roots = mutable.ListBuffer.empty[Builder]
      val all = mutable.ListBuffer.empty[Builder]
      for s <- Ide.symbols(key) do
        val node = Builder(s)
        val parent = s.container.flatMap { c =>
          all
            .filter(n =>
              n.sym.name == c && n.sym.kind == SymKind.MetaDef && n.sym.extent.start <= s.span.start && s.span.end <= n.sym.extent.end
            )
            .minByOption(n => n.sym.extent.end - n.sym.extent.start)
        }
        parent.fold(roots)(_.children) += node
        all += node
      roots.map(_.node).toList
