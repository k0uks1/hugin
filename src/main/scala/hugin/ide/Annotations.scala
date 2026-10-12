package hugin.ide

import hugin.compiler.MetaIndex.Hint
import hugin.compiler.{SemanticIndex, Sym}
import hugin.query.{Compile, CompileKey, Database}
import hugin.util.Span
import scala.collection.mutable
import scala.util.control.NonFatal

/** A name of a file and what an editor shows for it: its hover (an index into [[Annotations.hovers]], or
 *  -1 if hover shows nothing there), its declaration, its occurrence group (the occurrences of one
 *  symbol or object variable share it), and whether it is the declaration itself. */
final case class Annotated(span: Span, hover: Int, target: Option[Target], group: Int, declaration: Boolean)

/** The annotation table of a file (`docs/design/web-ide.md`, 4.3): the bulk form of hover and navigation,
 *  from which an editor answers hover, go to definition, references and occurrence highlighting without
 *  asking the compiler again. `names` are sorted and do not overlap; `hovers` are deduplicated; `hints`
 *  are the inlay hints of the default settings. */
final case class Annotations(names: List[Annotated], hovers: Vector[Hover], hints: List[Hint])

object Annotations:
  val empty: Annotations = Annotations(Nil, Vector.empty, Nil)

  /** What a name is: a symbol's declaration or use, or an occurrence of an object variable. */
  private enum Name:
    case Symbol(at: Span, sym: Sym, declaration: Boolean)
    case Variable(occurrence: SemanticIndex#VarOccurrence)
    def span: Span = this match
      case Symbol(sp, _, _) => sp
      case Variable(v) => v.span

  /** The annotations of the file `path` of the program `key`: every name the semantic index knows there
   *  (the names the semantic tokens of [[Tokens]] classify; where two overlap, the declaration and then the
   *  first wins), each with the hover [[Hover.at]] gives at it (in the program's own file), the declaration [[Navigation.definition]]
   *  gives and its occurrence group, found in one pass over the index. A compiler crash leaves the table
   *  empty, as it leaves the highlighting without semantic tokens. */
  def of(key: CompileKey, path: String)(using db: Database): Annotations =
    if Files.isFacts(path) then empty
    else
      try compute(key, path)
      catch case NonFatal(_) => empty

  /** The spellings of the operators that `%infix op f.` binds to meta functions (reference:
   *  lexical-structure). */
  private val operatorSymbols = Set("+", "-", "*", "/", "^", "≡", "==")

  private def compute(key: CompileKey, path: String)(using db: Database): Annotations =
    val ix = db(Compile, key).index
    def inFile(sp: Span) = sp.exists && sp.source.path == path
    val decls = ix.symbols.filter(s => inFile(s.span) && s.span.text == s.name).map(s => Name.Symbol(s.span, s, true))
    // an operator bound to a meta function (`%infix + plus.`) refers to the function where it is written
    val uses = ix.references
      .filter(r => inFile(r.span) && (r.span.text == r.sym.name || operatorSymbols(r.span.text)))
      .map(r => Name.Symbol(r.span, r.sym, false))
    val vars = ix.variables.filter(v => inFile(v.span) && v.span.text == v.display).map(Name.Variable(_))
    def declFirst(n: Name) = n match
      case Name.Symbol(_, _, true) => 0
      case _ => 1
    val sorted = (decls ++ uses ++ vars).toList.sortBy(n => (n.span.start, declFirst(n)))
    val names = mutable.ListBuffer.empty[Name]
    var prevEnd = -1
    for n <- sorted if n.span.start >= prevEnd && n.span.end > n.span.start do
      names += n
      prevEnd = n.span.end
    // the first occurrence of each object variable in its rule: its declaration
    val firstVar = mutable.HashMap.empty[(Span, String), Span]
    for v <- ix.variables if v.span.exists do
      val k = (v.item, v.name)
      if firstVar.get(k).forall(sp => v.span.start < sp.start) then firstVar(k) = v.span
    val groups = mutable.LinkedHashMap.empty[Any, Int]
    val hovers = mutable.LinkedHashMap.empty[Hover, Int]
    val annotated = names.toList.map { n =>
      val (groupKey, target, declaration) = n match
        case Name.Symbol(_, s, decl) => (s, symbolTarget(s), decl)
        case Name.Variable(v) =>
          val first = firstVar((v.item, v.name))
          ((v.item, v.name), Some(Target.InFile(first)), first == v.span)
      val group = groups.getOrElseUpdate(groupKey, groups.size)
      // asked inside the name, not at its start, where a name just before it may end
      val at = n.span.start + (n.span.end - n.span.start) / 2
      val hover = (if path == key.path then Hover.at(key, at) else None).fold(-1)(h => hovers.getOrElseUpdate(h, hovers.size))
      Annotated(n.span, hover, target, group, declaration)
    }
    Annotations(annotated, hovers.keys.toVector, Hints.in(key, path, 0, Int.MaxValue, HintSettings()))

  private def symbolTarget(s: Sym): Option[Target] =
    if !s.span.exists then None
    else if Files.isLibrary(s.span.source.path) then Some(Target.Library(Files.libraryModule(s.span.source.path), s.name))
    else Some(Target.InFile(s.span))
