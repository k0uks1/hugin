package hugin.query

import hugin.compiler.{SemanticIndex, Sym, SymKind}
import hugin.compiler.SemanticIndex.Stage
import hugin.syntax.{Lexer, Tok, Token}
import hugin.util.*

/** A declaration in a document outline: `span` is its name, `extent` the whole declaration, `container`
 *  the name of the enclosing definition. */
final case class DocumentSymbol(name: String, kind: SymKind, span: Span, extent: Span, container: Option[String])

/** Hover information: the signature of the symbol or variable at a position, and notes on what the
 *  compiler decided there (staging, family instances). */
final case class HoverInfo(signature: Option[String], notes: List[String]):
  def text: String = (signature.toList ++ notes).mkString("\n")

/** A completion candidate: the text to insert, what it is, and a description. */
final case class CompletionItem(label: String, kind: String, detail: String)

/** Position-based queries for tooling (hover, go to definition, find references, completion, outline).
 *  Positions are character offsets into the text of the program's file, or of the file `in` (a part of a
 *  program made of several files, such as the probe of a REPL session). */
object Ide:
  private def index(key: CompileKey)(using db: Database): SemanticIndex = db(Compile, key).index

  private def covers(span: Span, path: String, offset: Int): Boolean =
    span.exists && span.source.path == path && span.start <= offset && offset <= span.end

  private def size(span: Span): Int = span.end - span.start

  /** What is at an offset: a symbol (with the reference, if it is a use) or an object variable. */
  private enum Target:
    case Symbol(sym: Sym, use: Option[SemanticIndex#Reference])
    case Variable(occurrence: SemanticIndex#VarOccurrence)

  private def targetAt(key: CompileKey, offset: Int, in: Option[String])(using db: Database): Option[Target] =
    val ix = index(key)
    val path = in.getOrElse(key.path)
    val uses = ix.references.filter(r => covers(r.span, path, offset)).map(r => (r.span, Target.Symbol(r.sym, Some(r))))
    val decls = ix.symbols.filter(s => covers(s.span, path, offset)).map(s => (s.span, Target.Symbol(s, None)))
    val vars = ix.variables.filter(v => covers(v.span, path, offset)).map(v => (v.span, Target.Variable(v)))
    (uses ++ decls ++ vars).sortBy((sp, _) => size(sp)).headOption.map(_._2)

  /** The symbol referenced or declared at an offset (the innermost one). */
  def symbolAt(key: CompileKey, offset: Int, in: Option[String] = None)(using db: Database): Option[Sym] =
    targetAt(key, offset, in).collect {
      case Target.Symbol(s, _) => s
    }

  /** All occurrences of the object variable of `v`: same rule, same (internal) name. */
  private def occurrences(ix: SemanticIndex, v: SemanticIndex#VarOccurrence): List[Span] =
    ix.variables.filter(o => o.item == v.item && o.name == v.name).map(_.span).distinct.sortBy(_.start).toList

  /** Hover text: [[hoverInfo]] as lines. */
  def hover(key: CompileKey, offset: Int, in: Option[String] = None)(using db: Database): Option[String] =
    hoverInfo(key, offset, in).map(_.text)

  /** Hover information at an offset. The signature is the description of a symbol (as seen at this use),
   *  or the type of an object variable; a variable in a functor body may have different types in different
   *  instances, and all are shown. The notes say what the compiler decided there:
   *  - for a use of a family, the instance it resolved to (`len[int]`); for a family's declaration, all
   *    of its instances;
   *  - inside the innermost piece of staged code around the offset, whether a meta value was quoted,
   *    spliced or persisted, with the values it had. */
  def hoverInfo(key: CompileKey, offset: Int, in: Option[String] = None)(using db: Database): Option[HoverInfo] =
    val ix = index(key)
    val target = targetAt(key, offset, in)
    val signature = target.flatMap {
      case Target.Symbol(s, use) => use.flatMap(_.detail).orElse(ix.description(s))
      case Target.Variable(v) =>
        val types = ix.variables.filter(o => o.span == v.span && o.name == v.name).map(_.tpe).distinct
        Some(s"variable ${v.display} : ${types.mkString(" | ")}${if types.length > 1 then "  (in different instances)" else ""}")
    }
    val instances = target.toList.flatMap {
      case Target.Symbol(s, use) => familyInstances(ix, s, use.map(_.span))
      case Target.Variable(_) => Nil
    }
    val notes = instances ++ staging(ix, in.getOrElse(key.path), offset)
    Option.when(signature.isDefined || notes.nonEmpty)(HoverInfo(signature, notes))

  private def declares(family: Span, s: Sym): Boolean =
    s.span.exists && family.source.path == s.span.source.path && family.start <= s.span.start && s.span.end <= family.end

  /** The instances of the family `s`: at a use, those the use resolved to; at the declaration, all. */
  private def familyInstances(ix: SemanticIndex, s: Sym, use: Option[Span]): List[String] =
    val ofFamily = ix.instances.filter(i => declares(i.family, s))
    use match
      case Some(u) =>
        val names = ofFamily.filter(i => i.use.exists && i.use.source.path == u.source.path && i.use.start == u.start).map(_.name).distinct
        if names.isEmpty then Nil
        else List(s"instance: ${values(names)}${if names.length > 1 then "  (in different instances)" else ""}")
      case None =>
        val names = ofFamily.map(_.name).distinct
        if names.isEmpty then Nil else List(s"instances: ${names.map(n => s"`$n`").mkString(", ")}")

  /** The staging of the innermost staged code around an offset, one line per stage. */
  private def staging(ix: SemanticIndex, path: String, offset: Int): List[String] =
    val around = ix.staging.filter(st => covers(st.span, path, offset))
    around.map(_.span).minByOption(size).toList.flatMap { innermost =>
      val here = around.filter(_.span == innermost)
      here.map(_.stage).distinct.toList.map { stage =>
        val vs = here.filter(_.stage == stage).map(_.value).distinct
        val many = if vs.length > 1 then "  (in different applications)" else ""
        stage match
          case Stage.Quoted => s"quoted: passed to the meta level as the code ${values(vs)}$many"
          case Stage.Spliced => s"spliced: the meta-level code ${values(vs)} is inserted here$many"
          case Stage.Persisted => s"persisted: the compile-time value ${values(vs)} is embedded as a literal$many"
      }
    }

  /** Values in backticks, at most a few. */
  private def values(vs: Seq[String]): String =
    val shown = vs.take(MaxValues).map(v => s"`$v`").mkString(" | ")
    if vs.length > MaxValues then s"$shown | …" else shown

  private val MaxValues = 5

  /** Where the symbol at an offset is declared; for an object variable, its first occurrence in the rule. */
  def definition(key: CompileKey, offset: Int)(using db: Database): Option[Span] =
    targetAt(key, offset, None).flatMap {
      case Target.Symbol(s, _) => Some(s.span).filter(_.exists)
      case Target.Variable(v) => occurrences(index(key), v).headOption
    }

  /** The declaration and all uses of the symbol (or variable) at an offset, in source order. */
  def references(key: CompileKey, offset: Int)(using db: Database): List[Span] =
    val ix = index(key)
    targetAt(key, offset, None).toList.flatMap {
      case Target.Symbol(s, _) =>
        val uses = ix.references.filter(_.sym == s).map(_.span)
        (s.span +: uses).filter(_.exists).distinct.sortBy(sp => (sp.source.path, sp.start)).toList
      case Target.Variable(v) => occurrences(ix, v)
    }

  private val outlineKinds: Set[SymKind] =
    Set(SymKind.ObjType, SymKind.Struct, SymKind.Rel, SymKind.Ctor, SymKind.TypeDef, SymKind.FormulaFn, SymKind.MetaDef)

  /** The declarations of a file, each with its enclosing definition (for nested module bodies). */
  def symbols(key: CompileKey)(using db: Database): List[DocumentSymbol] =
    val syms = index(key).symbols.filter(s => outlineKinds(s.kind) && s.span.exists && s.span.source.path == key.path)
    def extent(s: Sym) = if s.extent.exists then s.extent else s.span
    val containers = syms.filter(s => s.kind == SymKind.MetaDef && s.extent.exists).map(s => (s, extent(s)))
    syms.toList
      .sortBy(_.span.start)
      .map { s =>
        val enclosing = containers
          .filter((c, sp) => c != s && sp.start <= s.span.start && s.span.end <= sp.end)
          .sortBy((_, sp) => size(sp))
          .headOption
          .map(_._1.name)
        DocumentSymbol(s.name, s.kind, s.span, extent(s), enclosing)
      }

  /** Completion candidates at an offset:
   *  - after `%`: directives;
   *  - inside the braces of a named pattern `c { ... }`: the labels of `c`;
   *  - after `m.`: the members of the module `m`;
   *  - otherwise: the names in scope at the offset (innermost module body outwards) and the variables of
   *    the enclosing rule (also of a rule that is still being typed and does not compile).
   *  Candidates are filtered by the identifier prefix before the offset. */
  def completions(key: CompileKey, offset: Int, in: Option[String] = None)(using db: Database): List[CompletionItem] =
    val ix = index(key)
    val path = in.getOrElse(key.path)
    val source = db(Parse, path).source
    val text = source.content
    val start = Iterator.iterate(offset)(_ - 1).find(i => i <= 0 || !isIdentChar(text.charAt(i - 1))).get
    val prefix = text.substring(start, offset.min(text.length))
    def matching(items: Seq[CompletionItem]) =
      items.filter(_.label.startsWith(prefix)).distinctBy(_.label).sortBy(_.label).toList
    if start > 0 && text.charAt(start - 1) == '%' then
      // the directives with a syntax of their own, and the meta functions in scope that are directives
      val functions = scopeAt(ix, path, offset).filter(ix.isDirective).map(s =>
        CompletionItem(s.name, "directive", ix.description(s).getOrElse("directive"))
      )
      matching(directives.map(d => CompletionItem(d, "directive", s"%$d")) ++ functions)
    else if start > 0 && text.charAt(start - 1) == '.' then
      // members of the module before the selector: the symbol the compiler resolved it to, or, in an item
      // that did not get that far, the one its name finds in the scope around the offset
      val qualEnd = start - 1
      val use = ix.references.filter(r => r.span.source.path == path && r.span.end == qualEnd).sortBy(r => size(r.span)).headOption
      val qualStart = Iterator.iterate(qualEnd)(_ - 1).find(i => i <= 0 || !isIdentChar(text.charAt(i - 1))).get
      val qual = text.substring(qualStart, qualEnd)
      val module = use.map(_.sym).orElse(scopeAt(ix, path, offset).find(_.name == qual))
      matching(module.toList.flatMap(m => ix.membersOf(m).map(item(ix, _))))
    else
      enclosingNamedPattern(source, start).flatMap(name => labels(ix, path, name, offset)) match
        case Some(ls) => matching(ls)
        case None =>
          val names = scopeAt(ix, path, offset).map(item(ix, _))
          val vars = ix.variables
            .filter(v => covers(v.item, path, offset))
            .map(v => CompletionItem(v.display, "variable", v.tpe))
          // the variables of an item that does not compile (yet) are not in the index: they are lexed
          val typed = itemVariables(source, start, offset).map(v => CompletionItem(v, "variable", "variable"))
          matching((vars ++ typed).filterNot(_.label == "_") ++ names)

  private val directives = List("infix", "import", "builtin")

  private def isIdentChar(c: Char): Boolean = c.isLetterOrDigit || c == '_' || c == '\''

  /** The names in scope at an offset: those of the innermost recorded extent (a module body) around it,
   *  then the top level's (also outside every extent, e.g. in a part of a program made of several files). */
  private def scopeAt(ix: SemanticIndex, path: String, offset: Int): List[Sym] =
    val inner = ix.scopes.filter(s => covers(s.extent, path, offset)).sortBy(s => size(s.extent)).headOption
    inner.toList.flatMap(_.names) ++ ix.topLevel

  private def item(ix: SemanticIndex, s: Sym): CompletionItem =
    CompletionItem(s.name, s.kind.describe, ix.description(s).getOrElse(s.kind.describe))

  /** The variables written in the item around an offset (from the period ending the previous item to the
   *  one ending this item), except the one being typed (from `start` to `offset`). */
  private def itemVariables(source: SourceFile, start: Int, offset: Int): List[String] =
    val toks = Lexer(source, Reporter()).tokenize().toVector
    val depths = toks.scanLeft(0) { (depth, t) =>
      t.kind match
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth + 1
        case Tok.RParen | Tok.RBrack | Tok.RBrace => (depth - 1).max(0)
        case _ => depth
    }
    def ends(i: Int) = toks(i).kind == Tok.Period && depths(i) == 0
    val first = toks.indices.filter(i => ends(i) && toks(i).span.end <= start).lastOption.fold(0)(_ + 1)
    val last = toks.indices.find(i => i >= first && ends(i) && toks(i).span.start >= offset).getOrElse(toks.length)
    toks.slice(first, last).toList.collect {
      case t if t.kind == Tok.Var && !(t.span.start == start && t.span.end == offset) => t.text
    }

  /** If the offset is inside the braces of `c { ... }`, the token `c`. */
  private def enclosingNamedPattern(source: SourceFile, offset: Int): Option[Token] =
    val toks = Lexer(SourceFile.virtual(source.path, source.content.substring(0, offset)), Reporter()).tokenize()
    var depth = 0
    var i = toks.length - 1
    var found: Option[Option[Token]] = None
    while i >= 0 && found.isEmpty do
      toks(i).kind match
        case Tok.RBrace => depth += 1
        case Tok.LBrace =>
          if depth == 0 then found = Some(Option.when(i > 0 && toks(i - 1).kind == Tok.Name)(toks(i - 1)))
          depth -= 1
        case Tok.Period if depth == 0 => found = Some(None)
        case _ =>
      i -= 1
    found.flatten

  private val relationKinds: Set[SymKind] = Set(SymKind.Rel, SymKind.Ctor, SymKind.Struct)

  /** The labels of the relation or constructor named by the token `name` (at an offset in `path`): the
   *  symbol the compiler resolved it to, or, in an item that does not compile, the one its name finds in
   *  the scope around the offset. None if the name is not a relation. */
  private def labels(ix: SemanticIndex, path: String, name: Token, offset: Int): Option[List[CompletionItem]] =
    val resolved = ix.references
      .filter(r => r.span.exists && r.span.source.path == path && r.span.start == name.span.start && r.sym.name == name.text)
      .sortBy(r => size(r.span))
      .headOption
      .map(_.sym)
    resolved.orElse(scopeAt(ix, path, offset).find(_.name == name.text)).filter(s => relationKinds(s.kind)).map { s =>
      ix.labelsOf(s).map(l => CompletionItem(l, "label", s"column of ${s.name}"))
    }

  def diagnostics(key: CompileKey)(using db: Database): List[Diagnostic] = db(Compile, key).diagnostics
