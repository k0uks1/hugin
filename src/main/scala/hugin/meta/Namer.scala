package hugin.meta

import hugin.syntax.*
import hugin.syntax.TreeOps.{codomain, headName}
import hugin.compiler.*
import hugin.obj.BaseType
import scala.collection.mutable

/** Enters the declarations of a module body into its scope and classifies items by stage (Section 2.5).
 *  The top-level program is entered by the `namer` phase; nested bodies are entered on demand by the typer. */
object Namer:
  private val builtins: Map[String, BaseType] = BaseType.values.map(b => b.show -> b).toMap

  /** Enters the declarations of `items` into the (new, empty) `scope`. Declarations are collected first,
   *  then the clauses of formula functions; the symbols are created last, with all of the namer's output. */
  def enter(items: List[Item], scope: Scope)(using Context): Unit =
    /** An accepted declaration. */
    final case class Entry(name: Ident, kind: SymKind, item: Item, key: ItemKey, abbrev: Boolean, base: Option[BaseType], fact: Boolean)
    val entries = mutable.LinkedHashMap.empty[String, Entry]
    def declare(
        name: Ident,
        kind: SymKind,
        item: Item,
        key: ItemKey,
        abbrev: Boolean = false,
        base: Option[BaseType] = None,
        fact: Boolean = false
    ): Boolean =
      entries.get(name.name) match
        case Some(prev) =>
          ctx.report(NameError.Duplicate(name.name, name.span, prev.name.span))
          false
        case None =>
          entries(name.name) = Entry(name, kind, item, key, abbrev, base, fact)
          true

    for (item, key) <- items.zip(ItemKey.assign(scope.key, items)) do
      item match
        case d @ Decl(name, params, _, _, defn, abbrev, fact) =>
          val kind = classify(d)
          if abbrev && !kind.contains(SymKind.TypeDef) then
            ctx.report(NameError.AbbrevNotTypeDefinition(d.span))
          if fact && kind.exists(k => k != SymKind.Ctor && k != SymKind.Struct) then
            ctx.report(NameError.FactNotConstructor(name.name, kind.get, d.span))
          kind.foreach { kd =>
            val base = if kd == SymKind.BaseType then defn.collect { case Builtin(b) => builtins(b.name) }
            else None
            val isFact = fact && (kd == SymKind.Ctor || kd == SymKind.Struct)
            if declare(name, kd, d, key, abbrev, base, isFact) && (kd == SymKind.Rel || kd == SymKind.Ctor) && params.nonEmpty then
              ctx.report(NameError.RelationWithParameters(name.name, params.head.span))
          }
        case d @ Def(name, _, _) => declare(name, SymKind.MetaDef, d, key)
        case _ =>

    // clauses of formula functions
    val clauses = mutable.HashMap.empty[String, mutable.ListBuffer[Rule]]
    for item <- items do
      item match
        case r @ Rule(_, heads, _) =>
          val fnHeads =
            heads.flatMap(h => headName(h).flatMap(n => entries.get(n.name)).filter(_.kind == SymKind.FormulaFn).map(h -> _))
          if fnHeads.nonEmpty then
            if heads.length > 1 then
              ctx.report(NameError.ClauseWithSeveralHeads(r.span))
            else clauses.getOrElseUpdate(fnHeads.head._2.name.name, mutable.ListBuffer.empty) += r
        case _ =>

    for e <- entries.values do
      val cls = clauses.get(e.name.name).fold(Nil)(_.toList)
      val name = e.name.name
      if !scope.claim(name) then throw IllegalStateException(s"`$name` entered twice into ${scope.key}")
      val key = SymKey(scope.key, name)
      scope.enter(Sym(name, e.kind, e.name.span, scope, key, ctx.unit.symKeys, Some(e.key), Some(e.item), cls, e.abbrev, e.base, e.fact))

  /** The kind of symbol a declaration declares (Section 2.5), or none if it cannot be classified (reported). */
  private def classify(d: Decl)(using Context): Option[SymKind] =
    val Decl(name, params, tpe, sup, defn, abbrev, _) = d
    tpe match
      case Keyword(Kw.Type) =>
        defn match
          case None => Some(SymKind.ObjType)
          case Some(Builtin(b)) =>
            if params.nonEmpty || sup.isDefined then
              ctx.report(NameError.BaseTypeWithParameters(d.span))
            if builtins.contains(b.name) then Some(SymKind.BaseType)
            else
              ctx.report(NameError.UnknownBaseType(b.name, b.span, builtins.keys.toList.sorted))
              None
          case Some(_: RecordType) if !abbrev =>
            if sup.isDefined then
              ctx.report(NameError.StructWithSupertype(sup.get.span))
            Some(SymKind.Struct)
          case Some(_) =>
            if sup.isDefined then
              ctx.report(NameError.TypeDefinitionWithSupertype(sup.get.span))
            Some(SymKind.TypeDef)
      case Keyword(Kw.Mod) =>
        if defn.isEmpty then
          ctx.report(NameError.SignatureWithoutDefinition(name.name, d.span))
          None
        else Some(SymKind.MetaDef)
      case _ =>
        codomain(tpe) match
          case Keyword(Kw.Rel) =>
            if defn.isDefined then
              ctx.report(NameError.RelationDefinedByEquation(name.name, defn.get.span))
            Some(SymKind.Rel)
          case Keyword(Kw.Prop) => Some(SymKind.FormulaFn)
          case Keyword(Kw.Type) =>
            ctx.report(NameError.TypeFunction(name.name, tpe.span))
            None
          case _ =>
            if defn.isDefined then Some(SymKind.MetaDef) else Some(SymKind.Ctor)

  /** Textual symbol table (output of the `namer` phase). */
  def show(scope: Scope): String =
    scope.decls.values.map(s => s"${s.name} : ${s.kind.describe}${if s.clauses.nonEmpty then s" (${s.clauses.length} clauses)" else ""}")
      .mkString("\n")

/** Phase: enter the prelude, the imported files and the program. The prelude's scope encloses the others,
 *  so its names are visible everywhere and can be shadowed; imported files see only the prelude. The
 *  libraries are named apart, once ([[NamedLibrary]]), and so is the program ([[NamedProgram]]). */
final class NamerPhase extends Phase:
  def phaseName = "namer"
  def description = "enter declarations, classify items by stage, detect duplicates"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    for lib <- u.libraries.values do
      val n = ctx.libraries.named(lib.key.nameKey)
      lib.named = n
      ctx.reportPart(hugin.compiler.DiagnosticPart.LibraryNames(lib.key.nameKey), n.diagnostics)
      u.symKeys.inherit(n.keys)
    // the program's top level is named apart (memoised by the query database, see `ProgramElab`)
    val named = ctx.libraries.nameProgram(u.source.path, u.source, u.untpd.nn, ctx.settings.prelude)
    ctx.reportPart(hugin.compiler.DiagnosticPart.ProgramNames(u.source.path, ctx.settings.prelude), named.diagnostics)
    u.symKeys.inherit(named.keys)
    u.named = named
    u.rootScope = named.scope
  override def show(using Context): String = Namer.show(ctx.unit.rootScope.nn)
