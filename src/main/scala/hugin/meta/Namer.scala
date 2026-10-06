package hugin.meta

import hugin.util.*
import hugin.syntax.*
import hugin.compiler.*
import hugin.obj.BaseType
import scala.collection.mutable

/** Enters the declarations of a module body into its scope and classifies items by stage (Section 2.5).
 *  The top-level program is entered by the `namer` phase; nested bodies are entered on demand by the typer. */
object Namer:
  private val builtins: Map[String, BaseType] = BaseType.values.map(b => b.show -> b).toMap

  /** Final codomain of an arrow type, ignoring labels and parentheses. */
  def codomain(t: Tree): Tree = t match
    case Arrow(_, _, c) => codomain(c)
    case Parens(i) => codomain(i)
    case other => other

  def arrowArity(t: Tree): Int = t match
    case Arrow(_, _, c) => 1 + arrowArity(c)
    case Parens(i) => arrowArity(i)
    case _ => 0

  def enter(items: List[Item], scope: Scope)(using Context): Unit =
    def declare(name: Ident, kind: SymKind, item: Item): Option[Sym] =
      scope.lookupLocal(name.name) match
        case Some(prev) =>
          ctx.report(
            Diagnostic.error("E0102", s"`${name.name}` is declared twice in this scope", name.span, "redeclared here")
              .withLabel(prev.span, "first declared here")
          )
          None
        case None =>
          val s = Sym(name.name, kind, name.span, scope)
          s.decl = Some(item)
          scope.enter(s)
          Some(s)

    for item <- items do
      item match
        case d @ Decl(name, params, tpe, sup, defn, abbrev) =>
          val kind: Option[SymKind] = tpe match
            case Keyword(Kw.Type) =>
              defn match
                case None => Some(SymKind.ObjType)
                case Some(Builtin(b)) =>
                  if params.nonEmpty || sup.isDefined then
                    ctx.error("E0103", "a base type has no parameters or supertype", d.span)
                  if builtins.contains(b.name) then Some(SymKind.BaseType)
                  else
                    ctx.report(Diagnostic.error("E0103", s"unknown base type `${b.name}`", b.span, "not a builtin")
                      .withNote(s"the builtin base types are ${builtins.keys.toList.sorted.mkString(", ")}"))
                    None
                case Some(_: RecordType) if !abbrev =>
                  if sup.isDefined then
                    ctx.error("E0103", "a struct declaration cannot have a supertype", sup.get.span)
                  Some(SymKind.Struct)
                case Some(_) =>
                  if sup.isDefined then
                    ctx.error(
                      "E0103",
                      "a type definition cannot have a supertype",
                      sup.get.span,
                      "remove this, or declare a refinement `a : type <: b.`"
                    )
                  Some(SymKind.TypeDef)
            case Keyword(Kw.Mod) =>
              if defn.isEmpty then
                ctx.report(Diagnostic.error("E0103", s"signature `${name.name}` has no definition", d.span)
                  .withHelp(s"write `${name.name} : mod = { ... }.`"))
                None
              else Some(SymKind.MetaDef)
            case _ =>
              codomain(tpe) match
                case Keyword(Kw.Rel) =>
                  if defn.isDefined then
                    ctx.report(Diagnostic.error("E0103", s"relation `${name.name}` cannot be defined by `=`", defn.get.span, "not allowed")
                      .withHelp("relations are defined by rules: `c X :- body.`"))
                  Some(SymKind.Rel)
                case Keyword(Kw.Prop) => Some(SymKind.FormulaFn)
                case Keyword(Kw.Type) =>
                  ctx.report(Diagnostic.error(
                    "E0103",
                    s"cannot classify the declaration of `${name.name}`",
                    tpe.span,
                    "a function returning `type`"
                  ).withHelp("declare a family with type parameters instead: `f A : type.`"))
                  None
                case _ =>
                  if defn.isDefined then Some(SymKind.MetaDef) else Some(SymKind.Ctor)
          if abbrev && !kind.contains(SymKind.TypeDef) then
            ctx.error("E0103", "`%abbrev` only applies to type definitions", d.span)
          kind.foreach { kd =>
            declare(name, kd, d).foreach { s =>
              s.abbrev = abbrev
              if kd == SymKind.BaseType then
                defn.collect { case Builtin(b) => builtins(b.name) }.foreach(b => s.base = Some(b))
                s.state = Sym.State.Done
              if (kd == SymKind.Rel || kd == SymKind.Ctor) && params.nonEmpty then
                ctx.report(Diagnostic.error("E0103", s"relation `${name.name}` cannot have parameters", params.head.span)
                  .withHelp("type parameters of relation families are implicit: write uppercase type variables in the column types"))
            }
          }
        case d @ Def(name, _, _) => declare(name, SymKind.MetaDef, d)
        case _ =>

    // clauses of formula functions
    for item <- items do
      item match
        case r @ Rule(_, heads, _) =>
          def headName(t: Tree): Option[Ident] = t match
            case id: Ident => Some(id)
            case Apply(f, _) => headName(f)
            case _ => None
          val fnHeads =
            heads.flatMap(h => headName(h).flatMap(n => scope.lookupLocal(n.name)).filter(_.kind == SymKind.FormulaFn).map(h -> _))
          if fnHeads.nonEmpty then
            if heads.length > 1 then
              ctx.error("E0004", "a clause of a formula function must have exactly one head", r.span)
            else fnHeads.head._2.clauses += r
        case _ =>

  /** Textual symbol table (output of the `namer` phase). */
  def show(scope: Scope): String =
    scope.decls.values.map(s => s"${s.name} : ${s.kind.describe}${if s.clauses.nonEmpty then s" (${s.clauses.length} clauses)" else ""}")
      .mkString("\n")

/** Phase: enter the prelude, the imported files and the program. The prelude's scope encloses the others,
 *  so its names are visible everywhere and can be shadowed; imported files see only the prelude. */
final class NamerPhase extends Phase:
  def phaseName = "namer"
  def description = "enter declarations, classify items by stage, detect duplicates"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val prelude = Scope(None, "prelude")
    prelude.qualifier = Some("")
    val taken = mutable.HashSet("")
    for lib <- u.libraries.values do
      val sc = if lib.isPrelude then prelude else Scope(Some(prelude), s"file ${lib.path}")
      if !lib.isPrelude then
        sc.qualifier = Some(Iterator.from(1).map(k => if k == 1 then lib.name else s"${lib.name}$k").find(taken.add).get)
      lib.scope = sc
      Namer.enter(lib.program.items, sc)
    val root = Scope(Some(prelude), "program")
    root.qualifier = Some("")
    u.rootScope = root
    Namer.enter(u.untpd.nn.items, root)
    prelude.shadowed = root.decls.keySet.intersect(prelude.decls.keySet).toSet
  override def show(using Context): String = Namer.show(ctx.unit.rootScope.nn)
