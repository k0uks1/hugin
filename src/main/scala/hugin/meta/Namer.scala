package hugin.meta

import hugin.util.*
import hugin.syntax.*
import hugin.core.*
import hugin.obj.BaseType

/** Enters the declarations of a module body into its scope and classifies items by stage (Section 2.5).
 *  The top-level program is entered by the `namer` phase; nested bodies are entered on demand by the typer. */
object Namer:
  val prelude: Scope =
    val s = Scope(None, "prelude")
    for (n, b) <- List("int" -> BaseType.IntT, "float" -> BaseType.FloatT, "string" -> BaseType.StringT) do
      val sym = Sym(n, SymKind.PreludeType, Span.NoSpan, s)
      sym.base = Some(b)
      sym.state = Sym.State.Done
      s.enter(sym)
    s

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
    def declare(name: Ident, kind: SymKind, item: Item, order: Int): Option[Sym] =
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
          s.order = order
          scope.enter(s)
          Some(s)

    for (item, k) <- items.zipWithIndex do
      item match
        case d @ Decl(name, params, tpe, sup, defn, abbrev) =>
          val kind: Option[SymKind] = tpe match
            case Keyword(Kw.Type) =>
              defn match
                case None => Some(SymKind.ObjType)
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
            declare(name, kd, d, k).foreach { s =>
              s.abbrev = abbrev
              if (kd == SymKind.Rel || kd == SymKind.Ctor) && params.nonEmpty then
                ctx.report(Diagnostic.error("E0103", s"relation `${name.name}` cannot have parameters", params.head.span)
                  .withHelp("type parameters of relation families are implicit: write uppercase type variables in the column types"))
            }
          }
        case d @ Def(name, _, _) => declare(name, SymKind.MetaDef, d, k)
        case _ =>

    // clauses of formula functions
    for (item, k) <- items.zipWithIndex do
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

/** Phase: enter the top-level program. */
final class NamerPhase extends Phase:
  def phaseName = "namer"
  def description = "enter declarations, classify items by stage, detect duplicates"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val root = Scope(Some(Namer.prelude), "program")
    u.rootScope = root
    Namer.enter(u.untpd.nn.items, root)
  override def show(using Context): String = Namer.show(ctx.unit.rootScope.nn)
