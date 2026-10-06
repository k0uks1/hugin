package hugin.meta
package typer

import hugin.util.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{OType, Column, TParam, Expansion}
import hugin.obj
import scala.collection.mutable

/** Elaborated information about an object declaration. */
final case class DeclInfo(cols: List[Column], result: Option[OType], typeKind: Option[TypeKindE])

/** Per-rule state while elaborating object code. */
final class RuleCtx(val allowVars: Boolean):
  val expansions: mutable.ListBuffer[Expansion] = mutable.ListBuffer.empty

  /** Set when a structural error was reported; the item is then dropped to avoid cascading errors. */
  var failed = false

  /** Nesting depth of aggregate bodies (negative context). */
  var aggDepth = 0
  private var wild = 0
  def freshWild(): String = { wild += 1; s"${obj.Var.WildPrefix}$wild" }

/** How uppercase identifiers that do not resolve are treated in types. */
enum TVars:
  case NoTVars

  /** Implicit type parameters of an object declaration (a family). */
  case Family(explicit: Map[String, TParam], implicits: mutable.LinkedHashMap[String, TParam], allowImplicit: Boolean)

  /** Implicit meta parameters of a meta function type (entered into `scope`). */
  case MetaImplicit(scope: Scope, collected: mutable.ListBuffer[Sym])

/** State and helpers shared by all parts of the typer. */
private[meta] trait TyperBase:
  protected val context: Context
  protected given Context = context

  val declInfo: mutable.HashMap[Sym, DeclInfo] = mutable.HashMap.empty
  private var freshN = 0
  private[meta] def fresh(prefix: String): String = { freshN += 1; s"$prefix$freshN" }

  private[meta] def err(code: String, msg: String, span: Span, label: String = ""): Unit =
    ctx.error(code, msg, span, label)

  // ======================================================================= names

  private[meta] def editDistance(a: String, b: String): Int =
    val d = Array.tabulate(a.length + 1, b.length + 1)((i, j) => if i == 0 then j else if j == 0 then i else 0)
    for i <- 1 to a.length; j <- 1 to b.length do
      d(i)(j) = (d(i - 1)(j) + 1).min(d(i)(j - 1) + 1).min(d(i - 1)(j - 1) + (if a(i - 1) == b(j - 1) then 0 else 1))
    d(a.length)(b.length)

  private[meta] def suggestion(name: String, sc: Scope): Option[String] =
    val cands = sc.allNames.toList.distinct.filter(n => n != name && n.headOption.map(_.isUpper) == name.headOption.map(_.isUpper))
    cands.map(n => (editDistance(n, name), n)).filter(_._1 <= (name.length / 3).max(1)).sortBy(_._1).headOption.map(_._2)

  private[meta] def unresolved(name: String, span: Span, sc: Scope, what: String = "name"): Unit =
    var d = Diagnostic.error("E0101", s"unresolved $what `$name`", span, "not found in this scope")
    suggestion(name, sc).foreach(s => d = d.withHelp(s"a declaration with a similar name exists: `$s`"))
    ctx.report(d)

  private[meta] def lookup(name: String, span: Span, sc: Scope): Option[Sym] =
    sc.lookup(name) match
      case some @ Some(s) => s.used = true; some
      case None => unresolved(name, span, sc); None

  /** Forward-reference check for meta definitions (Section 2.3). */
  private[meta] def visible(s: Sym, span: Span): Boolean =
    if s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn then
      s.state match
        case Sym.State.Done => s.mtype != null
        case Sym.State.InProgress =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` refers to itself", span, "recursive reference")
            .withLabel(s.span, "while elaborating this definition")
            .withNote("the meta level has no recursion; definitions may only refer to earlier definitions"))
          false
        case Sym.State.Pending =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` is used before its definition", span, "used here")
            .withLabel(s.span, "defined later here")
            .withNote("meta definitions may only refer to earlier definitions (Section 2.3)"))
          false
    else true
