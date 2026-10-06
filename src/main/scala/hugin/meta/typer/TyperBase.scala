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

  /** The typing results of this compilation (see [[SymTable]]). */
  val syms: SymTable = SymTable()

  val declInfo: mutable.HashMap[Sym, DeclInfo] = mutable.HashMap.empty
  private var freshN = 0
  private[meta] def fresh(prefix: String): String = { freshN += 1; s"$prefix$freshN" }

  private[meta] def err(code: String, msg: String, span: Span, label: String = ""): Unit =
    ctx.error(code, msg, span, label)

  // ======================================================================= names

  private[meta] def editDistance(a: String, b: String): Int =
    org.apache.commons.text.similarity.LevenshteinDistance.getDefaultInstance.apply(a, b)

  private[meta] def suggestion(name: String, sc: Scope): Option[String] =
    val cands = sc.allNames.toList.distinct.filter(n => n != name && n.headOption.map(_.isUpper) == name.headOption.map(_.isUpper))
    cands.map(n => (editDistance(n, name), n)).filter(_._1 <= (name.length / 3).max(1)).sortBy(_._1).headOption.map(_._2)

  private[meta] def unresolved(name: String, span: Span, sc: Scope, what: String = "name"): Unit =
    var d = Diagnostic.error("E0101", s"unresolved $what `$name`", span, "not found in this scope")
    suggestion(name, sc).foreach { s =>
      d = d.withHelp(s"a declaration with a similar name exists: `$s`")
      if span.text == name then d = d.withSuggestion(s"replace with `$s`", span, s)
    }
    ctx.report(d)

  private[meta] def lookup(name: String, span: Span, sc: Scope): Option[Sym] =
    sc.lookup(name) match
      case some @ Some(s) =>
        noteUse(span, s)
        some
      case None => unresolved(name, span, sc); None

  /** Records a resolved use of a symbol (for the semantic index and the unused-definition warning). */
  private[meta] def noteUse(span: Span, s: Sym, detail: Option[String] = None): Unit =
    s.used = true
    noteReference(span, s, detail)

  /** Records a reference for tooling only (e.g. a directive naming a function, which is not a use). */
  private[meta] def noteReference(span: Span, s: Sym, detail: Option[String] = None): Unit =
    context.unit.index.reference(span, s, detail)

  /** Forward-reference check for meta definitions (Section 2.3). */
  private[meta] def visible(s: Sym, span: Span): Boolean =
    if s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn then
      syms.state(s) match
        case ElabState.Done => syms.mtype(s).isDefined
        case ElabState.InProgress =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` refers to itself", span, "recursive reference")
            .withLabel(s.span, "while elaborating this definition")
            .withNote("the meta level has no recursion; definitions may only refer to earlier definitions"))
          false
        case ElabState.Pending =>
          ctx.report(Diagnostic.error("E0105", s"`${s.name}` is used before its definition", span, "used here")
            .withLabel(s.span, "defined later here")
            .withNote("meta definitions may only refer to earlier definitions (Section 2.3)"))
          false
    else true
