package hugin.meta

import hugin.obj.{Column, OType, TParam}
import hugin.syntax.Tree
import hugin.util.Span
import scala.collection.mutable

/** Elaboration state of a lazily elaborated symbol (meta definitions, formula functions, object declarations,
 *  type definitions): used for forward references (E0105) and cyclic type definitions (E0104). */
enum ElabState:
  case Pending, InProgress, Done

/** Elaborated information about an object declaration: its family type parameters (explicit ones first,
 *  then the implicit ones of relations and constructors), columns, constructor result type, and the kind
 *  of an object type. */
final case class DeclInfo(tparams: List[TParam], cols: List[Column], result: Option[OType], typeKind: Option[TypeKindE])

/** An elaborated type definition `n A1 ... Ak = τ` (Section 4.7): its parameters as meta parameters and its
 *  right-hand side. */
final case class TypeDefInfo(params: List[Sym], rhs: OType)

/** What the typer computed for one symbol. Mutable while the typer runs; read through [[TypingResults]]. */
final class SymInfo:
  /** Elaboration state (see [[ElabState]]). */
  var state: ElabState = ElabState.Pending

  /** Meta type. */
  var mtype: Option[MType] = None

  /** Static normal form (for transparent definitions: types, records of types and relations). */
  var static: Option[MExpr] = None

  /** For signature definitions (`graph : mod = {...}`): the signature itself. */
  var sigValue: Option[MType] = None

  /** For object declarations (object types, structs, relations, constructors). */
  var declInfo: Option[DeclInfo] = None

  /** For type definitions. */
  var typeDef: Option[TypeDefInfo] = None

  /** `%mode` declarations of a formula function (Section 4.8): input flags and the directive's span. */
  var fnModes: List[(List[Boolean], Span)] = Nil

  def snapshot: SymSnapshot = SymSnapshot(state, mtype, static, sigValue, declInfo, typeDef, fnModes)

  /** A copy, for a table that changes the results of a symbol of one of its parents. */
  def copy(): SymInfo =
    val c = SymInfo()
    c.state = state
    c.mtype = mtype
    c.static = static
    c.sigValue = sigValue
    c.declInfo = declInfo
    c.typeDef = typeDef
    c.fnModes = fnModes
    c

/** Read-only view on the typing results of a compilation, for the phases after the typer and for tooling.
 *  Symbols the typer did not elaborate have no results. */
trait TypingResults:
  /** The meta type of a symbol. */
  def mtype(s: Sym): Option[MType]

  /** The static normal form of a transparent definition. */
  def static(s: Sym): Option[MExpr]

  /** The signature defined by a signature definition. */
  def sigValue(s: Sym): Option[MType]

  /** The elaborated object declaration. */
  def declInfo(s: Sym): Option[DeclInfo]

  /** The family type parameters of an object declaration (none for other symbols). */
  def tparams(s: Sym): List[TParam] = declInfo(s).fold(Nil)(_.tparams)

  /** The elaborated type definition. */
  def typeDef(s: Sym): Option[TypeDefInfo]

  /** The `%mode` declarations of a formula function. */
  def fnModes(s: Sym): List[(List[Boolean], Span)]

object TypingResults:
  /** No results (before the typer ran). */
  def empty: TypingResults = SymTable()

/** The typer's symbol table: typing results per symbol, owned and filled by the typer, exposed afterwards
 *  as [[TypingResults]] (`CompilationUnit.symbols`). Symbols are keyed by their (stable) keys.
 *
 *  A table is layered over the (frozen) tables of the files it was elaborated against (`parents`: the
 *  prelude and the imported files, see [[hugin.compiler.ElaboratedLibrary]]): reads fall through to them,
 *  writes go to this table only (a symbol of a parent that is changed, such as a formula function of the
 *  prelude that gets a `%mode` declaration, is copied first), so a library's results are shared read-only
 *  by every compilation importing it. */
final class SymTable(parents: List[SymTable] = Nil, view: SymTable.View = SymTable.View.All) extends TypingResults:
  private val infos = mutable.HashMap.empty[Sym, SymInfo]
  private val paramTrees = mutable.HashMap.empty[Sym, Tree]
  private var frozen = false

  /** The parents and their ancestors, nearest first, each once. */
  private val ancestors: Vector[SymTable] =
    val seen = java.util.IdentityHashMap[SymTable, Unit]()
    (parents.iterator ++ parents.iterator.flatMap(_.ancestors)).filter(t => !seen.containsKey(t) && { seen.put(t, ()); true }).toVector

  /** Forbids further changes (the table of a library, shared by the compilations importing it). */
  def freeze(): Unit = frozen = true

  private def find(s: Sym): Option[SymInfo] =
    infos.get(s) match
      case some @ Some(_) => some
      case None =>
        view.observe(s)
        if view.hidden(s) then return None
        var i = 0
        var found: Option[SymInfo] = None
        while found.isEmpty && i < ancestors.length do
          found = ancestors(i).infos.get(s)
          i += 1
        found

  /** The (mutable) results of a symbol, created on first access. */
  private[meta] def apply(s: Sym): SymInfo =
    if frozen then throw IllegalStateException(s"typing results of `$s` changed in a frozen table")
    infos.getOrElseUpdate(s, find(s).fold(SymInfo())(_.copy()))

  /** The elaboration state of a symbol. */
  private[meta] def state(s: Sym): ElabState = find(s).fold(ElabState.Pending)(_.state)

  /** Records the meta type of a symbol that needs no further elaboration (parameters, fields). */
  private[meta] def define(s: Sym, t: MType): Unit =
    val i = apply(s)
    i.mtype = Some(t)
    i.state = ElabState.Done

  /** The declared type of a meta parameter as written, for suggested edits to signatures. */
  private[meta] def paramType(p: Sym): Option[Tree] =
    paramTrees.get(p).orElse {
      view.observe(p)
      ancestors.iterator.flatMap(_.paramTrees.get(p)).nextOption()
    }

  private[meta] def setParamType(p: Sym, t: Tree): Unit =
    if frozen then throw IllegalStateException(s"parameter `$p` declared in a frozen table")
    paramTrees(p) = t

  /** Whether this table (not a parent) has results for `s`. */
  def hasLocal(s: Sym): Boolean = infos.contains(s)

  /** The results computed in this table (not in its parents), as snapshots. */
  def localResults: Iterator[(Sym, SymSnapshot)] = infos.iterator.map((s, i) => (s, i.snapshot))

  /** The declared types of parameters recorded in this table (not in its parents). */
  def localParamTypes: Iterator[(Sym, Tree)] = paramTrees.iterator

  /** Adds the results computed in `other` (not those of its parents) to this table: the per-item tables
   *  of a program are merged into the table of the whole program. */
  def absorb(other: SymTable): Unit =
    if frozen then throw IllegalStateException("results added to a frozen table")
    infos ++= other.infos
    paramTrees ++= other.paramTrees

  def mtype(s: Sym): Option[MType] = find(s).flatMap(_.mtype)
  def static(s: Sym): Option[MExpr] = find(s).flatMap(_.static)
  def sigValue(s: Sym): Option[MType] = find(s).flatMap(_.sigValue)
  def declInfo(s: Sym): Option[DeclInfo] = find(s).flatMap(_.declInfo)
  def typeDef(s: Sym): Option[TypeDefInfo] = find(s).flatMap(_.typeDef)
  def fnModes(s: Sym): List[(List[Boolean], Span)] = find(s).fold(Nil)(_.fnModes)

object SymTable:
  /** What a table shows of its parents: symbols the reader must not see yet (`hidden`, read as having no
   *  results), and a hook told about every symbol whose results are read from a parent (`observe`). */
  trait View:
    def hidden(s: Sym): Boolean
    def observe(s: Sym): Unit

  object View:
    /** Everything, unobserved. */
    object All extends View:
      def hidden(s: Sym): Boolean = false
      def observe(s: Sym): Unit = ()

/** The typing results of one symbol at one point, immutable (see [[SymInfo]]). */
final case class SymSnapshot(
    state: ElabState,
    mtype: Option[MType],
    static: Option[MExpr],
    sigValue: Option[MType],
    declInfo: Option[DeclInfo],
    typeDef: Option[TypeDefInfo],
    fnModes: List[(List[Boolean], Span)]
)
