package hugin.meta

import hugin.obj.{Column, OType, TParam}
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
 *  as [[TypingResults]] (`CompilationUnit.symbols`). Symbols are keyed by identity. */
final class SymTable extends TypingResults:
  private val infos = mutable.HashMap.empty[Sym, SymInfo]

  /** The (mutable) results of a symbol, created on first access. */
  private[meta] def apply(s: Sym): SymInfo = infos.getOrElseUpdate(s, SymInfo())

  /** The elaboration state of a symbol. */
  private[meta] def state(s: Sym): ElabState = infos.get(s).fold(ElabState.Pending)(_.state)

  /** Records the meta type of a symbol that needs no further elaboration (parameters, fields). */
  private[meta] def define(s: Sym, t: MType): Unit =
    val i = apply(s)
    i.mtype = Some(t)
    i.state = ElabState.Done

  def mtype(s: Sym): Option[MType] = infos.get(s).flatMap(_.mtype)
  def static(s: Sym): Option[MExpr] = infos.get(s).flatMap(_.static)
  def sigValue(s: Sym): Option[MType] = infos.get(s).flatMap(_.sigValue)
  def declInfo(s: Sym): Option[DeclInfo] = infos.get(s).flatMap(_.declInfo)
  def typeDef(s: Sym): Option[TypeDefInfo] = infos.get(s).flatMap(_.typeDef)
  def fnModes(s: Sym): List[(List[Boolean], Span)] = infos.get(s).fold(Nil)(_.fnModes)
