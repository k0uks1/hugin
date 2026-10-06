package hugin.meta

import scala.collection.mutable

/** Elaboration state of a lazily elaborated symbol (meta definitions, formula functions, object declarations,
 *  type definitions): used for forward references (E0105) and cyclic type definitions (E0104). */
enum ElabState:
  case Pending, InProgress, Done

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

/** Read-only view on the typing results of a compilation, for the phases after the typer and for tooling.
 *  Symbols the typer did not elaborate have no results. */
trait TypingResults:
  /** The meta type of a symbol. */
  def mtype(s: Sym): Option[MType]

  /** The static normal form of a transparent definition. */
  def static(s: Sym): Option[MExpr]

  /** The signature defined by a signature definition. */
  def sigValue(s: Sym): Option[MType]

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
