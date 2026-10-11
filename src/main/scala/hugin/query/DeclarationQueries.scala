package hugin.query

import hugin.core.{ElaboratedDeclarations, Fingerprint, Footprint, GlobalKey, Opaque}

final case class FingerprintKey(program: ProgramKey, key: GlobalKey)
final case class DeclNameKey(program: ProgramKey, channel: String, name: String)
final case class DeclTableKey(program: ProgramKey, channel: String)

/** The fingerprint of one global of a program's declarations, by key (issue #126, PR 7 step 3;
 *  [[hugin.core.DeclarationsSummary]]): a projection of [[Signatures]], cut off unless the global or
 *  something it refers to changed. `None` if the declarations have no such global. */
object DeclFingerprint extends Query[FingerprintKey, Option[Fingerprint]]("declFingerprint"):
  def compute(key: FingerprintKey)(using db: Database): Option[Fingerprint] = db(Signatures, key.program).summary.fingerprint(key.key)

/** The outcome of one name in one per-name table of the declarations' state (the scope, the erroneous,
 *  unelaborated, function and declared names). */
object DeclName extends Query[DeclNameKey, Any]("declName"):
  def compute(key: DeclNameKey)(using db: Database): Any = db(Signatures, key.program).summary.name(key.channel, key.name)

/** One whole table of the declarations' state, comparable. */
object DeclTable extends Query[DeclTableKey, Option[Any]]("declTable"):
  def compute(key: DeclTableKey)(using db: Database): Option[Any] = db(Signatures, key.program).summary.table(key.channel)

/** The libraries the declarations were elaborated on, by identity: the libraries' globals are named by
 *  their ids, which another chain of libraries numbers differently. */
object DeclBase extends Query[ProgramKey, Opaque]("declBase"):
  def compute(key: ProgramKey)(using db: Database): Opaque = Opaque(db(Signatures, key).base)

/** The dependencies of an object item on its program's declarations, from its footprint (section 9.4 of
 *  `docs/design/incrementality-2.md`): the fingerprint of every global it read, the outcome of every name
 *  it looked up, every table it read as a whole, and the libraries. An item that read a meta or a level
 *  variable of the declarations, the globals or metas as a whole, or a table without a comparable
 *  projection depends on all of the declarations (the designer's choice for metas and levels). */
object DeclarationDependencies:
  def record(program: ProgramKey, decls: ElaboratedDeclarations, footprint: Footprint)(using db: Database): Unit =
    val summary = decls.summary
    val whole = footprint.whole.toList.sorted
    if footprint.metas.nonEmpty || footprint.levels.nonEmpty || whole.exists(summary.table(_).isEmpty) then
      db(Signatures, program)
    else
      db(DeclBase, program)
      for id <- footprint.globals do db(DeclFingerprint, FingerprintKey(program, summary.keys(id)))
      for (channel, names) <- footprint.names.toList.sortBy(_._1) if !footprint.whole(channel); n <- names.toList.sorted do
        db(DeclName, DeclNameKey(program, channel, n))
      for channel <- whole do db(DeclTable, DeclTableKey(program, channel))
