package hugin.query

import hugin.core.{ElaboratedDeclarations, Fingerprint, Footprint, GlobalKey, Opaque}

/** What one object item read of its program's declarations (its footprint, with globals by their
 *  stable keys): the globals, the names in each per-name table, and the tables read as a whole. Its hash
 *  is computed once (the key is looked up whenever the item is revalidated). */
final case class DeclViewKey(program: ProgramKey, globals: Vector[GlobalKey], names: Vector[(String, String)], tables: Vector[String]):
  override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)

/** The projections of a program's declarations that one object item read (issue #126, PR 7 step 3;
 *  [[hugin.core.DeclarationsSummary]]): the libraries they were elaborated on (by identity: another chain
 *  of libraries numbers the libraries' globals differently), the fingerprint of each global it read (`None`
 *  if the declarations have no global with that key), the outcome of each name it looked up, and each
 *  table it read as a whole. Cut off unless one of them changed. One query per item rather than one per
 *  projection: a cold compilation of a large program records a few dependencies per item instead of one
 *  per read (gen_large: 3 691 instead of about 25 000, measured as most of step 3's cost). */
object DeclView extends Query[DeclViewKey, (Opaque, Vector[Option[Fingerprint]], Vector[Any], Vector[Option[Any]])]("declView"):
  def compute(key: DeclViewKey)(using db: Database): (Opaque, Vector[Option[Fingerprint]], Vector[Any], Vector[Option[Any]]) =
    val decls = db(Signatures, key.program)
    val summary = decls.summary
    (
      Opaque(decls.base),
      key.globals.map(summary.fingerprint),
      key.names.map((channel, n) => summary.name(channel, n)),
      key.tables.map(summary.table)
    )

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
      val globals = footprint.globals.iterator.map(summary.keys(_)).toVector // in id order
      // in the footprint's order: a different order of the same names only makes a new key (a view
      // computed again), never a wrong cut-off
      val names = footprint.names.iterator
        .filter((channel, _) => !footprint.whole(channel))
        .flatMap((channel, ns) => ns.iterator.map((channel, _)))
        .toVector
      db(DeclView, DeclViewKey(program, globals, names, whole.toVector))
