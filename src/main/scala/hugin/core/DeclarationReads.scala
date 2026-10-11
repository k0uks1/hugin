package hugin.core

import scala.collection.mutable

/** The reads of a program's declarations made while one of its object items is elaborated (issue #126,
 *  PR 7; `docs/design/incrementality-2.md`, section 9.4). The item is elaborated in a fork of the
 *  declarations' core with a fork of their elaborator state; every read of what the declarations put
 *  there goes through one of these calls, at the boundary of the data structures (the globals and metas
 *  of the core, its universe levels, its tables of instances, modules, derived constants and
 *  requirements, the scope and the elaborator state), so that no access path is left out:
 *
 *  - `global(id)`, `meta(m)`, `level(v)`: an entry of the core, by position;
 *  - `name(channel, n)`: the entry for the name `n` in a per-name table (`scope`, `erroneous`,
 *    `unelaborated`, `functionNames`, `declaredHere`);
 *  - `all(channel)`: a whole table, or all of a per-name one (an iteration, a listing of names).
 *
 *  The calls sit on everything the fork of the item shares with the declarations (`Core.fork`,
 *  `ElabState.fork`, `Elaborator.fork`): the globals and metas ([[Entries]]), the level graph
 *  (`Levels.reads`), the instances of families, the module tables (body ids, instances by site, prefixes,
 *  anonymous names, file ranks), the derived constants, the subtyping edges, the counter of fresh object
 *  variables (`hygiene`), the cached relation information (a read of its global), the scope
 *  (`NameScope`) and the elaborator state (`ElabState.Names`, and the `opened`, `exported`,
 *  `signatures` and `droppedUses` tables). The requirements recorded are only added to by an item.
 *
 *  Reads of the libraries' part of the core (the prefix every program's declarations fork) and of what
 *  the item itself created are not reads of the declarations: [[Footprint]] keeps only the positions in
 *  the declarations' ranges. */
trait DeclarationReads:
  def global(id: Int): Unit
  def meta(m: Int): Unit
  def level(v: Int): Unit
  def name(channel: String, n: String): Unit
  def all(channel: String): Unit

/** The positions the declarations added to the core: globals, metas and level variables from the
 *  libraries' counts (inclusive) to the declarations' (exclusive). */
final case class DeclarationRanges(globals: Range, metas: Range, levels: Range)

object DeclarationRanges:
  def of(libraries: Core, declarations: Core): DeclarationRanges =
    DeclarationRanges(
      libraries.globals.length until declarations.globals.length,
      libraries.metas.length until declarations.metas.length,
      libraries.levels.count until declarations.levels.count
    )

/** What one item read of its declarations (step 2 of the addendum: recorded, not yet used). */
final class Footprint(val ranges: DeclarationRanges) extends DeclarationReads:
  val globals: mutable.BitSet = mutable.BitSet.empty
  val metas: mutable.BitSet = mutable.BitSet.empty
  val levels: mutable.BitSet = mutable.BitSet.empty
  val names: mutable.Map[String, mutable.Set[String]] = mutable.HashMap.empty
  val whole: mutable.Set[String] = mutable.HashSet.empty

  def global(id: Int): Unit = if ranges.globals.contains(id) then globals += id
  def meta(m: Int): Unit = if ranges.metas.contains(m) then metas += m
  def level(v: Int): Unit = if ranges.levels.contains(v) then levels += v
  def name(channel: String, n: String): Unit = names.getOrElseUpdate(channel, mutable.HashSet.empty) += n
  def all(channel: String): Unit = whole += channel

  /** Whether the reads of `other` are among these. */
  def covers(channel: String, n: String): Boolean = whole(channel) || names.get(channel).exists(_(n))

/** A test instrument (section 9.6, step 2): fails on any read of the declarations that `reference` did
 *  not record, so that an item elaborated again under it proves that the footprint covers every read on
 *  its path. */
final class Unrecorded(reference: Footprint) extends DeclarationReads:
  private def fail(what: String): Nothing = throw UnrecordedRead(what)
  private val r = reference.ranges
  def global(id: Int): Unit = if r.globals.contains(id) && !reference.globals(id) then fail(s"global $id")
  def meta(m: Int): Unit = if r.metas.contains(m) && !reference.metas(m) then fail(s"meta $m")
  def level(v: Int): Unit = if r.levels.contains(v) && !reference.levels(v) then fail(s"level $v")
  def name(channel: String, n: String): Unit = if !reference.covers(channel, n) then fail(s"$channel $n")
  def all(channel: String): Unit = if !reference.whole(channel) then fail(s"all of $channel")

final class UnrecordedRead(val what: String) extends scala.util.control.ControlThrowable(s"read of the declarations not recorded: $what")
