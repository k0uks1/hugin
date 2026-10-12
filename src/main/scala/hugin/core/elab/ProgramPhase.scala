package hugin.core
package elab

import hugin.syntax.TreeOps
import hugin.syntax.Trees.*

import scala.collection.mutable

/** The proof phase of a file or a module body (reference: meta/index, "Order of elaboration"; #186 P9f).
 *
 *  A meta declaration (or a member of a body) is *program-dependent* if it mentions the program of its own
 *  scope: `programOf here` or a judgment `here ⊢ r t̄`, or a program-dependent declaration of the same
 *  scope. Such declarations need the scope's rules, which are elaborated after the declarations they may
 *  use, so they are elaborated in a phase of their own after the scope's object items. They are found
 *  syntactically, before anything is elaborated: a declaration that mentions `here` directly (outside the
 *  module bodies it contains, whose `here` is their own), and the declarations that mention its name,
 *  transitively, by the names of [[ElabOrder.mentions]]. A function's signature and its clauses, and a
 *  formula function's declaration and its rules, go together. Everything else keeps its place, so a
 *  scope without `here` is elaborated as before; the test for one is a scan of the items' text for the
 *  word `here`, which most files fail at once.
 *
 *  Lean 4, Isabelle and Agda elaborate in textual order, so a lemma comes after the inductive definition
 *  it is about. Hugin's items are unordered (the dependency order of `ElabOrder`, #91), so the same order
 *  follows from the dependencies: a proof about the scope's program depends on all of its rules. A rule
 *  (or anything the rules need) that uses a program-dependent declaration depends on its own program:
 *  that is the cycle E0962, reported where the name is used ([[Names]]). */
object ProgramPhase:

  /** Why a name is program-dependent: the names through which it reaches the program, ending with the
   *  form that names the program (`programOf here` or `here ⊢ …`); whether the scope is a module body. */
  final case class Dependence(chain: List[String], body: Boolean)

  /** The program-dependent items of a scope, and what the elaboration before them needs to know of them:
   *  the names they declare, the functions they define by clauses, the names their `%opaque` directives
   *  name, and why each declared name is program-dependent. */
  final case class Deferred(
      items: List[Item],
      declared: Set[Name],
      functions: Set[Name],
      opaque: Set[Name],
      chains: Map[Name, List[String]]
  ):
    def isEmpty: Boolean = items.isEmpty

    /** What the items before them read of them (comparable: an edit inside a proof keeps it). */
    def names: (Set[Name], Set[Name], Set[Name], Map[Name, List[String]]) = (declared, functions, opaque, chains)

  object Deferred:
    val empty: Deferred = Deferred(Nil, Set.empty, Set.empty, Set.empty, Map.empty)

  /** The items of a scope split into those elaborated before its object items and the program-dependent
   *  ones. `programOfFree`: whether `programOf` is the form (the scope does not declare the name).
   *  `deferrable`: whether a program-dependent item can be elaborated after the object items (`%use`, a
   *  subtyping edge, an object constant of a body cannot: they are elaborated before, where the use of a
   *  program-dependent name is E0962). */
  def classify(items: List[Item], programOfFree: Boolean, deferrable: Item => Boolean): (List[Item], Deferred) =
    val direct = items.zipWithIndex.flatMap((it, i) => if mayMentionHere(it) then usesHere(it, programOfFree).map(i -> _) else None)
    if direct.isEmpty then (items, Deferred.empty)
    else
      val owners = items.map(owner).toVector
      val mentioning = mutable.HashMap.empty[Name, List[Int]]
      for (it, i) <- items.zipWithIndex; n <- ElabOrder.mentions(it) if !owners(i).contains(n) do
        mentioning(n) = i :: mentioning.getOrElse(n, Nil)
      val chains = mutable.LinkedHashMap.empty[Name, List[String]]
      val dependentItems = mutable.Set.empty[Int]
      val todo = mutable.Queue.empty[Name]
      def mark(i: Int, chain: List[String]): Unit =
        if dependentItems.add(i) then
          owners(i).foreach { n =>
            if !chains.contains(n) then
              chains(n) = n :: chain
              todo.enqueue(n)
          }
      for (i, form) <- direct do mark(i, List(form))
      while todo.nonEmpty do
        val n = todo.dequeue()
        for i <- mentioning.getOrElse(n, Nil).reverse do mark(i, chains(n))
      val isDeferred = items.indices.map(i => (dependentItems(i) || owners(i).exists(chains.contains)) && deferrable(items(i)))
      val (later, now) = items.zip(isDeferred).partition(_._2)
      val deferredItems = later.map(_._1)
      val declaredNames = deferredItems.flatMap(owner).toSet
      val functions = deferredItems.collect {
        case c: Clause => TreeOps.headName(c.lhs).map(_.name)
        case d: Def if deferredItems.exists { case e: Decl => e.name.name == d.name.name; case _ => false } => Some(d.name.name)
      }.flatten.toSet
      val opaque =
        deferredItems.collect { case Directive("opaque", DirArgs.Apply(args, None)) => args.collect { case Ident(n) => n } }.flatten.toSet
      // only the names that are elaborated later are reported as cycles where they are used
      val deferredChains = chains.view.filterKeys(declaredNames).toMap
      (now.map(_._1), Deferred(deferredItems, declaredNames, functions, opaque, deferredChains))

  /** The name an item belongs to: a declaration's or definition's, a clause's function, a rule's head
   *  (the rules of a formula function among the declarations). */
  private def owner(item: Item): Option[Name] = item match
    case d: Decl => Some(d.name.name)
    case d: Def => Some(d.name.name)
    case c: Clause => TreeOps.headName(c.lhs).map(_.name)
    case r: Rule => r.heads.headOption.flatMap(TreeOps.headName).map(_.name)
    case _ => None

  /** Whether the text of an item has the word `here` (an item without a position is walked). */
  private def mayMentionHere(item: Item): Boolean =
    val sp = item.span
    if !sp.exists then true
    else
      // within the item's text only (an item without a slice of its own has the whole file as its origin)
      val s = sp.origin.content
      val end = sp.until.min(s.length) - 4
      def ident(ch: Char) = ch.isLetterOrDigit || ch == '_' || ch == '\''
      var i = sp.from.max(0)
      var found = false
      while !found && i <= end do
        if s.charAt(i) == 'h' && s.startsWith("here", i) && (i == 0 || !ident(s.charAt(i - 1))) &&
          (i + 4 >= s.length || !ident(s.charAt(i + 4)))
        then found = true
        i += 1
      found

  private def isHere(t: Any): Boolean = t match
    case Ident("here") => true
    case Parens(i) => isHere(i)
    case _ => false

  /** The form in which an item names the program of its scope, outside the module bodies it contains. */
  def usesHere(item: Item, programOfFree: Boolean): Option[String] =
    val todo = mutable.ArrayBuffer[Any](item)
    var found: Option[String] = None
    while found.isEmpty && todo.nonEmpty do
      todo.remove(todo.length - 1) match
        case _: ModuleBody =>
        case Judgment(p, db, atom) =>
          if isHere(p) then found = Some("here ⊢ …")
          else
            todo += p
            todo ++= db
            todo += atom
        case Apply(Ident("programOf"), a) if programOfFree && isHere(a) => found = Some("programOf here")
        case p: Product => todo ++= p.productIterator
        case it: Iterable[?] => todo ++= it
        case _ =>
    found
