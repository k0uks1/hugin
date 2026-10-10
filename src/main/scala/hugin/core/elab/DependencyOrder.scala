package hugin.core
package elab

import hugin.syntax.Trees.*
import scala.collection.mutable

/** The elaboration of a file's declarations by the components of their dependency graph ([[ElabOrder]];
 *  reference: meta/index, "Order of elaboration"). In each component, the declarations, definitions and
 *  signatures come first (retried in source order for forward references, [[Items.elabInDependencyOrder]]),
 *  then the derived functions, the clause groups and the rules of formula functions, each a block. While a
 *  component is elaborated, its functions, definitions and formula functions are *sealed*: no body of the
 *  component unfolds in the component, whatever the written order (as in Lean's mutual blocks and Rocq's
 *  `Fix`). At its end, the termination of its functions and the cycles of its formula functions are
 *  checked; then its bodies unfold for the later components. */
trait DependencyOrder:
  self: Elaborator =>
  import core.*

  /** The names of the component being elaborated whose bodies are sealed, in source order (for the note on
   *  stuck applications, [[ElabErrors]]). */
  var cycleNames: List[Name] = Nil

  private var sealing = false
  private val sealedHere = mutable.ArrayBuffer.empty[Int]

  /** The case trees of the component's functions and the values of its definitions and formula
   *  functions, installed when the component is done: until then a function has no case tree and a
   *  definition is a postulate, so they do not unfold, at no cost to evaluation. */
  val withheld: mutable.Map[Int, GlobalKind] = mutable.Map.empty

  /** The kind of a global, also while it is withheld (for the checks that read definitions' terms). */
  def kindOf(id: Int): GlobalKind = withheld.getOrElse(id, globals(id).kind)

  /** Typed definitions of the component declared with their type before their value ([[provisionalSignatures]]). */
  val provisional: mutable.Set[Int] = mutable.Set.empty

  /** Elaborates the plain items (declarations, definitions, `%use`, subtyping edges), the clause groups and
   *  the formula functions with their rules (and the position of their declaration) by components. */
  def elabByComponents(plain: List[Item], groups: List[(Name, List[Item])], rules: List[(Name, List[Rule], Int)]): Unit =
    val shared = plain.collect { case d: Decl if isDataDecl(d) => d.name.name }.toSet
    val constructors = plain.collect { case d: Decl if d.defn.isEmpty && ElabOrder.codomainHead(d).exists(shared) => d.name.name }
    // the file declares the compiler-known names itself (the standard library): every body may need them
    val implicitNeeds = if coreOutside then Set.empty[Name] else compilerNames.toSet
    val plan = ElabOrder.plan(
      ElabOrder.Input(
        plain.map(i => (i, mightDeclare(i))),
        groups,
        rules,
        Option.when(shared.nonEmpty)(shared ++ constructors),
        implicitNeeds,
        n => file.parent.contains(n) || file.builtinNames && builtinTypes.contains(n)
      )
    )
    // without the clauses of functions, those that a declaration needs are elaborated all the same
    lazy val needed = plan.neededBySignatures
    def wanted(i: Int) = !file.signaturesOnly || needed(i)
    for component <- plan.components do
      val nodes = component.map(i => (i, plan.nodes(i)))
      cycleNames = nodes.flatMap((_, n) => bodyNames(n)).distinct
      sealing = true
      // the functions and formula functions whose signatures came in earlier components
      for (_, n) <- nodes if n.kind != ElabOrder.Kind.Plain; f <- bodyNames(n); id <- scope.get(f) do seal(id)
      val (uses, others) = nodes.collect { case (_, n) if n.kind == ElabOrder.Kind.Plain => n.items }.flatten.partition(isUse)
      elabInDependencyOrder(uses ++ others)
      // the derived functions are generated code: nothing to show for their positions
      if nodes.exists(_._2.kind == ElabOrder.Kind.Derived) then withoutTooling(defineSharedFunctions())
      for case (i, ElabOrder.Node(ElabOrder.Kind.Clauses(f), items, _)) <- nodes if wanted(i) do
        scope.get(f).foreach(seal)
        elabClauseGroup(f, items)
      val defined = for
        case (i, ElabOrder.Node(ElabOrder.Kind.Rules(f), items, _)) <- nodes
        if wanted(i) && !state.unelaborated(f) && scope.get(f).exists(globals(_).kind == GlobalKind.Postulate)
      yield
        val rs = items.collect { case r: Rule => r }
        scope.get(f).foreach(seal)
        inBlock(elabFormulaClauses(f, rs))
        scope.get(f).foreach(seal)
        (f, rs)
      // the component's call cycles and formula cycles are known: its bodies may unfold now
      checkTermination()
      for (f, kind) <- withheld if !rejectedByTermination(f) do globals(f).kind = kind
      withheld.clear()
      checkFormulaCycles(defined)
      sealedHere.foreach(globals(_).inCycle = false)
      sealedHere.clear()
      provisional.clear()
      sealing = false
      cycleNames = Nil

  /** The functions, definitions and formula functions a node gives a body. */
  private def bodyNames(n: ElabOrder.Node): List[Name] = n.kind match
    case ElabOrder.Kind.Clauses(f) => List(f)
    case ElabOrder.Kind.Rules(f) => List(f)
    case ElabOrder.Kind.Derived => Nil
    case ElabOrder.Kind.Plain =>
      n.items.collect {
        case d: Def => d.name.name
        case d: Decl if d.defn.isDefined => d.name.name
      }

  /** Seals what an item of the component being elaborated declared. */
  def sealDeclared(item: Item): Unit = if sealing then declares(item).flatMap(scope.get).foreach(seal)

  /** Seals a function, a formula function or a definition of a meta value; object type definitions are
   *  object-level aliases, which object declarations in the same cycle need to see. */
  private def seal(id: Int): Unit =
    val g = globals(id)
    val objectType = g.kind.isInstanceOf[GlobalKind.Definition] && force(telescope(g.ty)._2) == Val.Lift(Val.U0)
    if !objectType && g.stage == Stage.S1 then
      if !g.inCycle then
        g.inCycle = true
        sealedHere += id
      g.kind match
        case d: GlobalKind.Definition =>
          withheld(id) = d
          g.kind = GlobalKind.Postulate
        case _ =>

  /** No item of `pending` could be elaborated: the typed definitions among them that wait for a signature
   *  (a declaration without definition) of the same component are declared with their type alone, so
   *  that the signature can refer to them; their values follow ([[Declarations.define]]). Whether any
   *  was declared. */
  def provisionalSignatures(pending: List[(Item, Option[ElabError])]): Boolean =
    val signatures = pending.collect { case (d: Decl, _) if d.defn.isEmpty => d.name.name }.toSet
    val waiting = pending.collect {
      case (d @ Decl(n, _, tpe, None, Some(e)), Some(err))
          if err.unresolved.exists(signatures) && !scope.contains(n.name) && definitionWithType(tpe, e) =>
        d
    }
    waiting.count { d =>
      inBlock {
        val start = metas.length
        try
          withoutTooling(undoOnFailure {
            declareSignature(d)
            checkSolved(start)
          })
          scope.get(d.name.name).foreach(seal)
          true
        catch case _: ElabError => false
      }
    } > 0

  /** A definition `x : A = e.` whose value can follow its type: not a type definition, a builtin or a
   *  module body (those are elaborated as a whole). */
  private def definitionWithType(tpe: hugin.syntax.Tree, e: hugin.syntax.Tree): Boolean = (tpe, e) match
    case (Keyword(_), _) | (_, _: Builtin) | (_, _: ModuleBody) => false
    case (VarRef("Type"), _) => false
    case _ => true

  /** A typed definition declared provisionally whose value failed: its name is dropped. */
  def dropProvisional(item: Item): Unit =
    for n <- declares(item); id <- scope.get(n) if provisional(id) do
      withheld -= id
      globals(id).kind = GlobalKind.Postulate
      scope.remove(n)
