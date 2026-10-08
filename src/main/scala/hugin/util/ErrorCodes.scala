package hugin.util

import hugin.util.diagnostics.Code

/** The short explanations of the codes, printed by `hugin explain` and `:explain`; titles and properties
 *  live in the registry, [[Code]]. */
object ErrorCodes:
  val explanations: Map[Code, String] = Map(
    // syntax and names
    Code.E0001 -> "The parser found a token it did not expect. Parsing resumes at the next item.",
    Code.E0002 -> "A `(*` comment or string literal reaches the end of the file.",
    Code.E0003 -> "An integer literal does not fit into 64 bits, or a string contains an invalid escape.",
    Code.E0004 -> "The item does not have the shape of a declaration, definition, rule, query or directive.",
    Code.E0101 -> "A name is not declared in any enclosing scope (Section 2.3).",
    Code.E0102 -> "A name is declared twice in the same scope.",
    Code.E0103 -> "The item cannot be classified by stage (Section 2.5), e.g. a constructor whose result is not an open type.",
    Code.E0104 -> "Type definitions may be used before their declaration but must not form a cycle.",
    Code.E0105 -> "Meta definitions may only refer to earlier definitions; the meta level has no recursion.",
    Code.E0106 -> "A type definition whose right-hand side does not mention every parameter must be marked %abbrev (Section 4.7).",
    Code.E0107 -> "A path `m.x` requires `m` to be module-valued.",
    Code.E0108 -> "An imported file does not exist, or files import each other in a cycle. A file is a module body that is elaborated before the files importing it, so imports must form an acyclic graph.",
    // stage and meta typing
    Code.E0201 -> "An object variable occurs where a meta value of primitive type, `type`, a record or a function is required (Section 3.2).",
    Code.E0202 -> "A meta value is used at the object level where it cannot be spliced, or an object entity is used where a meta value of another kind is required.",
    Code.E0203 -> "A meta expression does not have the expected meta type (Section 4.3).",
    Code.E0204 -> "An argument does not match the parameter signature (Section 4.4).",
    Code.E0205 -> "Within a recursive component, a family is used at type arguments different from those being instantiated (Definition 4.2).",
    Code.E0206 -> "An implicit type parameter or family type argument is not determined by first-order matching.",
    Code.E0207 -> "A relation, constructor, family or formula function is applied to the wrong number of arguments.",
    Code.E0208 -> "A signature requires %complete or %mode of a relation argument which the argument does not satisfy.",
    Code.E0209 -> "A primitive operation evaluated at the meta level is undefined (overflow or division by zero).",
    Code.E0210 -> "A functor that negates or aggregates over a relation parameter must require %complete in its signature (Section 11).",
    // records
    Code.E0301 -> "A named pattern must mention every label, unless it ends in `..`.",
    Code.E0302 -> "Rest patterns are forbidden in rule heads, since the omitted columns would be unknown.",
    Code.E0303 -> "Projection and update require a closed type (a fact type or a union of closed types).",
    Code.E0304 -> "Every member of the projected type must have the label.",
    Code.E0305 -> "The label has types in different members whose join is undefined.",
    Code.E0306 -> "The relation has no column with this label.",
    Code.E0307 -> "A label occurs twice.",
    // object typing
    Code.E0401 -> "The meet of the expected types of a variable is empty (Definition 6.1).",
    Code.E0402 -> "A term does not have a subtype of the expected type.",
    Code.E0404 -> "Declarations must satisfy Section 5.4.",
    Code.E0405 -> "An ascription (t : T) must select members of the type of t.",
    Code.E0406 -> "A constructor or struct declared without `%fact` is a data constructor: it builds values, which are not facts of a relation. It cannot be read by an atom (in a body, a negation, an aggregate or a query), derived by a rule head, named by a directive, or passed where a relation is expected; terms built with it are allowed everywhere. Declare it `%fact c : τ1 -> ... -> a.` to read its facts, and require `%fact c : ...` in a signature to read a constructor field inside a functor.",
    // moding
    Code.E0501 -> "The rule is not range-restricted: a variable is not bound by the body in the canonical order (Section 6.3).",
    Code.E0502 -> "A moded relation or primitive is called without any applicable mode.",
    Code.E0503 -> "Input positions of the heads of moded relations must be patterns (Section 7.3).",
    Code.E0504 -> "An input argument of a call of a moded relation (in a body, under `not`, in an aggregate or in a query) contains a term of a `%fact` constructor. The demand transformation builds the inputs of a call, which would make that term a fact, so `%mode` would change the database. Remove `%fact` if the constructor is only used as a value, or bind an existing fact to a variable first (`S = c t`, an existence check) and pass the variable. Input columns of the moded relation's own rule heads are patterns and are not affected.",
    // checks
    Code.E0601 -> "A cycle of the dependency graph contains a negative edge (Section 6.4).",
    Code.E0602 -> "The completeness discipline forbids negative edges to possibly incomplete relations (Definition 6.6).",
    Code.E0603 -> "A recursive component with a constructive rule must terminate by descent along derivations (an argument decreases from premise to conclusion in every cycle) or by guarded induction (a measure decreases along every recursive call and is bound by a guard) (Section 10, docs/NOTES.md). There are no round budgets: a program that cannot be shown to terminate is rejected.",
    Code.E0604 -> "A recursive call does not decrease the measure, the measure is not bounded (an anchor is missing), or a measured relation calls a relation of its component without a measure (Definition 10.3 as generalised in docs/NOTES.md). `--explain-termination` shows the accepted justifications.",
    Code.E0605 -> "A bound column type `min τ` / `max τ` is allowed only as the last column of a relation declaration (not of a constructor, struct or signature field), with an integer type `τ`, and not on a relation with `%mode` (docs/REDESIGN.md §5.2).",
    Code.E0606 -> "A rule reads a bound column of a relation of its own recursive component in a way that is not monotone (Kaminski et al. 2017, Berent et al. Def. 4): the value must occur in exactly one atom, linearly (non-zero integer coefficients), only in the bound column of a bound head and in `<`, `<=`, `>`, `>=` comparisons, in the direction in which improving it improves the head or keeps the comparison true: for a `min` head (or the smaller side of a comparison) with a positive coefficient from `min` columns and a negative one from `max` columns, dually for `max`. Values of bound relations of earlier components are constants and can be used freely.",
    Code.E0701 -> "A directive refers to a relation of the wrong kind or arity.",
    Code.E0801 -> "An input fact is not ground, not well-typed, or not for an input relation.",
    Code.W0001 -> "An object-level expression over literals is undefined, so the rule can never fire.",
    Code.W0002 -> "A variable occurs only once in a rule; use `_` if this is intended.",
    Code.W0003 -> "A top-level meta function, formula function or constant is never referenced.",
    Code.W0005 -> "A formula function is declared without clauses or definition; it is always false."
  )

  /** The explanation of a code (case-insensitive) as printed by `hugin explain` and `:explain`. */
  def explain(code: String): Option[String] =
    Code.parse(code).map(c => s"${c.id}: ${c.title}\n\n${explanations.getOrElse(c, "")}")
