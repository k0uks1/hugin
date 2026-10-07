package hugin.util

/** Catalog of diagnostic codes (Appendix A.1), used by `hugin explain`. */
object ErrorCodes:
  val all: List[(String, String, String)] = List(
    // syntax and names
    ("E0001", "syntax error", "The parser found a token it did not expect. Parsing resumes at the next item."),
    ("E0002", "unterminated comment or string", "A `(*` comment or string literal reaches the end of the file."),
    ("E0003", "invalid literal", "An integer literal does not fit into 64 bits, or a string contains an invalid escape."),
    ("E0004", "malformed item", "The item does not have the shape of a declaration, definition, rule, query or directive."),
    ("E0101", "unresolved name", "A name is not declared in any enclosing scope (Section 2.3)."),
    ("E0102", "duplicate declaration", "A name is declared twice in the same scope."),
    (
      "E0103",
      "misclassified item",
      "The item cannot be classified by stage (Section 2.5), e.g. a constructor whose result is not an open type."
    ),
    ("E0104", "cyclic type definition", "Type definitions may be used before their declaration but must not form a cycle."),
    ("E0105", "forward reference", "Meta definitions may only refer to earlier definitions; the meta level has no recursion."),
    (
      "E0106",
      "non-strict type definition",
      "A type definition whose right-hand side does not mention every parameter must be marked %abbrev (Section 4.7)."
    ),
    ("E0107", "not a module", "A path `m.x` requires `m` to be module-valued."),
    (
      "E0108",
      "import error",
      "An imported file does not exist, or files import each other in a cycle. A file is a module body that is elaborated before the files importing it, so imports must form an acyclic graph."
    ),
    // stage and meta typing
    (
      "E0201",
      "runtime value used at compile time",
      "An object variable occurs where a meta value of primitive type, `type`, a record or a function is required (Section 3.2)."
    ),
    (
      "E0202",
      "stage error",
      "A meta value is used at the object level where it cannot be spliced, or an object entity is used where a meta value of another kind is required."
    ),
    ("E0203", "meta type mismatch", "A meta expression does not have the expected meta type (Section 4.3)."),
    ("E0204", "signature mismatch", "An argument does not match the parameter signature (Section 4.4)."),
    (
      "E0205",
      "polymorphic recursion",
      "Within a recursive component, a family is used at type arguments different from those being instantiated (Definition 4.2)."
    ),
    (
      "E0206",
      "cannot infer type argument",
      "An implicit type parameter or family type argument is not determined by first-order matching."
    ),
    ("E0207", "arity mismatch", "A relation, constructor, family or formula function is applied to the wrong number of arguments."),
    (
      "E0208",
      "unsatisfied requirement",
      "A signature requires %complete or %mode of a relation argument which the argument does not satisfy."
    ),
    (
      "E0209",
      "compile-time arithmetic failure",
      "A primitive operation evaluated at the meta level is undefined (overflow or division by zero)."
    ),
    (
      "E0210",
      "negation over a parameter without %complete",
      "A functor that negates or aggregates over a relation parameter must require %complete in its signature (Section 11)."
    ),
    // records
    ("E0301", "missing labels in named pattern", "A named pattern must mention every label, unless it ends in `..`."),
    ("E0302", "`..` in a head", "Rest patterns are forbidden in rule heads, since the omitted columns would be unknown."),
    (
      "E0303",
      "projection on a type that is not closed",
      "Projection and update require a closed type (a fact type or a union of closed types)."
    ),
    ("E0304", "no common label", "Every member of the projected type must have the label."),
    ("E0305", "undefined join", "The label has types in different members whose join is undefined."),
    ("E0306", "unknown label", "The relation has no column with this label."),
    ("E0307", "duplicate label", "A label occurs twice."),
    // object typing
    ("E0401", "no value can occur in all these positions", "The meet of the expected types of a variable is empty (Definition 6.1)."),
    ("E0402", "type mismatch", "A term does not have a subtype of the expected type."),
    ("E0404", "ill-formed declaration", "Declarations must satisfy Section 5.4."),
    ("E0405", "invalid ascription", "An ascription (t : T) must select members of the type of t."),
    (
      "E0406",
      "data constructor used as a relation",
      "A constructor or struct declared without `%fact` is a data constructor: it builds values, which are not facts of a relation. It cannot be read by an atom (in a body, a negation, an aggregate or a query), derived by a rule head, named by a directive, or passed where a relation is expected; terms built with it are allowed everywhere. Declare it `%fact c : τ1 -> ... -> a.` to read its facts, and require `%fact c : ...` in a signature to read a constructor field inside a functor."
    ),
    // moding
    (
      "E0501",
      "unbound variable",
      "The rule is not range-restricted: a variable is not bound by the body in the canonical order (Section 6.3)."
    ),
    ("E0502", "call without applicable mode", "A moded relation or primitive is called without any applicable mode."),
    ("E0503", "input position is not a pattern", "Input positions of the heads of moded relations must be patterns (Section 7.3)."),
    (
      "E0504",
      "fact constructor built in a moded input",
      "An input argument of a call of a moded relation (in a body, under `not`, in an aggregate or in a query) contains a term of a `%fact` constructor. The demand transformation builds the inputs of a call, which would make that term a fact, so `%mode` would change the database. Remove `%fact` if the constructor is only used as a value, or bind an existing fact to a variable first (`S = c t`, an existence check) and pass the variable. Input columns of the moded relation's own rule heads are patterns and are not affected."
    ),
    // checks
    ("E0601", "stratification cycle through negation", "A cycle of the dependency graph contains a negative edge (Section 6.4)."),
    (
      "E0602",
      "negation or aggregation over an incomplete relation",
      "The completeness discipline forbids negative edges to possibly incomplete relations (Definition 6.6)."
    ),
    (
      "E0603",
      "growing component without a termination argument",
      "A recursive component with a constructive rule must terminate by descent along derivations (an argument decreases from premise to conclusion in every cycle) or by guarded induction (a measure decreases along every recursive call and is bound by a guard) (Section 10, docs/NOTES.md). There are no round budgets: a program that cannot be shown to terminate is rejected."
    ),
    (
      "E0604",
      "invalid %terminates directive",
      "A recursive call does not decrease the measure, the measure is not bounded (an anchor is missing), or a measured relation calls a relation of its component without a measure (Definition 10.3 as generalised in docs/NOTES.md). `--explain-termination` shows the accepted justifications."
    ),
    (
      "E0605",
      "invalid bound column",
      "A bound column type `min τ` / `max τ` is allowed only as the last column of a relation declaration (not of a constructor, struct or signature field), with an integer type `τ`, and not on a relation with `%mode` (docs/REDESIGN.md §5.2)."
    ),
    (
      "E0606",
      "type-inconsistent rule",
      "A rule reads a bound column of a relation of its own recursive component in a way that is not monotone (Kaminski et al. 2017, Berent et al. Def. 4): the value must occur in exactly one atom, linearly (non-zero integer coefficients), only in the bound column of a bound head and in `<`, `<=`, `>`, `>=` comparisons, in the direction in which improving it improves the head or keeps the comparison true: for a `min` head (or the smaller side of a comparison) with a positive coefficient from `min` columns and a negative one from `max` columns, dually for `max`. Values of bound relations of earlier components are constants and can be used freely."
    ),
    ("E0701", "invalid directive", "A directive refers to a relation of the wrong kind or arity."),
    ("E0801", "invalid input fact", "An input fact is not ground, not well-typed, or not for an input relation."),
    ("W0001", "undefined constant expression", "An object-level expression over literals is undefined, so the rule can never fire."),
    ("W0002", "singleton variable", "A variable occurs only once in a rule; use `_` if this is intended."),
    ("W0003", "unused definition", "A top-level meta function, formula function or constant is never referenced."),
    ("W0005", "formula function without clauses", "A formula function is declared without clauses or definition; it is always false.")
  )

  def lookup(code: String): Option[(String, String, String)] = all.find(_._1 == code)

  /** The explanation of a code (case-insensitive) as printed by `hugin explain` and `:explain`. */
  def explain(code: String): Option[String] = lookup(code.toUpperCase).map((c, title, text) => s"$c: $title\n\n$text")
