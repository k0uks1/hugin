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
    ("E0403", "cannot infer type", "A variable has neither an expected type nor a defining equation."),
    ("E0404", "ill-formed declaration", "Declarations must satisfy Section 5.4."),
    ("E0405", "invalid ascription", "An ascription (t : T) must select members of the type of t."),
    // moding
    (
      "E0501",
      "unbound variable",
      "The rule is not range-restricted: a variable is not bound by the body in the canonical order (Section 6.3)."
    ),
    ("E0502", "call without applicable mode", "A moded relation or primitive is called without any applicable mode."),
    ("E0503", "input position is not a pattern", "Input positions of the heads of moded relations must be patterns (Section 7.3)."),
    // checks
    ("E0601", "stratification cycle through negation", "A cycle of the dependency graph contains a negative edge (Section 6.4)."),
    (
      "E0602",
      "negation or aggregation over an incomplete relation",
      "The completeness discipline forbids negative edges to possibly incomplete relations (Definition 6.6)."
    ),
    (
      "E0603",
      "growing component without valid %terminates",
      "A recursive component with a constructive rule needs a valid %terminates directive or a %partial relation (Section 10)."
    ),
    ("E0604", "invalid %terminates directive", "The directive does not satisfy Definition 10.3."),
    ("E0701", "invalid directive", "A directive refers to a relation of the wrong kind or arity."),
    ("E0801", "invalid input fact", "An input fact is not ground, not well-typed, or not for an input relation."),
    ("W0001", "undefined constant expression", "An object-level expression over literals is undefined, so the rule can never fire."),
    ("W0002", "singleton variable", "A variable occurs only once in a rule; use `_` if this is intended."),
    ("W0003", "unused definition", "A top-level meta function, formula function or constant is never referenced."),
    ("W0005", "formula function without clauses", "A formula function is declared without clauses or definition; it is always false."),
    (
      "W0004",
      "nested facts of an earlier component",
      "A rule constructs nested facts of a relation that is evaluated earlier; readers evaluated in between may miss them."
    )
  )

  def lookup(code: String): Option[(String, String, String)] = all.find(_._1 == code)
