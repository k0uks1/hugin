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
      "A recursive component with a constructive rule must terminate by descent along derivations (an argument decreases from premise to conclusion in every cycle) or by guarded induction (a measure decreases along every recursive call and is bound by a guard), or have a %partial relation (Section 10, docs/NOTES.md)."
    ),
    (
      "E0604",
      "invalid %terminates directive",
      "A recursive call does not decrease the measure, the measure is not bounded (an anchor is missing), or a measured relation calls a relation of its component without a measure (Definition 10.3 as generalised in docs/NOTES.md). `--explain-termination` shows the accepted justifications."
    ),
    ("E0701", "invalid directive", "A directive refers to a relation of the wrong kind or arity."),
    ("E0801", "invalid input fact", "An input fact is not ground, not well-typed, or not for an input relation."),
    // the new meta level (docs/REDESIGN.md, Phase B; `--new-meta`)
    (
      "E0901",
      "mismatched types",
      "A term does not have the type expected by its context in the new meta level, and no coercion (stage adjustment, lift, record coercion) applies. Notes say why unification failed: an unknown that would contain itself (occurs check), that would mention a variable out of its scope, or that is applied to arguments that are not distinct variables (outside the pattern fragment)."
    ),
    (
      "E0902",
      "stage error",
      "Object code (rule variables, constructor terms, formulas) is used where a compile-time value is needed, or a compile-time value that is not object code (`⇑A`) or a primitive value is used as object code. Object code exists only at run time; the meta level computes at compile time and can only take object code as data of type `⇑A`."
    ),
    (
      "E0903",
      "cannot infer",
      "An implicit argument, the type of a variable or another unknown is not determined by elaboration. Add a type annotation or pass the argument."
    ),
    (
      "E0904",
      "universe inconsistency",
      "The universe levels required by the program have no solution. Levels are inferred and cumulative (`Type₀ : Type₁ : …`, and a type in `Typeᵢ` is in `Typeⱼ` for i ≤ j); `Type : Type` is excluded because it makes the meta level inconsistent and non-terminating."
    ),
    (
      "E0905",
      "not a function",
      "A term is applied to an argument but its type is not a function type (or a relation is applied to too many arguments)."
    ),
    (
      "E0906",
      "unknown or missing field",
      "A projection names a field the record type (or relation) does not have, or a record value lacks a field of its expected type."
    ),
    (
      "E0907",
      "not supported by the new meta level yet",
      "The construct is part of the language but not yet supported by the new meta level (`--new-meta`), which is developed in steps (docs/REDESIGN.md §10, Phase B)."
    ),
    (
      "E0908",
      "object-level function",
      "The object level is first order: object functions (lambdas at the object level) and relations or constructors over object types cannot be defined. Functions on object code are meta functions (formula functions, functors); families of relations are meta functions returning relations."
    ),
    (
      "E0909",
      "staging failure",
      "After evaluating the meta code of an object item, what remains is not object code: meta code spliced into it is stuck (it applies a postulated meta function or a variable), or a compile-time primitive value is undefined (overflow, division by zero)."
    ),
    ("E0910", "invalid rule head", "A rule head must be an atom (a relation applied to all of its columns) or a constructor term."),
    (
      "E0911",
      "non-covering clauses",
      "Meta functions are total: their clauses must cover every combination of constructors of the matched arguments. Cases that are impossible by the indices of the types (`head : vec A (suc N) -> A` applied to `vnil`) need no clause. The diagnostic shows a missing case."
    ),
    (
      "E0912",
      "possibly non-terminating meta function",
      "Meta functions must terminate: along every cycle of calls between functions, some argument must get structurally smaller (a proper constructor subterm of the clause's pattern). The check uses the size-change principle (Lee, Jones & Ben-Amram), so lexicographic orders, mutual recursion and permuted arguments are recognised."
    ),
    (
      "E0913",
      "non-positive occurrence",
      "An inductive family occurs in a non-positive position in the type of one of its constructors (to the left of an arrow, or inside an argument of another type). Such types make the meta level inconsistent and non-terminating, so they are rejected (strict positivity)."
    ),
    (
      "E0914",
      "invalid inductive declaration",
      "A constructor must return its family applied to all of its arguments, and its arguments must live in the family's universe (predicativity); clauses can only define meta functions, not constructors, families or object relations."
    ),
    (
      "E0915",
      "invalid pattern",
      "A clause's patterns must be uppercase variables (each bound once), `_`, constructors applied to their explicit arguments, or natural-number literals of a nat-like type, and every clause of a function has the same number of patterns. Matching must be decidable: a constructor pattern must be against an inductive type whose indices unify with the constructor's, or clearly do not."
    ),
    ("W0001", "undefined constant expression", "An object-level expression over literals is undefined, so the rule can never fire."),
    ("W0002", "singleton variable", "A variable occurs only once in a rule; use `_` if this is intended."),
    ("W0003", "unused definition", "A top-level meta function, formula function or constant is never referenced."),
    ("W0005", "formula function without clauses", "A formula function is declared without clauses or definition; it is always false."),
    ("W0006", "unreachable clause", "A clause of a meta function is never used: the clauses before it cover every case it matches.")
  )

  def lookup(code: String): Option[(String, String, String)] = all.find(_._1 == code)

  /** The explanation of a code (case-insensitive) as printed by `hugin explain` and `:explain`. */
  def explain(code: String): Option[String] = lookup(code.toUpperCase).map((c, title, text) => s"$c: $title\n\n$text")
