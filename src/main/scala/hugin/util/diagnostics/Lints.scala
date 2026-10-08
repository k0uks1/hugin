package hugin.util.diagnostics

/** A named lint: a kind of warning that users may silence or turn into an error from the command line
 *  (`-A`, `-W`, `-D`, see [[LintLevels]]). Every warning code is the code of exactly one lint
 *  (`Code.lint`), whose default level is the code's level.
 *
 *  Names follow rustc's rule: lowercase with underscores, plural, reading well after "allow"
 *  ("allow singleton_variables"). A new warning is declared as a lint from the start. */
enum Lint(val name: String):
  case UndefinedConstantExpressions extends Lint("undefined_constant_expressions")
  case SingletonVariables extends Lint("singleton_variables")
  case UnusedDefinitions extends Lint("unused_definitions")
  case EmptyFormulaFunctions extends Lint("empty_formula_functions")
  case UnreachableClauses extends Lint("unreachable_clauses")

  /** The warning code this lint reports. */
  def code: Code = Code.values.find(_.lint.contains(this)).getOrElse(sys.error(s"lint $name has no code"))

  def defaultLevel: Level = code.level

object Lint:
  /** A lint by its name, or by its code (`W0002`). */
  def parse(s: String): Option[Lint] = values.find(_.name == s.trim).orElse(Code.parse(s).flatMap(_.lint))
