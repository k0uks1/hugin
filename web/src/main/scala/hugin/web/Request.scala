package hugin.web

import hugin.compiler.{Compiler, Display, Settings}
import hugin.util.diagnostics.{Level, Lint}
import scala.scalajs.js

/** The options of a `check` or `run` call (the `options` object of [[Hugin]]), as the command line's. */
final case class Request(
    file: String = "main.hgn",
    settings: Settings = Settings(),
    display: Display = Display(),
    allRelations: Boolean = false,
    budgetMs: Option[Double] = None
)

object Request:
  /** Reads an options object (or its JSON text); `Left` names the first invalid option. Unknown fields are ignored.
   *
   *  - `file` (string): the program's file name, used in diagnostics (default `main.hgn`)
   *  - `printAfter` (string or array of strings): `--print-after`, phase names or `all`
   *  - `stopAfter` (string): `--stop-after`
   *  - `prelude` (boolean, default true): `false` is `--no-prelude`
   *  - `explainTermination`, `allRelations`, `denyWarnings` (booleans): the flags of the same names
   *  - `lints` (object): lint name or code to `"allow"`, `"warn"` or `"deny"` (`-A`, `-W`, `-D`)
   *  - `budgetMs` (number): evaluation stops at its next round after this many milliseconds
   */
  def read(options: js.UndefOr[js.Any]): Either[String, Request] =
    if options.isEmpty || options.get == null then Right(Request())
    else
      // an object, or its JSON text
      val o = (options.get: Any) match
        case text: String => js.JSON.parse(text).asInstanceOf[js.Dictionary[js.Any]]
        case obj => obj.asInstanceOf[js.Dictionary[js.Any]]
      def field[A](name: String)(pick: PartialFunction[Any, A]): Either[String, Option[A]] =
        o.get(name).filter(v => !js.isUndefined(v) && v != null) match
          case None => Right(None)
          case Some(v) => pick.lift(v).map(Some(_)).toRight(s"invalid option `$name`")
      val str: PartialFunction[Any, String] = { case s: String => s }
      val bool: PartialFunction[Any, Boolean] = { case b: Boolean => b }
      for
        file <- field("file")(str)
        printAfter <- field("printAfter") {
          case s: String => List(s)
          case a: js.Array[?] @unchecked if a.forall(_.isInstanceOf[String]) => a.toList.map(_.toString)
        }
        stopAfter <- field("stopAfter")(str)
        prelude <- field("prelude")(bool)
        explain <- field("explainTermination")(bool)
        all <- field("allRelations")(bool)
        deny <- field("denyWarnings")(bool)
        budget <- field("budgetMs") { case d: Double if d >= 0 => d }
        lints <- field("lints") { case d: js.Object => d.asInstanceOf[js.Dictionary[Any]].toList }
        phases = printAfter.getOrElse(Nil) ++ stopAfter
        _ <- phases.find(p => p != "all" && !Compiler.allPhaseNames.contains(p)).map(p => s"unknown phase `$p`").toLeft(())
        levels <- lints.getOrElse(Nil).foldLeft[Either[String, hugin.util.diagnostics.LintLevels]](Right(Display().lints)) {
          case (acc, (name, level)) =>
            for
              ls <- acc
              lint <- Lint.parse(name).toRight(s"unknown lint `$name`")
              lv <- levelOf(level).toRight(s"invalid level for lint `$name`: expected allow, warn or deny")
            yield ls.set(lint, lv)
        }
      yield Request(
        file.getOrElse("main.hgn"),
        Settings(printAfter.getOrElse(Nil).toSet, stopAfter, prelude.getOrElse(true), explain.getOrElse(false)),
        Display(lints = levels.copy(denyWarnings = deny.getOrElse(false))),
        all.getOrElse(false),
        budget
      )

  private def levelOf(v: Any): Option[Level] = v match
    case "allow" => Some(Level.Allow)
    case "warn" => Some(Level.Warning)
    case "deny" => Some(Level.Error)
    case _ => None
