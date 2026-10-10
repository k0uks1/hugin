ThisBuild / scalaVersion := "3.3.4"
ThisBuild / organization := "hugin"
ThisBuild / version := "0.1.0"
ThisBuild / licenses := List("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0"))

lazy val root = (project in file("."))
  .enablePlugins(JavaAppPackaging)
  .settings(
    name := "hugin",
    scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked", "-Wunused:imports"),
    // warnings are errors on CI
    scalacOptions ++= (if (sys.env.contains("CI")) Seq("-Werror") else Nil),
    libraryDependencies ++= Seq(
      "com.github.scopt" %% "scopt" % "4.1.0", // command-line parsing
      "com.lihaoyi" %% "fansi" % "0.5.0", // ANSI colours in diagnostics
      "org.jline" % "jline" % "3.27.1", // line editing, history and completion in the REPL
      "org.eclipse.lsp4j" % "org.eclipse.lsp4j" % "0.23.1", // language server protocol (with its JSON-RPC layer)
      "org.scalameta" %% "munit" % "1.0.2" % Test,
      "org.scalameta" %% "munit-scalacheck" % "1.0.0" % Test
    ),
    // `sbt stage` produces target/universal/stage/bin/hugin
    executableScriptName := "hugin",
    Universal / javaOptions ++= Seq("-J-Xss64m"),
    Compile / mainClass := Some("hugin.cli.Main"),
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value,
    run / fork := true,
    run / connectInput := true,
    Global / cancelable := true
  )

// `sbt fuzz`: the long run of the fuzz suites (hugin.fuzz): 2000 tests per property from a random seed;
// HUGIN_FUZZ_COUNT and HUGIN_FUZZ_SEED in the environment override both (see README, "Fuzz testing")
addCommandAlias("fuzz", "set Test / javaOptions += \"-Dhugin.fuzz.long=true\"; testOnly hugin.fuzz.*")

// the explanations of the diagnostic codes (docs/errors/EXXXX.md) are resources `/hugin/errors/EXXXX.md`,
// printed by `hugin explain` without the repository at hand
Compile / resourceGenerators += Def.task {
  val out = (Compile / resourceManaged).value / "hugin" / "errors"
  val docs = ((ThisBuild / baseDirectory).value / "docs" / "errors" * "*.md").get
  docs.map { f =>
    val target = out / f.getName
    IO.copyFile(f, target)
    target
  }
}.taskValue

// the URL of the published language reference (reference/site-url.txt, its single source) is the resource
// `/hugin/site-url.txt`: the base of the links to the error index printed by `hugin explain`, sent by the
// language server (`codeDescription`) and included in the JSON diagnostics
Compile / resourceGenerators += Def.task {
  val source = (ThisBuild / baseDirectory).value / "reference" / "site-url.txt"
  val target = (Compile / resourceManaged).value / "hugin" / "site-url.txt"
  IO.copyFile(source, target)
  Seq(target)
}.taskValue
