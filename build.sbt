ThisBuild / scalaVersion := "3.3.4"
ThisBuild / organization := "hugin"
ThisBuild / version := "0.1.0"

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
      "org.jgrapht" % "jgrapht-core" % "1.5.2", // SCCs, topological order, shortest paths
      "org.apache.commons" % "commons-text" % "1.12.0", // edit distance for suggestions
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
