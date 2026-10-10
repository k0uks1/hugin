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

// The browser build of the compiler (issue #58, docs/design/website.md, "No-move variant"): Scala.js compiles
// the shared sources in src/main/scala, without the JVM-only packages, together with web/src/main/scala (the
// JS `hugin.platform.Platform` and the playground API `hugin.web`). A shared package that imports a JVM-only
// package or uses a JVM-only API breaks this build only; CI links it and runs tests/run through it.
// `sbt web/fullLinkJS` links web/target/scala-3.3.4/hugin-web-opt/main.js (a classic script, what the Site
// workflow takes); `sbt web/bundle` copies it to web/target/bundle/hugin.js and adds hugin.mjs (an ES module).
lazy val jvmOnlyPackages = Seq("cli", "repl", "lsp", "platform")
lazy val bundle = taskKey[File]("link the browser bundle (fullLinkJS with Closure) into web/target/bundle")

lazy val web = (project in file("web"))
  .enablePlugins(ScalaJSPlugin)
  .settings(
    name := "hugin-web",
    scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked", "-Wunused:imports"),
    scalacOptions ++= (if (sys.env.contains("CI")) Seq("-Werror") else Nil),
    libraryDependencies += "com.lihaoyi" %%% "fansi" % "0.5.0",
    Compile / unmanagedSourceDirectories += (ThisBuild / baseDirectory).value / "src" / "main" / "scala",
    Compile / unmanagedSources / excludeFilter := {
      val shared = ((ThisBuild / baseDirectory).value / "src" / "main" / "scala" / "hugin").toPath
      val excluded = jvmOnlyPackages.map(shared.resolve)
      (Compile / unmanagedSources / excludeFilter).value || new SimpleFileFilter(f => excluded.exists(f.toPath.startsWith))
    },
    Compile / sourceGenerators += Def.task {
      val out = (Compile / sourceManaged).value / "hugin" / "platform" / "BundledResources.scala"
      Seq(BundledResources.generate((ThisBuild / baseDirectory).value, out))
    }.taskValue,
    // a classic script: fullLinkJS runs the Closure Compiler only for NoModule; hugin.mjs re-exports it
    scalaJSLinkerConfig ~= (_.withModuleKind(ModuleKind.NoModule)),
    Compile / fullLinkJS / scalaJSLinkerConfig ~= (_.withClosureCompiler(true)),
    bundle := {
      val report = (Compile / fullLinkJS).value.data
      val dir = (Compile / fullLinkJS / scalaJSLinkerOutputDirectory).value
      val text = IO.read(dir / report.publicModules.head.jsFileName, IO.utf8)
      val out = target.value / "bundle"
      IO.write(out / "hugin.js", text, IO.utf8)
      IO.write(out / "hugin.mjs", text + "\nexport { Hugin };\n", IO.utf8)
      streams.value.log.info(s"browser bundle in $out")
      out
    }
  )
