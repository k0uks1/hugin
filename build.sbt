ThisBuild / scalaVersion := "3.3.4"
ThisBuild / organization := "hugin"
ThisBuild / version := "0.1.0"

lazy val root = (project in file("."))
  .settings(
    name := "hugin",
    scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked", "-Wunused:imports"),
    libraryDependencies += "org.scalameta" %% "munit" % "1.0.2" % Test,
    Compile / mainClass := Some("hugin.Main"),
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value,
    run / fork := true,
    run / connectInput := true,
    Global / cancelable := true
  )
