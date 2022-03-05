ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "systems.informal"
// TODO
// ThisBuild / homepage := Some(url("https://github.com/sbt/sbt-hello"))

// https://circe.github.io/circe/
val circeVersion = "0.14.1"
libraryDependencies ++= Seq(
  "io.circe" %% "circe-core",
  "io.circe" %% "circe-generic",
  "io.circe" %% "circe-parser",
).map(_ % circeVersion)

libraryDependencies ++= Seq(
  "commons-io" % "commons-io" % "2.11.0",
  "org.scala-sbt" % "sbt" % "1.6.2",
)

lazy val sbt_benchexec = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
    name := "sbt-benchexec",
    pluginCrossBuild / sbtVersion := {
      scalaBinaryVersion.value match {
        case "2.12" => "1.2.8" // set minimum sbt version
      }
    },
  )
