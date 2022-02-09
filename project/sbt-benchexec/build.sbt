ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "systems.informal"
// TODO
// ThisBuild / homepage := Some(url("https://github.com/sbt/sbt-hello"))

libraryDependencies += "commons-io" % "commons-io" % "2.11.0"

lazy val root = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
    name := "sbt-benchexec",
    pluginCrossBuild / sbtVersion := {
      scalaBinaryVersion.value match {
        case "2.12" => "1.2.8" // set minimum sbt version
      }
    },
  )
