ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "systems.informal"

libraryDependencies ++= Seq(
  "org.scala-sbt" % "sbt" % "1.6.2"
)

lazy val sbt_apalache = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
    name := "sbt-apalache",
    pluginCrossBuild / sbtVersion := {
      scalaBinaryVersion.value match {
        case "2.12" => "1.2.8" // set minimum sbt version
      }
    },
  )
