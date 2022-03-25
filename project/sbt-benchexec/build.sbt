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

// https://github.com/tototoshi/scala-csv
libraryDependencies += "com.github.tototoshi" %% "scala-csv" % "1.3.10"

libraryDependencies ++= Seq(
  "commons-io" % "commons-io" % "2.11.0",
  "org.scala-sbt" % "sbt" % "1.6.2",
  // Needed foor  bzip2 decompression
  "org.apache.commons" % "commons-compress" % "1.21",
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
