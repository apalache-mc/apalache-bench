// http://github.com/sbt/sbt-site
addSbtPlugin("com.typesafe.sbt" % "sbt-site" % "1.4.1")
// https://github.com/sbt/sbt-ghpages
addSbtPlugin("com.typesafe.sbt" % "sbt-ghpages" % "0.6.3")

// Required by BenchExec plugin
libraryDependencies ++= Seq(
  "commons-io" % "commons-io" % "2.11.0"
)

// Add the locally defined BenchExec plugin
lazy val root = (project in file("."))
  .dependsOn(benchExecPlugin, apalachePlugin)
  .settings(
    name := "apalache-bench-plugins"
  )

lazy val benchExecPlugin =
  ProjectRef(file("sbt-benchexec"), "sbt_benchexec")
lazy val apalachePlugin =
  ProjectRef(file("sbt-apalache"), "sbt_apalache")
