// Required by BenchExec plugin
libraryDependencies ++= Seq(
  "commons-io" % "commons-io" % "2.11.0"
)

// Add the locally defined BenchExec plugin
lazy val root = (project in file("."))
  .dependsOn(benchExecPlugin, apalachePlugin)

lazy val benchExecPlugin = RootProject(file("sbt-benchexec"))
lazy val apalachePlugin = RootProject(file("sbt-apalache"))
