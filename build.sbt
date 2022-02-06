import Benchmark._

ThisBuild / version := "0.0.1"
ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "systems.informal"

// TODO Move into aux file
lazy val benchmarks =
  settingKey[Seq[Benchmark]]("Benchmark suite definitions")
benchmarks := Seq()

benchmarks += {
  val opts = Seq(Opt("check"), Opt("--inv", "Inv"))
  Benchmark(
    "testing benchmark",
    runs = Seq(
      Run("length 2", opts :+ Opt("--length", 2)),
      Run("length 10", opts :+ Opt("--length", 10)),
    ),
    tasks = Seq(Tasks("task 1", "*.tla")),
  )
}

lazy val benchmarkDefsGenerate =
  taskKey[Seq[File]]("Generate the BenchExec definition files")
benchmarkDefsGenerate := {
  benchmarks.value.map(b => {
    println(s"Working on {b.name}")
    val file = (Compile / resourceManaged).value / b.name / "benchmarks.xml"
    b.save(file)
  })
}

Compile / resourceGenerators += benchmarkDefsGenerate
