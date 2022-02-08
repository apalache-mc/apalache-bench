import java.text.SimpleDateFormat
import Benchmark._
import scala.sys.process.Process
import java.util.Date

ThisBuild / version := "0.0.1"
ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "systems.informal"

// TODO Move into aux file
lazy val benchmarks =
  settingKey[Seq[Benchmark]]("Benchmark suite definitions")

ThisBuild / benchmarks := Seq()

def isTargetDir(f: File): Boolean = {
  f.toPath.getFileName.toString == "target"
}

// Enable taking a specific benchmark
lazy val benchmarkDefs = taskKey[Seq[File]]("A benchmark definition")
lazy val benchmarkResults = taskKey[Seq[File]]("Results of a benchmarking run")

lazy val benchexecSetup: Def.Initialize[Task[Seq[File]]] = Def.task {
  val log = streams.value.log
  val resourceDir = (Compile / resourceManaged).value
  val projectDir = baseDirectory.value

  log.info(s"Copying resource files from ${projectDir} to ${resourceDir}")
  IO.listFiles(projectDir).foreach { file =>
    val fname = file.toPath.getFileName.toString
    val destination = resourceDir / fname
    if (file.isDirectory() && !(fname == "target")) {
      IO.copyDirectory(file, destination)
    } else if (file.isFile()) {
      IO.copyFile(file, destination)
    }
  }

  benchmarks.value.map { b =>
    log.info(s"Generating benchmark definition for ${b.name} in ${resourceDir}")
    val file = resourceDir / s"${b.name}.xml"
    b.save(file)
    file
  }
}

// - outdir: the directory into which results are to be written
def benchexecCmd(file: File, outdir: File): List[String] =
  List(
    "benchexec",
    file.name,
    "--output",
    outdir.name,
    "--read-only-dir",
    "/",
    "--overlay-dir",
    "/home",
  )

lazy val benchexecRun: Def.Initialize[Task[Seq[File]]] = Def.task {
  val log = streams.value.log
  val timestamp =
    new SimpleDateFormat("yyyy-MM-dd'T'HH-mm-ss").format(new Date())
  val workdir = (Compile / resourceManaged).value
  benchmarkDefs.value.map { defFile =>
    // TODO Use Apache Commons IO for extension splitting?
    val name = defFile.toPath().getFileName().toString().split("\\.")(0)
    val outdir = workdir / s"${name}.${timestamp}.results"
    IO.createDirectory(outdir)
    log.info(
      s"Running benchmark ${defFile.toPath().getFileName()} with results in ${outdir}"
    )
    Process(benchexecCmd(defFile, outdir), workdir) ! log
    outdir
  }
}

// TODO enable running a single benchmark definition
// - Rework so benchmark task runs one benchmark definition?

lazy val performance = (project in file("performance"))
  .settings(
    benchmarks += {
      val length = Seq(2, 10, 15, 20, 30)
      val runs = length.map(n =>
        Run(
          s"length ${n}",
          Opt("check"),
          Opt("--inv", "Inv"),
          Opt("--length", n),
        )
      )
      Benchmark(
        "testing-benchmark",
        runs,
        tasks = Seq(
          Tasks("prisoners", "Prisoners/APAPrisoners.tla"),
          Tasks("counter", "Counter.tla"),
        ),
      )
    },
    benchmarkDefs := benchexecSetup.value,
    benchmarkResults := benchexecRun.value,
    Compile / compile := ((Compile / compile)
      .dependsOn(benchmarkDefs))
      .value,
  )
