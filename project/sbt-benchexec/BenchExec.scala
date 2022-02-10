package systems.informal.benchexec

import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.FilenameUtils

import sbt._
import Keys._

object BenchExec extends AutoPlugin {
  override def trigger = allRequirements

  object autoImport {
    val BenchExecDsl = systems.informal.benchexec.BenchExecDsl

    lazy val benchmarks =
      settingKey[Seq[BenchExecDsl.Bench.T]]("Benchmark suite definitions")

    // Enable taking a specific benchmark
    lazy val benchmarkDefs = taskKey[Seq[File]]("A benchmark definition")
    lazy val benchmarkResults =
      taskKey[Seq[File]]("Results of a benchmarking run")
  }

  import autoImport._
  import BenchExecDsl._

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

    benchmarks.value.flatMap { b =>
      log.info(
        s"Generating benchmark definition for ${b.name} in ${resourceDir}"
      )
      b.save(resourceDir)
    }
  }

  private def benchexecCmd(file: File, outdir: File): List[String] =
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
      val name =
        FilenameUtils.removeExtension(defFile.toPath().getFileName().toString())
      val outdir = workdir / s"${name}.${timestamp}.results"
      IO.createDirectory(outdir)
      log.info(
        s"Running benchmark ${defFile.toPath().getFileName()} with results in ${outdir}"
      )
      Process(benchexecCmd(defFile, outdir), workdir) ! log
      outdir
    }
  }

  // override lazy val globalSettings: Seq[Setting[_]] = Seq(
  //   helloGreeting := "hi"
  // )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    benchmarks := Seq(),
    benchmarkDefs := benchexecSetup.value,
    benchmarkResults := benchexecRun.value,
    Compile / compile := ((Compile / compile)
      .dependsOn(benchmarkDefs))
      .value,
  )
}
