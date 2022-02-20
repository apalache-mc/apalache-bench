package systems.informal.benchexec

import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.FilenameUtils
import sbt.nio.file.{Glob, FileTreeView}
import java.nio.file.Path

import sbt._
import Keys._

object BenchExec extends AutoPlugin {
  object autoImport {
    val BenchExecDsl = systems.informal.benchexec.BenchExecDsl

    import BenchExecDsl._
    lazy val benchmarks =
      settingKey[Seq[Bench.T[Bench.Specified]]](
        "Benchmark suite definitions"
      )

    // TODO Enable running a specific benchmark
    lazy val benchmarksDef =
      taskKey[Seq[Bench.T[Bench.Defined]]]("A benchmark definition")

    lazy val benchmarksRun =
      taskKey[Seq[Bench.T[Bench.Executed]]]("Results of a benchmarking run")

    lazy val benchmarksReport =
      taskKey[Seq[File]]("Reports from a benchmarking run")

    lazy val bencharmkReportsDir =
      settingKey[File]("The location to which generated reports are written")

    lazy val benchmarksToolVersion =
      taskKey[String]("The version of the tool being benchmarked")
  }

  import autoImport._
  import BenchExecDsl._

  lazy val benchexecSetup: Def.Initialize[Task[Seq[Bench.T[Bench.Defined]]]] =
    Def.task {
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

  private def timestamp() =
    new SimpleDateFormat("yyyy-MM-dd'T'HH-mm-ss").format(new Date())

  lazy val benchexecRun: Def.Initialize[Task[Seq[Bench.T[Bench.Executed]]]] =
    Def.task {
      val log = streams.value.log
      val workdir = (Compile / resourceManaged).value
      val time = timestamp()
      val version = benchmarksToolVersion.value
      benchmarksDef.value.map { bench =>
        log.info(
          s"Running benchmark ${bench.name} with tool version ${version} and results to ${workdir}"
        )
        bench match {
          case runs: Bench.Runs[Bench.Defined] =>
            Bench.run(runs, workdir, time, log)

          case suite: Bench.Suite[Bench.Defined] =>
            Bench.run(suite, workdir, time, log)
        }
      }
    }

  private def globPaths(glob: Glob): Seq[Path] =
    FileTreeView.default.list(glob).map(_._1)

  lazy val benchexecReport: Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val log = streams.value.log
      val workdir = (Compile / resourceManaged).value
      val toolVersion = benchmarksToolVersion.value
      benchmarksRun.value.map { executed =>
        val results: Seq[String] =
          globPaths(executed.state.resultDir.toGlob / "*.xml.bz2")
            .map(_.toString)

        val reportDir = bencharmkReportsDir.value / toolVersion / executed.name
        IO.createDirectory(reportDir)

        log.info(s"Generating report to ${reportDir}")
        // Generate the table using the benchexec table-generator CLI tool
        val cmd =
          "table-generator" +: "--outputpath" +: reportDir.toString +: results
        log.info(cmd.toString)
        Process(cmd) ! log

        reportDir
      }
    }

  override lazy val globalSettings = Seq(
    bencharmkReportsDir := (ThisBuild / baseDirectory).value / "src" / "site" / "reports"
  )

  // override lazy val buildSettings = Seq(
  // )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    benchmarks := Seq(),
    benchmarksDef := benchexecSetup.value,
    benchmarksRun := benchexecRun.value,
    benchmarksReport := benchexecReport.value,
    // Compile / compile := ((Compile / compile)
    //   .dependsOn(benchmarksDef))
    //   .value,
  )
}
