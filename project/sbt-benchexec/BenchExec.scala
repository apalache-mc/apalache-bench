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

    import BenchExecDsl._
    lazy val benchmarks =
      settingKey[Seq[Bench.T[Bench.Specified]]](
        "Benchmark suite definitions"
      )

    // TODO Enable running a specific benchmark
    lazy val benchmarkDefs =
      taskKey[Seq[Bench.T[Bench.Defined]]]("A benchmark definition")

    lazy val benchmarkResults =
      taskKey[Seq[Bench.T[Bench.Executed]]]("Results of a benchmarking run")

    lazy val benchmarkReports =
      taskKey[Seq[File]]("Reports from a benchmarking run")
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

  lazy val benchexecRun: Def.Initialize[Task[Seq[Bench.T[Bench.Executed]]]] =
    Def.task {
      val log = streams.value.log
      val timestamp =
        new SimpleDateFormat("yyyy-MM-dd'T'HH-mm-ss").format(new Date())
      val workdir = (Compile / resourceManaged).value
      benchmarkDefs.value.map { bench =>
        log.info(
          s"Running benchmark ${bench.name} with results to ${workdir}"
        )
        bench match {
          case runs: Bench.Runs[Bench.Defined] =>
            Bench.run(runs, workdir, timestamp)

          case suite: Bench.Suite[Bench.Defined] =>
            Bench.run(suite, workdir, timestamp)
        }
      }
    }

  lazy val benchexecReport: Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val log = streams.value.log
      val workdir = (Compile / resourceManaged).value
      benchmarkResults.value.map { executed =>
        // TODO Clean up file searches when I figure out how to use SBT's Glob:
        // val reports = Glob(executed.state.resultDir.toPath / "*.xml.bz2")
        val reports: List[String] = IO
          .listFiles(executed.state.resultDir)
          .toList
          .map(_.toString)
          .filter(_.matches(""".*\.xml\.bz2"""))
        Process("table-generator" :: reports) ! log
        // Return the HTML report location
        IO
          .listFiles(executed.state.resultDir)
          .toList
          // FIXME: err handling forindexing err (tho there shoud only ever be 1 html file)
          .filter(_.toString.matches(""".*\.html"""))(0)

      }
    }

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    benchmarks := Seq(),
    benchmarkDefs := benchexecSetup.value,
    benchmarkResults := benchexecRun.value,
    benchmarkReports := benchexecReport.value,
    Compile / compile := ((Compile / compile)
      .dependsOn(benchmarkDefs))
      .value,
  )
}
