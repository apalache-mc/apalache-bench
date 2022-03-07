package systems.informal.sbt.benchexec

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
    val BenchExecDsl = systems.informal.sbt.benchexec.BenchExecDsl

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

    lazy val benchmarkReportsDir =
      settingKey[File]("The location to which generated reports are written")

    lazy val benchmarksToolVersion =
      taskKey[String]("The version of the tool being benchmarked")

    lazy val benchmarksIndexFile =
      settingKey[Option[File]](
        "Location for the index of all the reports that have been generated as an HTML page"
      )

    lazy val benchmarksIndexUpdate =
      taskKey[Unit](
        "Update the index of reports to the `benchmarksIndex` file, if it has been set"
      )

    lazy val benchmarksLongitudinalData =
      taskKey[Option[File]](
        "Update the data combining runs from different tool versions"
      )
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

  private def tableGeneratorConfigXml(results: Seq[String]): xml.Elem = {
    val resultFiles = results.zipWithIndex.map { case (f, i) =>
      <result id={i.toString()} filename={f}/>
    }
    <table><union>{resultFiles}</union></table>
  }

  lazy val benchexecReport: Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val log = streams.value.log
      val workdir = (Compile / resourceManaged).value
      val toolVersion = benchmarksToolVersion.value
      benchmarksRun.value.map { executed =>
        val results: Seq[String] =
          globPaths(executed.state.resultDir.toGlob / "*.xml.bz2")
            .map(_.toString)

        // Create the table-generator XML config
        // We need to generate a custom table-generator config so we can
        // combine all results from a given suite run into the same columns.
        // See https://github.com/sosy-lab/benchexec/blob/main/doc/table-generator.md#complex-tables-with-custom-columns-or-combination-of-results
        val tableGenConfig =
          executed.state.resultDir / s"result.${timestamp()}.${executed.name}.table-generator.xml"
        BenchExecXml.save(
          tableGenConfig,
          BenchExecXml.DocType.trableGenerator,
          tableGeneratorConfigXml(results),
        )

        val reportDir = benchmarkReportsDir.value / toolVersion / executed.name
        IO.createDirectory(reportDir)

        log.info(s"Generating report to ${reportDir}")
        // Generate the table using the benchexec table-generator CLI tool
        // See https://github.com/sosy-lab/benchexec/blob/main/doc/table-generator.md
        val cmd =
          Seq(
            "table-generator",
            "-x",
            tableGenConfig.toString,
            "--outputpath",
            reportDir.toString,
          )
        log.info("Generating results tables")
        log.info(cmd.mkString(" "))
        Process(cmd) ! log

        reportDir
      }
    }

  private val columnsOfPath: Path => Seq[String] = p => {
    val lastPathIdx = p.getNameCount - 1
    0.to(lastPathIdx).map {
      case `lastPathIdx` =>
        // results.2022-02-20_13-22-43.table.html => 2022-02-20_13-22-43
        p.getName(lastPathIdx).toString().split("\\.")(1)
      case i => p.getName(i).toString()
    }
  }

  private val rowOfData: ((Seq[String], String)) => Seq[xml.Elem] = {
    case (columns, url) => {
      val timestamp = <td><a href={s"${url}"}>{columns.last}</a></td>
      columns.dropRight(1).map((x: String) => <td>{x}</td>) :+ timestamp
    }
  }

  lazy val benchmarksIndexUpdateImpl: Def.Initialize[Task[Unit]] =
    Def.task {
      benchmarksIndexFile.value.map { file =>
        val reportsDir = benchmarkReportsDir.value.toPath
        val resultsData =
          globPaths(reportsDir.toGlob / ** / "*.html")
            .map { path =>
              val relativePath = reportsDir.relativize(path)
              val columns = columnsOfPath(relativePath)
              val url = (reportsDir.getFileName.resolve(relativePath)).toString
              (columns, url)
            }
        val header = <tr><th>Version</th><th>Strategy</th><th>Results</th></tr>
        val rows =
          resultsData.map(
            ((x: Seq[xml.Elem]) => <tr>{x}</tr>).compose(rowOfData)
          )
        val style = xml.Unparsed("""
body {
  margin: auto;
  width: 75%;
  padding: 5;
}

h1 {
  text-align: center;
}
""")
        val script = xml.Unparsed("""
                $(document).ready(function() {
                        $("#results-table").fancyTable({
                            sortColumn:0,
                            pagination: true,
                            perPage:10,
                            globalSearch:true
                        });
                });
""")
        val page =
          // See https://frontbackend.com/jquery/a-jquery-plugin-for-making-html-tables-searchable-and-sortable
          // NOTE: Curly braces in the inline js are doubled up to make them litterals
          <html lang="en">
            <head>
              <title>Apalache Benchmark Reports</title>
              <script src="https://code.jquery.com/jquery-3.3.1.min.js"></script>
              <link href="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/css/bootstrap.min.css" rel="stylesheet"/>
              <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/js/bootstrap.min.js"></script>
              <script src="https://cdn.jsdelivr.net/npm/jquery.fancytable/dist/fancyTable.min.js"></script>
              <style>{style}</style>
            </head>
            <body>
              <h1>Apalache Benchmark Reports</h1>
              <table id="results-table" class="table table-striped sampleTable">
                <thead>{header}</thead>
                <tbody>{rows}</tbody>
              </table>
              <script>
                {script}
              </script>
            </body>
        </html>

        BenchExecXml.save(file, BenchExecXml.DocType.html, page)
      }
    }

  lazy val benchmarksLongitudinalDataImpl: Def.Initialize[Task[Option[File]]] =
    Def.task {
      val reportsDir = benchmarkReportsDir.value
      val longReportsDir = reportsDir / "longitudinal"

      // A map of all the latest reports organized by version and strategy:
      // v1 -> (strategy0 -> latestResult, strategy1 -> latestResult)
      // v2 -> (strategy0 -> latestResult, strategy1 -> latestResult)
      // TODO Memoize on changes of report dir
      val versionReports =
        globPaths(reportsDir.toGlob / *)
          .foldLeft(Map[String, List[(String, Path)]]()) { (m, versionDir) =>
            val v = versionDir.getFileName().toString()
            m ++ Map(
              globPaths(versionDir.toGlob / *).map { strategy =>
                val s = strategy.getFileName().toString()
                val latestResult = globPaths(strategy.toGlob / "*.csv")
                  .maxBy(_.toFile.lastModified)
                s -> (v -> latestResult :: m.getOrElse(s, List()))
              }: _*
            )
          }

      println(versionReports)
      // TODO
      None
    }

  override lazy val globalSettings = Seq(
    benchmarksIndexFile := None,
    benchmarkReportsDir := (ThisBuild / baseDirectory).value / "src" / "site" / "reports",
  )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    benchmarks := Seq(),
    benchmarksDef := benchexecSetup.value,
    benchmarksRun := benchexecRun.value,
    benchmarksReport := benchexecReport.value,
    benchmarksIndexUpdate := benchmarksIndexUpdateImpl.value,
    benchmarksLongitudinalData := benchmarksLongitudinalDataImpl.value,
    // Compile / compile := ((Compile / compile)
    //   .dependsOn(benchmarksDef))
    //   .value,
  )
}
