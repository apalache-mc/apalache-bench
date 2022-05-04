package systems.informal.sbt.benchexec

import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.{FilenameUtils, FileUtils}
import sbt.nio.file.{Glob, FileTreeView}
import java.nio.file.Path
import org.apache.commons.compress.compressors.bzip2._
import com.github.tototoshi.csv._

// JSON Encoding
import io.circe._
import io.circe.generic.auto._
import io.circe.parser._
import io.circe.syntax._

import sbt._
import Keys._
import java.io.InputStream

object BenchExec extends AutoPlugin {
  val Chart = LongitudinalChart

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

    lazy val benchmarksSiteDir =
      settingKey[File](
        "The site used to share and serve human-readible reports and charts"
      )

    lazy val benchmarksFilterExperiments =
      settingKey[Set[String]](
        "If non-empty, only experiments matching the names in set"
      )

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

    lazy val benchmarksLongitudinalVersions = taskKey[Set[String]](
      "The versions to include in the longitudinal performance reports"
    )

    lazy val benchmarksLongitudinalUpdate =
      taskKey[Seq[File]](
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

  private def timestamp() =
    new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss").format(new Date())

  lazy val benchexecRun: Def.Initialize[Task[Seq[Bench.T[Bench.Executed]]]] =
    Def.task {
      val log = streams.value.log
      val workdir = (Compile / resourceManaged).value
      val time = timestamp()
      val version = benchmarksToolVersion.value

      val includeBenchmark = (b: Bench.T[Bench.Defined]) => {
        val filterSet = (ThisBuild / benchmarksFilterExperiments).value
        (filterSet.isEmpty) || filterSet(b.name)
      }

      benchmarksDef.value.filter(includeBenchmark).map { bench =>
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
    val resultFiles = results.sorted.zipWithIndex.map { case (f, i) =>
      <result id={i.toString()} filename={f}/>
    }
    <table>
      <union>
        {resultFiles}
      </union>
    </table>
  }

  private def inputBz2(fileName: String): InputStream = {
    new BZip2CompressorInputStream(
      new java.io.BufferedInputStream(new java.io.FileInputStream(fileName))
    )
  }

  private val incorrectColumn = (column: xml.NodeSeq) =>
    (column \ "@title").text == "category" && (column \ "@value").text != "correct"

  // Query the report XML to check for failed runs
  // returns a option pair of the options provided and the task that was incorrect
  private def findIncorrectRunsFromResult(
      resultFile: String
    ): Option[(String, Seq[String])] = {
    val input = inputBz2(resultFile)
    val result = xml.XML.load(input)
    val incorrectRuns = (result \ "run")
      .filter(run => (run \ "column").exists(incorrectColumn))
      .map(n => (n \ "@name").text)
    if (incorrectRuns.nonEmpty) {
      val options = (result \ "@options").text
      Some((options, incorrectRuns))
    } else {
      None
    }
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

        val runFiles: Seq[Path] =
          globPaths(executed.state.resultDir.toGlob / "*.files")

        val stamp = s"${timestamp()}.${executed.name}"

        // Create the table-generator XML config
        // We need to generate a custom table-generator config so we can
        // combine all results from a given suite run into the same columns.
        // See https://github.com/sosy-lab/benchexec/blob/main/doc/table-generator.md#complex-tables-with-custom-columns-or-combination-of-results
        val tableGenConfig =
          executed.state.resultDir / s"result.${stamp}.table-generator.xml"

        BenchExecXml.save(
          tableGenConfig,
          BenchExecXml.DocType.tableGenerator,
          tableGeneratorConfigXml(results),
        )

        val reportDir = benchmarkReportsDir.value / toolVersion / executed.name

        val incorrectResults = results.flatMap(findIncorrectRunsFromResult)
        if (incorrectResults.nonEmpty) {
          log.error(s"Some results were incorrect: ${incorrectResults}")
          val errFile = executed.state.resultDir / s"ERRORS.${stamp}.json"
          log.error(s"Error data saved to ${errFile}")
          val errData = Map(stamp -> incorrectResults.toMap)
          IO.append(errFile, errData.asJson.toString)
        }

        IO.createDirectory(reportDir)
        log.info("Saving run outputs...")
        runFiles.foreach { f =>
          log.info(s"Copying run output for ${executed.name} to ${f}")
          FileUtils.copyDirectory(f.toFile, reportDir / f.getFileName.toString)
        }

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
        Exec.succeed(cmd, log)

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

  private def longitudinalExperimentLinks(siteDir: Path): xml.Elem = {
    val longReportsDir = siteDir / "longitudinal"
    val items = globPaths(longReportsDir.toGlob / ** / "*.html").map { report =>
      val name = report.getFileName.toString
      val link = s"longitudinal/${name}"
      <li><a href={link}>{name}</a></li>
    }
    <ul>
      {items}
    </ul>
  }

  lazy val benchmarksIndexUpdateImpl: Def.Initialize[Task[Unit]] =
    Def.task {
      val log = streams.value.log
      benchmarksIndexFile.value.map { file =>
        val reportsDir = benchmarkReportsDir.value.toPath
        val longitudinalLinks =
          longitudinalExperimentLinks(benchmarksSiteDir.value.toPath)
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
              <h2>Longitudinal Comparison of Experiments</h2>
                {longitudinalLinks}
              <h2>Individual Experiments</h2>
              <table id="results-table" class="table table-striped sampleTable">
                <thead>{header}</thead>
                <tbody>{rows}</tbody>
              </table>
              <script>
                {script}
              </script>
            </body>
        </html>

        log.info(s"Saving updated site index to $file")
        BenchExecXml.save(file, BenchExecXml.DocType.html, page)
      }
    }

  // Use tab-separated CSV, as per benchexec
  implicit object CSVDelimFormat extends DefaultCSVFormat {
    override val delimiter = '\t'
  }

  private def parseResults(results: Map[String, Path]): List[Chart.Report] = {

    val cputimeReport = Chart.Report("cputime")
    val walltimeReport = Chart.Report("walltime")
    val memoryReport = Chart.Report("memory")

    for ((version, resultPath) <- results) {
      CSVReader
        .open(resultPath.toFile)
        .all()
        .drop(3)
        .foreach {
          case task :: id :: status :: cputime :: walltime :: memory :: Nil => {
            cputimeReport.addResult(version, s"${task}:${id}", cputime.toDouble)
            walltimeReport.addResult(
              version,
              s"${task}:${id}",
              walltime.toDouble,
            )
            memoryReport.addResult(version, s"${task}:${id}", memory.toDouble)
          }
          case row =>
            throw new RuntimeException(s"Invalid report data row: ${row}")
        }
    }

    List(cputimeReport, walltimeReport, memoryReport)
  }

  lazy val benchmarksLongitudinalDataImpl: Def.Initialize[Task[Seq[File]]] =
    Def.task {
      val log = streams.value.log
      val reportsDir = benchmarkReportsDir.value
      val longReportsDir = benchmarksSiteDir.value / "longitudinal"
      val versionsToInclude = benchmarksLongitudinalVersions.value

      def shouldIncludeReport(p: Path): Boolean =
        versionsToInclude.contains(p.getFileName().toString)

      // TODO Memoize on changes of report dir
      // We always want to include the latest generated report
      val latestReport +: olderReports =
        globPaths(reportsDir.toGlob / *)
          .sortBy(_.toFile().lastModified())
          .reverse

      val otherReportsToInclude = olderReports.filter(shouldIncludeReport)

      // A map of all the latest reports organized by version and strategy:
      // v1 -> (strategy0 -> latestResult, strategy1 -> latestResult)
      // v2 -> (strategy0 -> latestResult, strategy1 -> latestResult)
      val emptyMap: Map[String, Map[String, Path]] = Map()
      val reportsToInclude = latestReport +: otherReportsToInclude

      val reportsByExperiment = reportsToInclude.foldLeft(emptyMap) {
        (m, versionDir) =>
          val v = versionDir.getFileName().toString()
          val versionExperiments = globPaths(versionDir.toGlob / *)
          val results = {
            versionExperiments.map { strategy =>
              val s = strategy.getFileName().toString()
              val latestResult =
                globPaths(strategy.toGlob / "*.csv")
                  .maxBy(_.toFile.lastModified)
              val strategyResults =
                m.getOrElse(s, Map()) + (v -> latestResult)
              s -> strategyResults
            }
          }
          // Add results
          m ++ results
      }

      reportsByExperiment.map { case (experiment, results) =>
        val pageFile = longReportsDir / s"${experiment}.html"
        log.info(s"Saving longitudinal report for ${experiment} to ${pageFile}")
        Chart.Page(experiment, parseResults(results)).save(pageFile)
        pageFile
      }.toSeq
    }

  override lazy val globalSettings = Seq(
    benchmarksIndexFile := None,
    benchmarksLongitudinalVersions := Set(),
    benchmarksSiteDir := (ThisBuild / baseDirectory).value / "src" / "site",
    benchmarkReportsDir := benchmarksSiteDir.value / "reports",
    benchmarksFilterExperiments := Set(),
  )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    benchmarks := Seq(),
    benchmarksDef := benchexecSetup.value,
    benchmarksRun := benchexecRun.value,
    benchmarksReport := benchexecReport.value,
    benchmarksIndexUpdate := benchmarksIndexUpdateImpl.value,
    benchmarksLongitudinalUpdate := benchmarksLongitudinalDataImpl.value,
  )
}
