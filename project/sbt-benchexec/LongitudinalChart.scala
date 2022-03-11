package systems.informal.sbt.benchexec

import java.nio.file.Path
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.HashMap

import io.circe._
import io.circe.generic.auto._
import io.circe.parser._
import io.circe.syntax._
import io.circe.generic.semiauto._

import sbt._

object LongitudinalChart {

  // TODO Support NaN for missing data

  // Representation of a Chart.js dataset
  // will be serialized to JSON for use on the page
  case class Dataset(
      label: String,
      data: List[Double],
      borderColor: String,
      tension: Double = 0.1)

  // Representation of Chart.js chart data
  case class Data(
      labels: List[String],
      datasets: List[Dataset])

  // The JSON data object representing a report to inject
  // into the HTML page for each chart
  case class ReportPayload(
      metric: String,
      data: Data)

  case class Report(metric: String) {

    // All taskIds involved in the report, accumulated in the order they are added
    private val taskIds: LinkedHashSet[String] = LinkedHashSet()

    // Map from taskId -> value
    private type TaskResults = Map[String, Double]

    // Map of version -> result
    private val results = HashMap[String, TaskResults]().withDefaultValue(Map())

    private def uniqueHexColorForString(s: String): String =
      sbt.io.Hash.toHex(sbt.io.Hash(s)).take(6)

    private def toData(): Data = {
      // Labels for the categories on the X axis
      val labels = taskIds.toList

      // Each data set is a line on the chart
      val datasets = results.map { case (version, results) =>
        // Arrange the data in the same order as it appears in the X aixs labels
        // Default to NaN if any result set is missing data for a task
        val data = taskIds
          .map(results.getOrElse(_, Double.NaN))
          .toList

        Dataset(
          label = version,
          data = data,
          borderColor = "#" + uniqueHexColorForString(version),
        )
      }.toList

      Data(
        labels = labels,
        datasets = datasets,
      )
    }

    def addResult(version: String, taskId: String, value: Double): Unit = {
      taskIds.add(taskId)
      results(version) += (taskId -> value)
    }

    def toJson(): Json =
      ReportPayload(
        metric = metric,
        data = this.toData(),
      ).asJson
  }

  def chart(report: Report): xml.Elem = {
    val canvasId = s"${report.metric}-canvas"
    val divId = s"${report.metric}-div"
    <div class="chart-section">
        <h2 class="metric-header">{report.metric}</h2>
        <div id={divId} class="chart-container">
            <canvas id={canvasId}></canvas>
        </div>
    </div>
  }

  implicit val reportEncoder: Encoder[Report] =
    new Encoder[Report] {
      final def apply(r: Report): Json = r.toJson()
    }

  /** A page that displays longitudinal results
    *
    * @param results
    *   map from version to result data
    */
  case class Page(
      experimentName: String,
      reports: List[Report]) {

    val data = xml.Unparsed(reports.asJson.toString)

    val script = xml.Unparsed("""
const reportData = JSON.parse(document.getElementById("report-data").innerHTML)
for (const data of reportData) {
    const ctx = document.getElementById(data.metric + '-canvas').getContext('2d');
    new Chart(ctx, {
            type: 'line',
            data: data.data,
            options: {
                scales: {
                    y: {
                        beginAtZero: true,
                        title: {
                            display: true,
                            text: data.metric
                        }
                    }
                }
            }
        }
    )
};
""")

    val style = xml.Unparsed("""
body {
  max-width: 80%;
  padding: 10px;
  margin: auto;
}

.metric-header {
  text-align: center;
}
""")

    val content =
      <html lang="en">
        <head>
            <meta content="text/html;charset=utf-8" http-equiv="Content-Type"/>
            <meta content="utf-8" http-equiv="encoding"/>
            <title>Longitudinal Results For {experimentName}</title>
                <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
            </head>
        <body>
            <style>
                {style}
            </style>
            <script type="application/json" id="report-data">
                {data}
            </script>
            <h1>Longitudinal Results For {experimentName}</h1>
            {reports.map(chart)}
            <script>
                {script}
            </script>
        </body>
      </html>

    def save(f: File): Unit = {
      BenchExecXml.save(f, BenchExecXml.DocType.html, content)
    }
  }
}
