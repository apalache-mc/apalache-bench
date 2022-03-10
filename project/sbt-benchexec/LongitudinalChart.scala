package systems.informal.sbt.benchexec

import java.nio.file.Path
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.HashMap

import io.circe._
import io.circe.generic.auto._
import io.circe.parser._
import io.circe.syntax._

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

    def asJson(): Json =
      ReportPayload(
        metric = metric,
        data = this.toData(),
      ).asJson
  }

  def chart(report: Report): xml.Elem = {
    val script = xml.Unparsed("""
const ctx = document.getElementById('myChart').getContext('2d');
const myChart = new Chart(ctx, {
    type: 'line',
    data: {
        labels: ['Red', 'Blue', 'Yellow', 'Green', 'Purple', 'Orange'],
        datasets: [{
            label: '# of Votes',
            data: [12, 19, 3, 5, 2, 3],
            borderColor: 'rgba(255, 99, 132, 1)',
            borderWidth: 1
        }]
    },
    options: {
        scales: {
            y: {
                beginAtZero: true,
                title: {
                    display: true,
                    text:"TODO: Metric"
                }
            }
        }
    }
});
""")
    <div class="chart-section">
        <h1>TODO: Title</h1>
        <div class="chart-container">
            <canvas id="chartID" width="400" height="400"></canvas>
        </div>
        <script>
            {script}
        </script>
    </div>
  }

  /** A page that displays longitudinal results
    *
    * @param results
    *   map from version to result data
    */
  case class Page(
      experimentName: String) {

    val page =
      <html lang="en">
        <head>
            <title>Longitudinal Results For {}</title>
                <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
            </head>
        <body>
        </body>
      </html>

    def save(f: File): Unit = {
      BenchExecXml.save(f, BenchExecXml.DocType.html, page)
    }
  }
}
