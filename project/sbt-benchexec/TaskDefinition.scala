package systems.informal.sbt.benchexec

import io.circe._
import io.circe.generic.auto._
import io.circe.parser._
import io.circe.syntax._

import sbt._

/* TaskDefinition.Format generates JSON that satisfies BenchExec's
 * task-definition YAML formt
 * It looks like this
 *
 *  {
 *  "format_version": "2.0",
 *  "input_files": ["foo/bar.tla", "fix/bix.tla"],
 *  "required_files": ["foo/baraux.tla", "fix/bixaux.tla"]
 *  }
 *
 * TODO add support for properties
 *  properties:
 *    - property_file: ../properties/unreach-call.prp
 *      expected_verdict: true
 *    - property_file: ../properties/valid-memsafety.prp
 *      expected_verdict: false
 *      subproperty: valid-memtrack
 */

// See https://gitlab.com/sosy-lab/benchmarking/task-definition-format
object TaskDefinition {
  case class Property(
      property_file: String,
      expected_verdict: Boolean = true)

  case class Format(
      required_files: Seq[String],
      input_files: Seq[String],
      properties: Seq[Property],
      format_version: String = "2.0")

  def save(f: File, content: Format): Unit = {
    IO.write(f, content.asJson.toString)
  }
}
