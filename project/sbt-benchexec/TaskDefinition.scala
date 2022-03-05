package systems.informal.sbt.benchexec

import io.circe._
import io.circe.generic.auto._
import io.circe.parser._
import io.circe.syntax._

import sbt._
/*

{
  "format_version": "2.0",
  "input_files": ["foo/bar.tla", "fix/bix.tla"],
  "required_files": ["foo/baraux.tla", "fix/bixaux.tla"]
}

 * TODO
properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true
  - property_file: ../properties/valid-memsafety.prp
    expected_verdict: false
    subproperty: valid-memtrack

 * * */

object TaskDefinition {

  // TODO In case we should take the files as Files
  // implicit val encodeFIle: Encoder[File] = Encoder.instance { f: File =>
  //   f.toString.asJson
  // }

  case class Format(
      required_files: Seq[String],
      input_files: Seq[String],
      format_version: String = "2.0")

  def save(f: File, content: Format): Unit = {
    IO.write(f, content.asJson.toString)
  }
}
