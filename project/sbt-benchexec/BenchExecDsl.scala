package systems.informal.benchexec

import sbt._
import scala.xml

private object Constants {
  // TODO Replace tool with "apalache" once apalache tool info is incorporated into
  // BenchExec
  val toolName = ".apalache"
}

object BenchExecDsl {
  trait ToXml {
    def toXml: xml.Elem
  }

  /** An option to pass to a `Cmd` command */
  case class Opt(flag: String, arg: Any = "") extends ToXml {
    def toXml = arg match {
      case ""  => <option>{flag}</option>
      case arg => <option>{s"${flag}=${arg}"}</option>
    }
  }

  /** A command to run on the files of the benchmark suite */
  case class Cmd(name: String, options: Opt*) extends ToXml {
    def toXml =
      <rundefinition name={name}>
      {options.map(_.toXml)}
    </rundefinition>
  }

  /** The tasks (files) to run in the suite. Each command will be run on each
    * file matching the `filePattern`
    */
  case class Tasks(name: String, filePatterns: String*) extends ToXml {
    def toXml =
      <tasks name={name}>
      {filePatterns.map(f => <include>{f}</include>)}
    </tasks>
  }

  object Bench {

    /** Base type of benchmark definitions
      *
      * They have a name, and can saved saved to files
      */
    sealed abstract class T {
      val name: String

      def save(file: File): Seq[File]
    }

    /** Benchmark runs derived from a set of commands and tasks */
    case class Runs(
        name: String,
        cmds: Seq[Cmd],
        tasks: Seq[Tasks],
        timelimit: String = "none")
        extends T
        with ToXml {
      def toXml =
        <benchmark tool={Constants.toolName} displayName={name}>
      {cmds.map(_.toXml)}
      {tasks.map(_.toXml)}
      </benchmark>

      private def docType = xml.dtd.DocType(
        "benchmark",
        xml.dtd.PublicID(
          "+//IDN sosy-lab.org//DTD BenchExec benchmark 1.18//EN",
          "https://www.sosy-lab.org/benchexec/benchmark-1.18.dtd",
        ),
        Nil,
      )

      /** Save the XML representation of the runs definitions a file in `dir`
        *
        * The file's name is determined by the `name` of the runs
        */
      def save(dir: File): Seq[File] = {
        assert(dir.isDirectory)
        val file = new File(dir, s"${name}.xml")
        val pp = new xml.PrettyPrinter(100, 2)
        val formatted = pp.format(this.toXml)
        IO.writer(file, "", charset = IO.defaultCharset) { w =>
          // First write the encoding and doctype
          xml.XML.write(
            w,
            xml.Text(""),
            "UTF-8",
            xmlDecl = true,
            doctype = this.docType,
          )
          w.append(
            "<!-- NOTE: This file is generated. Edit the build.sbt instead. -->\n"
          )
          // Then write the pretty printed XML payload
          w.append(formatted)
        }
        Seq(file)
      }
    }

    /** A suite of Runs each derived from possibly disjoint sets of commands and
      * tasks, but for which the resulting data is grouped as one set of results
      */
    case class Suite(name: String, runs: Runs*) extends T {
      def save(dir: File): Seq[File] = {
        assert(dir.isDirectory)
        runs.map(r => r.copy(name = s"${name}-r.name")).flatMap(_.save(dir))
      }
    }
  }
}
