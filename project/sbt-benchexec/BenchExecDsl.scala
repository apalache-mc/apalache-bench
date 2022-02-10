package systems.informal.benchexec

import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.FilenameUtils
import scala.language.postfixOps

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

    /** The possible states of a benchmark */
    sealed class State

    /** A benchamrk specified in the build config */
    case class Specified() extends State

    /** A benchmark for which the xml defs have been generated as `xmlFiles` */
    case class Defined(xmlFiles: Seq[File]) extends State

    /** A benchmark that has been executed with results in the `resultDir` */
    case class Executed(resultDir: File) extends State

    /** Base type of benchmark definitions
      *
      * They have a name, and can saved saved to files
      */
    sealed abstract class T[State] {
      val state: State
      val name: String

      // Saves the benchmark in the given `dir`, returned a Defined benchmark
      def save(dir: File): T[Defined]
    }

    /** Benchmark runs derived from a set of commands and tasks */
    case class Runs[State](
        name: String,
        cmds: Seq[Cmd],
        tasks: Seq[Tasks],
        timelimit: String = "none",
        state: State = Specified())
        extends T[State]
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
      def save(dir: File): Runs[Defined] = {
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
        this.copy(state = Defined(Seq(file)))
      }
    }

    /** A suite of Runs each derived from possibly disjoint sets of commands and
      * tasks, but for which the resulting data is grouped as one set of results
      */
    case class Suite[State](
        name: String,
        state: State = Specified(),
        runs: Seq[Runs[State]])
        extends T[State] {
      def save(dir: File): Suite[Defined] = {
        assert(dir.isDirectory)
        val savedRuns: Seq[Runs[Defined]] =
          runs.map(r => r.copy(name = s"${name}-${r.name}").save(dir))
        val xmlFiles: Seq[File] = savedRuns.flatMap(_.state.xmlFiles)
        this.copy(state = Defined(xmlFiles), runs = savedRuns)
        // this.copy(state = Defined(xmlFiles))
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

    def run(
        runs: Runs[Defined],
        workdir: File,
        timestamp: String,
      ): Runs[Executed] = {
      // Runs only ever have a single Xml file defining them
      val defFile = runs.state.xmlFiles(0)
      val resultDir = workdir / s"${runs.name}.${timestamp}.results"
      IO.createDirectory(resultDir)
      // TODO Log here?
      (Process(benchexecCmd(defFile, resultDir), workdir) !)
      runs.copy(state = Executed(resultDir))
    }

    /** Run all `Runs` of the `suite` with results to the same directory */
    def run(
        suite: Suite[Defined],
        workdir: File,
        timestamp: String,
      ): Suite[Executed] = {
      val defFiles: Seq[File] = suite.state.xmlFiles
      val resultDir = workdir / s"${suite.name}.${timestamp}.results"
      println(s"outfiles ${defFiles}")
      IO.createDirectory(resultDir)
      // TODO Log here?
      defFiles.foreach(f => Process(benchexecCmd(f, resultDir), workdir) !)
      val executedRuns = suite.runs.map(_.copy(state = Executed(resultDir)))
      suite.copy(state = Executed(resultDir), runs = executedRuns)
    }
  }
}
