package systems.informal.sbt.benchexec

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

  // Benchexec requires a property file (even if empty) if we want to determine
  // what a correct and expected result is for a task.
  // See https://github.com/sosy-lab/benchexec/issues/820
  private val propertyFileName = "property-file.prp"

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

  /** The tasks to run in the suite.
    *
    * Each command in the suite will be run on each task.
    *
    * @param filePatterns
    *   files on which the options are to be run
    * @param options
    *   additional CLI options to be supplied for this task, these will be added
    *   in addition to the options in the suite [[Cmd]]s
    * @param verdict
    *   the expected verdict of the task. Wether or not the task is correct is
    *   decided based on whether on the status of the task matches the verdict.
    *   Defaults to "true".
    */
  case class Tasks(
      name: String,
      filePatterns: Seq[String],
      options: Seq[Opt] = Nil,
      verdict: String = "true")
      extends ToXml {

    // Not used currently, this is the xml for a set of tasks that does not require
    // a task-definition file.
    def toXml =
      <tasks name={name}>
        {filePatterns.map(f => <include>{f}</include>)}
        {options.map(_.toXml)}
        <propertyfile expectedverdict={verdict}>{propertyFileName}</propertyfile>
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
    sealed abstract class T[+State] {
      val state: State
      val name: String

      /** All the groups assigned to runs */
      def groups(): Seq[String]

      /** Saves the benchmark in the given `dir`, returned a Defined benchmark
        */
      def save(dir: File): T[Defined]
    }

    // Tasks that use a task-definition file. This is neceessary for any tasks
    // require supporting files.
    private class DefinedTasks(
        filename: String,
        taskDef: TaskDefinition.Format,
        tasks: Tasks)
        extends ToXml {
      def toXml =
        <tasks name={tasks.name}>
          <include>{filename}</include>
          {tasks.options.map(_.toXml)}
          <propertyfile expectedverdict={tasks.verdict}>{propertyFileName}</propertyfile>
        </tasks>

      def addSuiteName(prefix: String): DefinedTasks = {
        new DefinedTasks(s"${prefix}-${filename}", taskDef, tasks)
      }

      // We want the full task name to come from the task, so they are absolute
      def save(dir: File) =
        TaskDefinition.save(dir / filename, taskDef)
    }

    private object DefinedTasks {
      def apply(prefix: String, tasks: Tasks): DefinedTasks = {
        val requiredFiles =
          // A wildcard for the directory in which each task file lives
          tasks.filePatterns.map(f => (file(f).getParentFile() / "*").toString)

        val taskDef = TaskDefinition.Format(
          required_files = requiredFiles,
          input_files = tasks.filePatterns,
          properties = Seq(TaskDefinition.Property(propertyFileName)),
        )

        new DefinedTasks(s"${prefix}-${tasks.name}.yml", taskDef, tasks)
      }
    }

    /** Benchmark runs derived from a set of commands and tasks
      *
      *   - `group` is an optional group ID that allows results to be gathered
      *     together in reports
      */
    class Runs[+State](
        val name: String,
        val cmds: Seq[Cmd],
        tasks: Seq[DefinedTasks],
        val timelimit: String = "none",
        val group: Option[String] = None,
        val state: State = Specified())
        extends T[State]
        with ToXml {
      def toXml =
        <benchmark tool={Constants.toolName} displayName={name}
            timelimit={timelimit}>
          {cmds.map(_.toXml)}
          {tasks.map(_.toXml)}
        </benchmark>

      /** Save the XML and YAML representation of the definitions in `dir`
        *
        * The file's name is determined by the `name` of the runs
        */
      def save(dir: File): Runs[Defined] = {
        assert(dir.isDirectory)
        val groupSuffix = group.map(i => s"-group:${i}").getOrElse("")
        val file = new File(dir, s"${name}${groupSuffix}.xml")
        BenchExecXml.save(file, BenchExecXml.DocType.benchmark, this.toXml)
        IO.touch(dir / propertyFileName)
        tasks.foreach(_.save(dir))
        this.defined(Seq(file))
      }

      private def defined(files: Seq[File]): Runs[Defined] = {
        new Runs(
          name,
          cmds,
          tasks,
          timelimit,
          state = Defined(files),
          group = group,
        )
      }

      def groups(): Seq[String] = group.toSeq

      def executed(resultDir: File): Runs[Executed] = {
        new Runs(
          name,
          cmds,
          tasks,
          timelimit,
          state = Executed(resultDir),
          group = group,
        )
      }

      def addSuiteName(suiteName: String): Runs[Specified] = {
        new Runs(
          s"${suiteName}-${name}",
          cmds,
          tasks = tasks.map(_.addSuiteName(suiteName)),
          timelimit,
          state = Specified(),
          group = group,
        )
      }
    }

    object Runs {
      def apply(
          name: String,
          cmds: Seq[Cmd],
          tasks: Seq[Tasks],
          timelimit: String = "none",
          group: Option[String] = None,
        ): Runs[Specified] = {
        val definedTasks = tasks.zipWithIndex.map { case (t, n) =>
          DefinedTasks(f"${n + 1}%03d-${name}", t)
        }
        new Runs(name, cmds, definedTasks, timelimit, group = group)
      }
    }

    /** A suite of Runs, each derived from (possibly) disjoint sets of commands
      * and tasks, but for which the resulting data is grouped as one set of
      * results
      */
    class Suite[+State](
        val name: String,
        val runs: Seq[Runs[State]],
        val state: State = Specified())
        extends T[State] {

      def save(dir: File): Suite[Defined] = {
        assert(dir.isDirectory)
        val savedRuns: Seq[Runs[Defined]] =
          runs.map(_.save(dir))
        val xmlFiles: Seq[File] = savedRuns.flatMap(_.state.xmlFiles)
        new Suite(name, runs = savedRuns, state = Defined(xmlFiles))
      }

      def executed(
          resultDir: File,
          executedRuns: Seq[Runs[Executed]],
        ): Suite[Executed] = {
        new Suite(name, executedRuns, state = Executed(resultDir))
      }

      def groups(): Seq[String] = {
        runs.flatMap(_.group)
      }
    }

    object Suite {
      def apply(
          name: String,
          runs: Seq[Runs[State]],
          state: State = Specified(),
        ): Suite[Specified] = {
        val suiteRuns = runs.map(_.addSuiteName(name))
        new Suite(name, suiteRuns, state = Specified())
      }
    }

    private def benchexecCmd(
        file: File,
        outdir: File,
        log: sbt.internal.util.ManagedLogger,
      ): List[String] = {
      val runWithDebug = sys.env.get("BENCH_DEBUG").getOrElse("false").toBoolean
      val runWithContainer =
        sys.env.get("BENCH_CONTAINER").getOrElse("true").toBoolean

      log.info(s"BENCH_DEBUG is set to ${runWithDebug}")
      log.info(s"BENCH_CONTAINER is set to ${runWithContainer}")

      val debug = if (runWithDebug) {
        List("--debug")
      } else {
        List()
      }

      val container =
        if (runWithContainer) {
          List(
            "--read-only-dir",
            "/",
            "--overlay-dir",
            "/home",
          )
        } else {
          List("--no-container")
        }

      val cmd = List(
        "benchexec",
        file.name,
        "--output",
        outdir.name,
      ) ++ container ++ debug

      log.info(s"Benchexec command: ${cmd}")

      cmd
    }

    def run(
        runs: Runs[Defined],
        workdir: File,
        timestamp: String,
        // The SBT logger is not in scope outside of tasks, so we need to thread it through
        log: sbt.internal.util.ManagedLogger,
      ): Runs[Executed] = {
      // Runs only ever have a single Xml file defining them
      val defFile = runs.state.xmlFiles(0)
      val resultDir = workdir / s"${runs.name}.${timestamp}.results"
      IO.createDirectory(resultDir)
      val cmd = Process(benchexecCmd(defFile, resultDir, log), workdir)
      Exec.succeed(cmd, log)
      runs.executed(resultDir)
    }

    /** Run all `Runs` of the `suite` with results to the same directory */
    def run(
        suite: Suite[Defined],
        workdir: File,
        timestamp: String,
        // The SBT logger is not in scope outside of tasks, so we need to thread it through
        log: sbt.internal.util.ManagedLogger,
      ): Suite[Executed] = {
      val defFiles: Seq[File] = suite.state.xmlFiles
      val resultDir = workdir / s"${suite.name}.${timestamp}.results"
      IO.createDirectory(resultDir)
      defFiles.foreach { f =>
        val cmd = Process(benchexecCmd(f, resultDir, log), workdir)
        Exec.succeed(cmd, log)
      }
      val executedRuns = suite.runs.map(_.executed(resultDir))
      suite.executed(resultDir, executedRuns)
    }
  }
}
