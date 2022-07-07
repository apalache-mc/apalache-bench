import systems.informal.sbt.benchexec.BenchExecDsl.{Bench, Cmd, Opt, Tasks}

/** Utilities */
object ProjectUtils {

  /** Abstracts over the parameters that vary between the various specs */
  case class Spec(
    folder: String,
    file: String,
    length: Int = 10,
    init: String = "Init",
    inv: String = "")

  /** Abstracts over the parameters that vary between the various commands */
  case class CmdPar(
    init: String,
    inv: String,
    length: Int,
    encoding: String,
    searchInvMode: String,
    discardDisabled: String)

  /** Generates a benchmarking suite */
  def suiteGen(
    suiteName: String,
    specs: Seq[Spec],
    cmdGen: CmdPar => Cmd = defaultCheckCmd) = {
    val suiteTimeLimit = "1h" // Time units are "s", "min", and "h"

    def runsForSpec(spec: Spec) = {
      val filePath = s"${spec.folder}/${spec.file}"
      val commands = Seq(
        CmdPar(spec.init, spec.inv, spec.length, "arrays", "before", "true"),
        CmdPar(spec.init, spec.inv, spec.length, "arrays", "before", "false"),
        CmdPar(spec.init, spec.inv, spec.length, "arrays", "after", "true"),
        CmdPar(spec.init, spec.inv, spec.length, "arrays", "after", "false"),
        CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "before", "true"),
        CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "before", "false"),
        CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "after", "true"),
        CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "after", "false"),
      )

      Bench.Runs(
        s"run-${spec.folder}-${spec.file}",
        timelimit = suiteTimeLimit,
        cmds = commands.map(cmdGen),
        tasks = Seq(Tasks(s"task-${spec.file}", Seq(filePath))),
      )
    }

    Bench.Suite(
      name = suiteName,
      runs = specs.map(runsForSpec)
    )
  }

  def defaultCheckCmd(cmdPar: CmdPar): Cmd = {
    Cmd(
      s"${cmdPar.encoding}-${cmdPar.discardDisabled}-${cmdPar.searchInvMode}",
      Opt("check"),
      Opt("--init", cmdPar.init),
      Opt("--inv", cmdPar.inv),
      Opt("--length", cmdPar.length),
      Opt("--smt-encoding", cmdPar.encoding),
      Opt("--tuning-options", s"search.invariant.mode=${cmdPar.searchInvMode}"),
      Opt("--discard-disabled", cmdPar.discardDisabled),
    )
  }
}
