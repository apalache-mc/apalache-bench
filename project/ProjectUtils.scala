import systems.informal.sbt.benchexec.BenchExecDsl.{Bench, Cmd, Opt, Tasks}

/** Utilities */
object ProjectUtils {

  /** Abstracts over the parameters that vary between the various specs */
  case class Spec(
    folder: String,
    file: String,
    length: Int = 10,
    init: String = "Init",
    next: String = "Next",
    cInit: Option[String] = None, // cinit cannot be an empty string
    inv: Option[String] = None) // inv cannot be an empty string

  /** Abstracts over the parameters that vary between the various fine tuning commands */
  case class CmdPar(
    encoding: String,
    searchInvMode: String,
    discardDisabled: String)

  /** Generates a benchmarking suite */
  def suiteGen(
      suiteName: String,
      specs: Seq[Spec],
      cmdPars: Seq[CmdPar],
      cmdGens: Seq[(Spec, CmdPar) => Cmd] = Seq(defaultCheckCmdGen)
    ): Bench.Suite[Bench.Specified] = {

    // We generate runs for a given spec
    def runsForSpec(spec: Spec) = {
      // We generates commands based on a given command generator and the values of the "smt-encoding",
      // "tuning-options=search.invariant.mode", and "discard-disabled" flags.
      def cmdsForCmdGen(cmdGen: (Spec, CmdPar) => Cmd) = {
        cmdPars.map(cmdGen(spec,_))
      }

      val filePath = s"${spec.folder}/${spec.file}"

      Bench.Runs(
        s"run-${spec.folder}-${spec.file}",
        timelimit = "1h", // Time units are "s", "min", and "h"
        cmds = cmdGens.flatMap(cmdsForCmdGen),
        tasks = Seq(Tasks(s"task-${spec.file}", Seq(filePath))),
      )
    }

    Bench.Suite(
      name = suiteName,
      runs = specs.map(runsForSpec)
    )
  }

  def defaultCheckCmdGen(spec: Spec, cmdPar: CmdPar): Cmd = {
    val cmdOpts: Seq[Opt] = Seq(
      Opt("check"),
      Opt("--length", spec.length),
      Opt("--init", spec.init),
      Opt("--next", spec.next),
      Opt("--features", "no-rows"), // needed until the specs are updated with rows
      Opt("--smt-encoding", cmdPar.encoding),
      Opt("--tuning-options", s"search.invariant.mode=${cmdPar.searchInvMode}"),
      Opt("--discard-disabled", cmdPar.discardDisabled),
    ) ++ spec.cInit.map(Opt("--cinit", _)).toSeq ++ spec.inv.map(Opt("--inv", _)).toSeq

    Cmd(
      s"$Cmd-${cmdPar.encoding}-${cmdPar.discardDisabled}-${cmdPar.searchInvMode}",
      cmdOpts: _*
    )
  }

  val cmdParsDefault: Seq[CmdPar] = Seq(
    CmdPar("arrays", "before", "true"),
    CmdPar("funArrays", "before", "true"),
    CmdPar("oopsla19", "before", "true"),
  )

  val cmdParsFull: Seq[CmdPar] = cmdParsDefault ++ Seq(
    CmdPar("arrays", "before", "false"),
    CmdPar("arrays", "after", "true"),
    CmdPar("arrays", "after", "false"),
    CmdPar("oopsla19", "before", "false"),
    CmdPar("oopsla19", "after", "true"),
    CmdPar("oopsla19", "after", "false"),
  )
}
