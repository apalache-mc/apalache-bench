import BenchExecDsl._
import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_examples(examplesSpecs)
)

lazy val examplesSpecs = Seq(
  Spec("2PCwithBTM", "MC4_FALSE_FALSE.tla", 10, inv = "Consistency"),
  Spec("2PCwithBTM", "MC4_TRUE_TRUE.tla", 10, inv = "Consistency"),
  Spec("2PCwithBTM", "MC10_FALSE_FALSE.tla", 10, inv = "Consistency"),
  Spec("2PCwithBTM", "MC10_TRUE_TRUE.tla", 10, inv = "Consistency"),
  Spec("2PCwithBTM", "MC20_FALSE_FALSE.tla", 10, inv = "Consistency"),
  Spec("2PCwithBTM", "MC20_TRUE_TRUE.tla", 10, inv = "Consistency"),
  Spec("aba_asyn_byz", "MC4.tla", 10),
  Spec("aba_asyn_byz", "MC10.tla", 10),
  Spec("aba_asyn_byz", "MC20.tla", 10),
  Spec("bakery", "MC3.tla", 10, inv = "MutualExclusion"),
  Spec("bakery", "MC3.tla", 0, inv = "Inv"),
  Spec("bakery", "MC3.tla", 1, init = "Inv", inv = "Inv"),
  Spec("changRoberts", "MC4.tla", 10, inv = "Correctness"),
  Spec("changRoberts", "MC10.tla", 10, inv = "Correctness"),
  Spec("changRoberts", "MC20.tla", 10, inv = "Correctness"),
  Spec("paxos", "MC3.tla", 13, inv = "V!OneValuePerBallot"),
  Spec("readersWriters", "MC4.tla", 10, inv = "Safety"),
  Spec("readersWriters", "MC10.tla", 10, inv = "Safety"),
  Spec("readersWriters", "MC20.tla", 10, inv = "Safety")
)

def suiteForEncoding_examples(specs: Seq[Spec]) = {
  val suiteTimeLimit = "1h"

  def checkCmd(cmdPar: CmdPar) = {
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
      cmds = commands.map(checkCmd),
      tasks = Seq(Tasks(s"task-${spec.file}", Seq(filePath))),
    )
  }

  Bench.Suite(
    name = s"005examples-apalache",
    runs = specs.map(runsForSpec),
  )
}
