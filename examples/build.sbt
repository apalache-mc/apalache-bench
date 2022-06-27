import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_examples(examplesSpecs)
)

lazy val examplesSpecs = Seq(
  ("2PCwithBTM", "MC4_FALSE_FALSE.tla", "Consistency"),
  ("2PCwithBTM", "MC4_TRUE_TRUE.tla", "Consistency"),
  ("2PCwithBTM", "MC10_FALSE_FALSE.tla", "Consistency"),
  ("2PCwithBTM", "MC10_TRUE_TRUE.tla", "Consistency"),
  ("2PCwithBTM", "MC20_FALSE_FALSE.tla", "Consistency"),
  ("2PCwithBTM", "MC20_TRUE_TRUE.tla", "Consistency"),
  ("aba_asyn_byz", "MC4.tla", ""),
  ("aba_asyn_byz", "MC10.tla", ""),
  ("aba_asyn_byz", "MC20.tla", "")
)

def suiteForEncoding_examples(specs: Seq[(String, String, String)]) = {
  val suiteTimeLimit = "1h"

  def checkCmd(encoding: String, inv: String, searchInvMode: String, discardDisabled: String) = {
    Cmd(
      s"${encoding}-${discardDisabled}-${searchInvMode}",
      Opt("check"),
      Opt("--inv", inv),
      Opt("--smt-encoding", encoding),
      Opt("--tuning-options", s"search.invariant.mode=$searchInvMode"),
      Opt("--discard-disabled", discardDisabled)
    )
  }

  def runsForSpec(spec: (String, String, String)) = {
    val (folder, fileName, inv) = spec
    val filePath = s"${folder}/${fileName}"

    Bench.Runs(
      s"run-${folder}-${fileName}",
      timelimit = suiteTimeLimit,
      cmds = Seq(
        checkCmd("arrays", inv, "before", "true"),
        checkCmd("arrays", inv, "before", "false"),
        checkCmd("arrays", inv, "after", "true"),
        checkCmd("arrays", inv, "after", "false"),
        checkCmd("oopsla19", inv, "before", "true"),
        checkCmd("oopsla19", inv, "before", "false"),
        checkCmd("oopsla19", inv, "after", "true"),
        checkCmd("oopsla19", inv, "after", "false"),
      ),
      tasks = Seq(Tasks(s"task-$fileName", Seq(filePath))),
    )
  }

  Bench.Suite(
    name = s"005examples-apalache",
    runs = specs.map(runsForSpec)
  )
}