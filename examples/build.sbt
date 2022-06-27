import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_examples(examplesSpecs)
)

// (folder, spec, init, inv, length)
lazy val examplesSpecs = Seq(
  ("2PCwithBTM", "MC4_FALSE_FALSE.tla", "Init", "Consistency", "10"),
  ("2PCwithBTM", "MC4_TRUE_TRUE.tla", "Init", "Consistency", "10"),
  ("2PCwithBTM", "MC10_FALSE_FALSE.tla", "Init", "Consistency", "10"),
  ("2PCwithBTM", "MC10_TRUE_TRUE.tla", "Init", "Consistency", "10"),
  ("2PCwithBTM", "MC20_FALSE_FALSE.tla", "Init", "Consistency", "10"),
  ("2PCwithBTM", "MC20_TRUE_TRUE.tla", "Init", "Consistency", "10"),
  ("aba_asyn_byz", "MC4.tla", "Init", "", "10"),
  ("aba_asyn_byz", "MC10.tla", "Init", "", "10"),
  ("aba_asyn_byz", "MC20.tla", "Init", "", "10"),
  ("bakery", "MC3.tla", "Init", "MutualExclusion", "10"),
  ("bakery", "MC3.tla", "Init", "Inv", "0"),
  ("bakery", "MC3.tla", "Inv", "Inv", "1"),
  ("changRoberts", "MC4.tla", "Init", "Correctness", "10"),
  ("changRoberts", "MC10.tla", "Init", "Correctness", "10"),
  ("changRoberts", "MC20.tla", "Init", "Correctness", "10")
)

def suiteForEncoding_examples(specs: Seq[(String, String, String, String, String)]) = {
  val suiteTimeLimit = "1h"

  def checkCmd(init: String, inv: String, length: String, encoding: String, searchInvMode: String, discardDisabled: String) = {
    Cmd(
      s"${encoding}-${discardDisabled}-${searchInvMode}",
      Opt("check"),
      Opt("--init", init),
      Opt("--inv", inv),
      Opt("--length", length),
      Opt("--smt-encoding", encoding),
      Opt("--tuning-options", s"search.invariant.mode=$searchInvMode"),
      Opt("--discard-disabled", discardDisabled)
    )
  }

  def runsForSpec(spec: (String, String, String, String, String)) = {
    val (folder, fileName, init, inv, length) = spec
    val filePath = s"${folder}/${fileName}"

    Bench.Runs(
      s"run-${folder}-${fileName}",
      timelimit = suiteTimeLimit,
      cmds = Seq(
        checkCmd(init, inv, length, "arrays", "before", "true"),
        checkCmd(init, inv, length, "arrays", "before", "false"),
        checkCmd(init, inv, length, "arrays", "after", "true"),
        checkCmd(init, inv, length, "arrays", "after", "false"),
        checkCmd(init, inv, length, "oopsla19", "before", "true"),
        checkCmd(init, inv, length, "oopsla19", "before", "false"),
        checkCmd(init, inv, length, "oopsla19", "after", "true"),
        checkCmd(init, inv, length, "oopsla19", "after", "false"),
      ),
      tasks = Seq(Tasks(s"task-$fileName", Seq(filePath))),
    )
  }

  Bench.Suite(
    name = s"005examples-apalache",
    runs = specs.map(runsForSpec)
  )
}