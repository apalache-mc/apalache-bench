import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_examples(examplesSpecs)
)

lazy val examplesSpecs = Seq(
  ("MC4_FALSE_FALSE.tla", "Consistency"),
  ("MC4_TRUE_TRUE.tla", "Consistency"),
  ("MC10_FALSE_FALSE.tla", "Consistency"),
  ("MC10_TRUE_TRUE.tla", "Consistency"),
  ("MC20_FALSE_FALSE.tla", "Consistency"),
  ("MC20_TRUE_TRUE.tla", "Consistency")
)

def suiteForEncoding_examples(specs: Seq[(String, String)]) = {
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

  def runsForSpec(spec: (String, String)) = {
    val (name, inv) = spec
    val specFile = s"2PCwithBTM/${name}"

    Bench.Runs(
      s"run-${name}",
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
      tasks = Seq(Tasks(s"task-$name", Seq(specFile))),
    )
  }

  Bench.Suite(
    name = s"005examples-apalache",
    runs = specs.map(runsForSpec)
  )
}