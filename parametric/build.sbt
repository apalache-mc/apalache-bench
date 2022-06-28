import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding("SetAdd", Seq("parametric-specs/SetAdd.tla")),
  suiteForEncoding("SetDel", Seq("parametric-specs/SetDel.tla")),
  suiteForEncoding("SetAddDel", Seq("parametric-specs/SetAddDel.tla")),
  suiteForEncoding("SetMembership", Seq("parametric-specs/SetMembership.tla")),
  suiteForEncoding("Subset", Seq("parametric-specs/Subset.tla")),
  suiteForEncoding("SetFilter", Seq("parametric-specs/SetFilter.tla")),
  suiteForEncoding("SetMap", Seq("parametric-specs/SetMap.tla")),
  suiteForEncoding("SetSndRcv", Seq("parametric-specs/SetSndRcv.tla")),
  suiteForEncoding("SetSndRcv_NoFullDrop", Seq("parametric-specs/SetSndRcv_NoFullDrop.tla")),
  suiteForEncoding("FunUse", Seq("parametric-specs/FunUse.tla"))
)

def suiteForEncoding(name: String, specs: Seq[String]) = {
  val suiteTimeLimit = "1h"

  val defaultMaxLength = 30
  val maxLength =
    // We default to the empty string for fallback so that we
    // can gracefully deal with the case when the environment
    // variable is not assigned a value
    sys.env.getOrElse("ENCODING_COMPARISON_MAX_LENGTH", "") match {
      case "" => defaultMaxLength
      case i  => i.toInt
    }

  def checkCmd(encoding: String, length: Int) = {
    Cmd(
      s"${encoding}-length:${length}",
      Opt("check"),
      Opt("--init", "Init"),
      Opt("--inv", "Inv"),
      Opt("--next", "Next"),
      Opt("--smt-encoding", encoding),
      Opt("--length", length),
      Opt("--cinit", s"CInit${length}"),
    )
  }

  def runsForEncoding(encoding: String) = {
    val lengths = 0.to(maxLength, 2)
    Bench.Runs(
      s"run-${encoding}",
      timelimit = suiteTimeLimit,
      cmds = lengths.map(checkCmd(encoding, _)),
      tasks = Seq(Tasks(s"task-${name}-${encoding}", specs))
    )
  }

  Bench.Suite(
    name = s"003parametric-${name}",
    runs = Seq(
      runsForEncoding("arrays"),
      runsForEncoding("oopsla19"),
    ),
  )
}