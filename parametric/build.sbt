import BenchExecDsl._
import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("003parametric-apalache", parametricSpecs, cmdGenGen())
)

lazy val parametricSpecs = Seq(
  Spec("parametric-specs", "SetAdd.tla", inv = "Inv"),
  Spec("parametric-specs", "SetAddDel.tla", inv = "Inv"),
  Spec("parametric-specs", "SetSndRcv.tla", inv = "Inv"),
  Spec("parametric-specs", "SetSndRcv_NoFullDrop.tla", inv = "Inv"),
)

lazy val cmds =
  val defaultMaxLength = 14
  val maxLength = sys.env.getOrElse("ENCODING_COMPARISON_MAX_LENGTH", "") match {
    // We default to the empty string for fallback so that we
    // can gracefully deal with the case when the environment
    // variable is not assigned a value
    case "" => defaultMaxLength
    case i  => i.toInt
  }
  val lengths = 0.to(maxLength, 2)

  lengths.map(parametricCheckCmdGen)
}

def parametricCheckCmdGen(length: Int) = {
  (spec: Spec, cmdPar: CmdPar) =>
    Cmd(
      s"$Cmd-CInit${length}-${cmdPar.encoding}-${cmdPar.discardDisabled}-${cmdPar.searchInvMode}",
      Opt("check"),
      Opt("--length", length), // Parametric length
      Opt("--init", spec.init),
      Opt("--next", spec.next),
      Opt("--cinit", s"CInit${length}"), // Parametric cinit
      Opt("--inv", spec.inv),
      Opt("--smt-encoding", cmdPar.encoding),
      Opt("--tuning-options", s"search.invariant.mode=${cmdPar.searchInvMode}"),
      Opt("--discard-disabled", cmdPar.discardDisabled),
    )
}