import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  indinvSuite,
  suiteForEncoding("SetAdd", Seq("array-encoding/SetAdd.tla")),
  suiteForEncoding("SetAddDel", Seq("array-encoding/SetAddDel.tla")),
  suiteForEncoding("SetSndRcv", Seq("array-encoding/SetSndRcv.tla")),
  suiteForEncoding(
    "SetSndRcv_NoFullDrop",
    Seq("array-encoding/SetSndRcv_NoFullDrop.tla"),
  ),
)

def suiteForEncoding(name: String, specs: Seq[String]) = {
  val maxLength = 4

  def checkCmd(encoding: String, length: Int) = {
    Cmd(
      s"${encoding}:length:${length}",
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
      encoding,
      timelimit = "2h",
      tasks = Seq(Tasks(s"SetAdd", specs)),
      cmds = lengths.map(checkCmd(encoding, _)),
    )
  }

  Bench.Suite(
    name = s"010encoding-${name}",
    runs = Seq(
      runsForEncoding("arrays"),
      runsForEncoding("oopsla19"),
    ),
  )
}

lazy val indinvSuite =
  Bench.Suite(
    name = "001indinv-apalache",
    runs = Seq(
      Bench.Runs(
        "APAEWD840",
        timelimit = "3h",
        cmds = Seq(
          Cmd(
            "no init",
            Opt("check"),
            Opt("--inv", "InvAndTypeOK"),
            Opt("--length", 0),
            Opt("--cinit", "ConstInit10"),
          ),
          Cmd(
            "--init=InvAndTypeOK",
            Opt("check"),
            Opt("--init", "InvAndTypeOK"),
            Opt("--inv", "InvAndTypeOK"),
            Opt("--length", 1),
            Opt("--cinit", "ConstInit10"),
          ),
        ),
        tasks = Seq(Tasks("APAEWD840", Seq("ewd840/APAEWD840.tla"))),
      ),
      Bench.Runs(
        "APABakery",
        timelimit = "3h",
        cmds = Seq(
          Cmd(
            "--init=Init",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--inv", "Inv"),
            Opt("--length", 0),
          ),
          Cmd(
            "--init=Inv",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--inv", "Inv"),
            Opt("--length", 1),
          ),
        ),
        tasks = Seq(Tasks("APABakery", Seq("Bakery-Boulangerie/APABakery.tla"))),
      ),
      Bench.Runs(
        "APAbcastByz",
        timelimit = "3h",
        cmds = Seq(
          Cmd(
            "--init=InitNoBcast",
            Opt("check"),
            Opt("--init", "IndInv_Unforg_NoBcast"),
            Opt("--inv", "InitNoBcast"),
            Opt("--length", 0),
            Opt("--cinit", "ConstInit4"),
          ),
          Cmd(
            "--init=IndInv_Unforg_NoBcast",
            Opt("check"),
            Opt("--init", "IndInv_Unforg_NoBcast"),
            Opt("--inv", "IndInv_Unforg_NoBcast"),
            Opt("--length", 1),
            Opt("--cinit", "ConstInit4"),
          ),
        ),
        tasks = Seq(Tasks("APAbcastByz.tla", Seq("bcastByz/APAbcastByz.tla"))),
      ),
      Bench.Runs(
        "APATwoPhase",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "no init",
            Opt("check"),
            Opt("--inv", "Inv"),
            Opt("--length", 0),
            Opt("--cinit", "ConstInit7"),
          ),
          Cmd(
            "--init=InitInv",
            Opt("check"),
            Opt("--init", "InitInv"),
            Opt("--inv", "Inv"),
            Opt("--length", 1),
            Opt("--cinit", "ConstInit7"),
          ),
        ),
        tasks = Seq(Tasks("APATwoPhase.tla", Seq("two-phase/APATwoPhase.tla"))),
      ),
    ),
  )
