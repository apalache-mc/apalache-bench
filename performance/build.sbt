import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  indinvSuite,
  bmcSuite,
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

lazy val bmcSuite =
  Bench.Suite(
    name = "002bmc-apalache",
    runs = Seq(
      Bench.Runs(
        "APAtraffic",
        timelimit = "1h",
        cmds = Seq(
          Cmd(
            "APATraffic",
            Opt("--length", 4),
          )
        ),
        tasks = Seq(Tasks("APATraffic", Seq("traffic/APAtraffic.tla"))),
      ),
      Bench.Runs(
        "APAPrisoners",
        timelimit = "30m",
        cmds = Seq(
          Cmd(
            "APAPrisoners",
            Opt("--inv", "SafetyInv"),
            Opt("--length", 15),
            Opt("--cinit=ConstInit"),
          )
        ),
        tasks = Seq(Tasks("APAPrisoners", Seq("Prisoners/APAPrisoners.tla"))),
      ),
      Bench.Runs(
        "APABakery",
        timelimit = "10h",
        cmds = Seq(
          Cmd("APABakery", Opt("--inv", "MutualExclusion"), Opt("--length", 8))
        ),
        tasks = Seq(Tasks("APABakery", Seq("Bakery-Boulangerie/APABakery.tla"))),
      ),
      Bench.Runs(
        "APAEWD840",
        timelimit = "1h",
        cmds = Seq(
          Cmd(
            "APAEWD840",
            Opt("--inv", "Inv"),
            Opt("--length", 12),
            Opt("--cinit", "ConstInit4"),
          )
        ),
        tasks = Seq(Tasks("APAEWD840", Seq("ewd840/APAEWD840.tla"))),
      ),
      Bench.Runs(
        "APAEWD840",
        timelimit = "5h",
        cmds = Seq(
          Cmd(
            "APAEWD840",
            Opt("--inv", "Inv"),
            Opt("--length", 30),
            Opt("--cinit", "ConstInit10"),
          )
        ),
        tasks = Seq(Tasks("APAEWD840", Seq("ewd840/APAEWD840.tla"))),
      ),
      Bench.Runs(
        "APASimpleAllocator",
        timelimit = "10h",
        cmds = Seq(
          Cmd(
            "APASimpleAllocator",
            Opt("--inv", "ResourceMutex"),
            Opt("--length", 7),
            Opt("--cinit", "ConstInit22"),
          )
        ),
        tasks = Seq(
          Tasks("APASimpleAllocator", Seq("allocator/APASimpleAllocator.tla"))
        ),
      ),
      Bench.Runs(
        "APASimpleAllocator",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "APASimpleAllocator",
            Opt("--inv", "ResourceMutex"),
            Opt("--length", 7),
            Opt("--cinit", "ConstInit53"),
          )
        ),
        tasks = Seq(
          Tasks("APASimpleAllocator", Seq("allocator/APASimpleAllocator.tla"))
        ),
      ),
      Bench.Runs(
        "APAbcastFolklore",
        timelimit = "30m",
        cmds = Seq(
          Cmd(
            "APAbcastFolklore",
            Opt("--init", "Init"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit4"),
          )
        ),
        tasks = Seq(
          Tasks("APAbcastFolklore", Seq("bcastFolklore/APAbcastFolklore.tla"))
        ),
      ),
      Bench.Runs(
        "APAbcastFolklore",
        timelimit = "30m",
        cmds = Seq(
          Cmd(
            "APAbcastFolklore",
            Opt("--init", "Init"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit20"),
          )
        ),
        tasks = Seq(
          Tasks("APAbcastFolklore", Seq("bcastFolklore/APAbcastFolklore.tla"))
        ),
      ),
      Bench.Runs(
        "APAbcastByz",
        timelimit = "30m",
        cmds = Seq(
          Cmd(
            "APAbcastByz",
            Opt("--init", "Init"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit4"),
          )
        ),
        tasks = Seq(Tasks("APAbcastByz", Seq("bcastByz/APAbcastByz.tla"))),
      ),
      Bench.Runs(
        "APAbcastByz",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "APAbcastByz",
            Opt("--init", "Init"),
            Opt("--length", 11),
            Opt("--cinit", "ConstInit6"),
          )
        ),
        tasks = Seq(Tasks("APAbcastByz", Seq("bcastByz/APAbcastByz.tla"))),
      ),
      Bench.Runs(
        "APATwoPhase",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "APATwoPhase",
            Opt("--init", "TCConsistent"),
            Opt("--length", 11),
            Opt("--cinit", "ConstInit3"),
          )
        ),
        tasks = Seq(Tasks("APATwoPhase", Seq("two-phase/APATwoPhase.tla"))),
      ),
      Bench.Runs(
        "APATwoPhase",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "APATwoPhase",
            Opt("--init", "TCConsistent"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit7"),
          )
        ),
        tasks = Seq(Tasks("APATwoPhase", Seq("two-phase/APATwoPhase.tla"))),
      ),
      Bench.Runs(
        "Apa3Paxos",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "Apa3Paxos",
            Opt("--init", "OneValuePerBallot"),
            Opt("--length", 13),
          )
        ),
        tasks = Seq(Tasks("Apa3Paxos", Seq("paxos/Apa3Paxos.tla"))),
      ),
      Bench.Runs(
        "Apa5Paxos",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "Apa5Paxos",
            Opt("--init", "OneValuePerBallot,"),
            Opt("--length", 14),
          )
        ),
        tasks = Seq(Tasks("Apa5Paxos", Seq("paxos/Apa5Paxos.tla"))),
      ),
      Bench.Runs(
        "APAraft",
        timelimit = "23h",
        cmds =
          Seq(Cmd("APAraft", Opt("--init", "OneLeader"), Opt("--length", 8))),
        tasks = Seq(Tasks("APAraft", Seq("raft/APAraft.tla"))),
      ),
    ),
  )
