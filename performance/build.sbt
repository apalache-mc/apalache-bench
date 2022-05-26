import BenchExecDsl._

enablePlugins(BenchExec)

val endiveSpecs = Seq(
  ("MC3_Consensus.tla", "Inv", "before")
  /*
  ("MC3_Simple.tla", "Inv", "before"),
  ("MC3_SimpleRegular.tla", "Inv", "before"),
  ("MC3_TCConsistent.tla", "Inv", "before"),
  ("MC3_TwoPhase.tla", "TCConsistent", "after"),
  ("MC3_client_server_ae.tla", "Safety", "after"),
  ("MC3_consensus_epr.tla", "Safety", "after"),
  ("MC3_consensus_forall.tla", "Safety", "after"),
  ("MC3_consensus_wo_decide.tla", "Safety", "after"),
  ("MC3_learning_switch.tla", "Safety", "before"),
  ("MC3_lockserv.tla", "Mutex", "before"),
  ("MC3_lockserv_automaton.tla", "Mutex", "before"),
  ("MC3_lockserver.tla", "Inv", "before"),
  ("MC3_majorityset_leader_election.tla", "Safety", "before"),
  ("MC3_naive_consensus.tla", "Safety", "before"),
  ("MC3_quorum_leader_election.tla", "Safety", "before"),
  ("MC3_sharded_kv.tla", "Safety", "before"),
  ("MC3_sharded_kv_no_lost_keys.tla", "Safety", "before"),
  ("MC3_simple_decentralized_lock.tla", "Inv", "before"),
  ("MC3_toy_consensus.tla", "Inv", "before"),
  ("MC3_toy_consensus_epr.tla", "Safety", "before"),
  ("MC3_toy_consensus_forall.tla", "Inv", "before"),
  ("MC3_two_phase_commit.tla", "Safety", "before"),
  ("MC3_MongoLoglessDynamicRaft.tla", "Safety", "before"),
   */
)

benchmarks ++= Seq(
  //indinvSuite,
  //bmcSuite,
  // suiteForEncoding("SetAdd", Seq("array-encoding/SetAdd.tla"))
  //suiteForEncoding("SetAddDel", Seq("array-encoding/SetAddDel.tla")),
  //suiteForEncoding("SetSndRcv", Seq("array-encoding/SetSndRcv.tla")),
  //suiteForEncoding("SetSndRcv_NoFullDrop", Seq("array-encoding/SetSndRcv_NoFullDrop.tla")),
  suiteForEncoding_endive(endiveSpecs)
)

def suiteForEncoding(name: String, specs: Seq[String]) = {
  val defaultMaxLength = 8
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
      tasks = Seq(Tasks(s"${name}-${encoding}", specs)),
      cmds = lengths.map(checkCmd(encoding, _)),
      group = Some(encoding),
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

def suiteForEncoding_endive(specs: Seq[(String, String, String)]) = {
  val endiveTimeLimit = "10s"

  def checkCmd(encoding: String, inv: String, searchInvMode: String) = {
    Cmd(
      encoding,
      Opt("check"),
      Opt("--no-deadlock"),
      Opt("--init", "Init"),
      Opt("--inv", inv),
      Opt("--next", "Next"),
      Opt("--smt-encoding", encoding),
      Opt("--tuning-options", s"search.invariant.mode=$searchInvMode")
    )
  }

  def runsForSpec(spec: (String, String, String)) = {
    val (name, inv, searchInvMode) = spec
    val specFile = s"endive/${name}"

    Bench.Runs(
      name,
      timelimit = "10s",
      tasks = Seq(Tasks(s"endive-$name", Seq(name))),
      cmds = Seq(checkCmd("arrays", inv, searchInvMode), checkCmd("oopsla19", inv, searchInvMode)),
      tasks = Seq(Tasks(s"endive-$name", Seq(specFile))),
      group = Some(name),
    )
  }

  Bench.Suite(
    name = s"011endive",
    //runs = specs.map(runsForSpec)
    runs = Seq(runsForSpec(specs.head))
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
        "Bakery",
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
        tasks = Seq(Tasks("Bakery", Seq("Bakery-Boulangerie/MC5_Bakery.tla"))),
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
      Bench.Runs(
        "ewd998",
        timelimit = "1h",
        cmds = Seq(
          Cmd(
            "inductive base",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--config", "ewd998/MC4_EWD998.cfg"),
            Opt("--inv", "TypedInv"),
            Opt("--length", 0),
          ),
          Cmd(
            "inductive step",
            Opt("check"),
            Opt("--init", "TypedInv"),
            Opt("--config", "ewd998/MC4_EWD998.cfg"),
            Opt("--inv", "TypedInv"),
            Opt("--length", 1),
          ),
        ),
        tasks = Seq(Tasks("ewd998", Seq("ewd998/EWD998.tla"))),
      ),
      Bench.Runs(
        "ewd998-atd",
        timelimit = "1h",
        cmds = Seq(
          Cmd(
            "inductive base",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--config", "ewd998/ATD.cfg"),
            Opt("--inv", "IndInv"),
            Opt("--length", 0),
          ),
          Cmd(
            "inductive step",
            Opt("check"),
            Opt("--init", "IndInv"),
            Opt("--config", "ewd998/ATD.cfg"),
            Opt("--inv", "IndInv"),
            Opt("--length", 1),
          ),
        ),
        tasks = Seq(Tasks("ewd998", Seq("ewd998/AsyncTerminationDetection.tla"))),
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
            Opt("check"),
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
            Opt("check"),
            Opt("--inv", "SafetyInv"),
            Opt("--length", 15),
            Opt("--cinit=ConstInit"),
          )
        ),
        tasks = Seq(Tasks("APAPrisoners", Seq("Prisoners/APAPrisoners.tla"))),
      ),
      Bench.Runs(
        "Bakery",
        timelimit = "10h",
        cmds = Seq(
          Cmd(
            "MutualExlusion-invariant",
            Opt("check"),
            Opt("--inv", "MutualExclusion"),
            Opt("--length", 8),
          )
        ),
        tasks = Seq(Tasks("Bakery", Seq("Bakery-Boulangerie/MC5_Bakery.tla"))),
      ),
      Bench.Runs(
        "APAEWD840",
        timelimit = "1h",
        cmds = Seq(
          Cmd(
            "length-12",
            Opt("check"),
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
            "length-30",
            Opt("check"),
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
            Opt("check"),
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
            Opt("check"),
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
            "ConstInit4",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit4"),
          ),
          Cmd(
            "ConstInit20",
            Opt("check"),
            Opt("--init", "Init"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit20"),
          ),
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
            "ConstInit4",
            Opt("check"),
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
            "ConstInit6",
            Opt("check"),
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
            "ConstInit3",
            Opt("check"),
            Opt("--inv", "TCConsistent"),
            Opt("--length", 11),
            Opt("--cinit", "ConstInit3"),
          ),
          Cmd(
            "ConstInit7",
            Opt("check"),
            Opt("--inv", "TCConsistent"),
            Opt("--length", 10),
            Opt("--cinit", "ConstInit7"),
          ),
        ),
        tasks = Seq(Tasks("APATwoPhase", Seq("two-phase/APATwoPhase.tla"))),
      ),
      Bench.Runs(
        "Apa3Paxos",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "Apa3Paxos",
            Opt("check"),
            Opt("--inv", "OneValuePerBallot"),
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
            Opt("check"),
            Opt("--inv", "OneValuePerBallot"),
            Opt("--length", 14),
          )
        ),
        tasks = Seq(Tasks("Apa5Paxos", Seq("paxos/Apa5Paxos.tla"))),
      ),
      Bench.Runs(
        "APAraft",
        timelimit = "23h",
        cmds = Seq(
          Cmd(
            "APAraft",
            Opt("check"),
            Opt("--inv", "OneLeader"),
            Opt("--length", 8),
          )
        ),
        tasks = Seq(Tasks("APAraft", Seq("raft/APAraft.tla"))),
      ),
      Bench.Runs(
        "ewd998-atd",
        timelimit = "3h",
        cmds = Seq(
          Cmd(
            "ewd998-atd",
            Opt("check"),
            Opt("--config", "ewd998/ATD.cfg"),
            Opt("--length", 10),
          )
        ),
        tasks = Seq(Tasks("ewd998-atd", Seq("ewd998/AsyncTerminationDetection.tla"))),
      ),
      Bench.Runs(
        "ewd998",
        timelimit = "3h",
        cmds = Seq(
          Cmd(
            "ewd998",
            Opt("check"),
            Opt("--config", "ewd998/MC4_EWD998.cfg"),
            Opt("--inv", "TerminationDetection"),
            Opt("--length", 10),
          )
        ),
        tasks = Seq(Tasks("ewd998", Seq("ewd998/EWD998.tla"))),
      ),
    ),
  )
