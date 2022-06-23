import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_endive(endiveSpecs)
)

lazy val endiveSpecs = Seq(
  ("MC3_Consensus.tla", "Inv", "before"),
  ("MC3_Simple.tla", "Inv", "before"),
  ("MC3_SimpleRegular.tla", "Inv", "before"),
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
  ("MC3_MongoLoglessDynamicRaft.tla", "Safety", "before")
)

def suiteForEncoding_endive(specs: Seq[(String, String, String)]) = {
  val suiteTimeLimit = "1h"

  def checkCmd(encoding: String, inv: String, searchInvMode: String, discardDisabled: String) = {
    Cmd(
      s"${encoding}-${discardDisabled}",
      Opt("check"),
      Opt("--no-deadlock"),
      Opt("--init", "Init"),
      Opt("--inv", inv),
      Opt("--next", "Next"),
      Opt("--smt-encoding", encoding),
      Opt("--tuning-options", s"search.invariant.mode=$searchInvMode"),
      Opt("--discard-disabled", discardDisabled)
    )
  }

  def runsForSpec(spec: (String, String, String)) = {
    val (name, inv, searchInvMode) = spec
    val specFile = s"endive-specs/${name}"

    Bench.Runs(
      s"run-${name}",
      timelimit = suiteTimeLimit,
      cmds = Seq(
        checkCmd("arrays", inv, searchInvMode, "true"),
        checkCmd("arrays", inv, searchInvMode, "false"),
        checkCmd("oopsla19", inv, searchInvMode, "true"),
        checkCmd("oopsla19", inv, searchInvMode, "false")
      ),
      tasks = Seq(Tasks(s"task-$name", Seq(specFile))),
    )
  }

  Bench.Suite(
    name = s"003endive-apalache",
    runs = specs.map(runsForSpec)
  )
}