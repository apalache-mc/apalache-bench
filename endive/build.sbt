import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("004endive-apalache", endiveSpecs, cmdParsDefault),
)

lazy val endiveSpecs = Seq(
  Spec("endive-specs", "MC3_Consensus.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_Consensus.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_Simple.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_Simple.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_SimpleRegular.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_SimpleRegular.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_TwoPhase.tla", inv =  Some("TCConsistent")),
  Spec("endive-specs", "MC10_TwoPhase.tla", inv =  Some("TCConsistent")),
  Spec("endive-specs", "MC3_client_server_ae.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_client_server_ae.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_consensus_epr.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_consensus_epr.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_consensus_forall.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_consensus_forall.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_consensus_wo_decide.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_consensus_wo_decide.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_learning_switch.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_learning_switch.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_lockserv.tla", inv =  Some("Mutex")),
  Spec("endive-specs", "MC10_lockserv.tla", inv =  Some("Mutex")),
  Spec("endive-specs", "MC3_lockserv_automaton.tla", inv =  Some("Mutex")),
  Spec("endive-specs", "MC10_lockserv_automaton.tla", inv =  Some("Mutex")),
  Spec("endive-specs", "MC3_lockserver.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_lockserver.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_majorityset_leader_election.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_majorityset_leader_election.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_naive_consensus.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_naive_consensus.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_quorum_leader_election.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_quorum_leader_election.tla", inv =  Some("Inv")),
  //Spec("endive-specs", "MC15_quorum_leader_election.tla", inv = Some("Inv")), // increased size to check scalability
  //Spec("endive-specs", "MC20_quorum_leader_election.tla", inv = Some("Inv")), // increased size to check scalability
  Spec("endive-specs", "MC3_sharded_kv.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_sharded_kv.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_sharded_kv_no_lost_keys.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_sharded_kv_no_lost_keys.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_simple_decentralized_lock.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_simple_decentralized_lock.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_toy_consensus.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_toy_consensus.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_toy_consensus_epr.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_toy_consensus_epr.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_toy_consensus_forall.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC10_toy_consensus_forall.tla", inv =  Some("Inv")),
  Spec("endive-specs", "MC3_two_phase_commit.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_two_phase_commit.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC3_MongoLoglessDynamicRaft.tla", inv =  Some("Safety")),
  Spec("endive-specs", "MC10_MongoLoglessDynamicRaft.tla", inv =  Some("Safety")),
)

lazy val twoPhase_Str_Int_test = Seq(
  Spec("test", "MC10_TwoPhaseStr.tla", inv =  Some("TCConsistent")),
  Spec("test", "MC10_TwoPhaseInt.tla", inv =  Some("TCConsistent")),
)