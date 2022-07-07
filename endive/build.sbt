import BenchExecDsl._
import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteForEncoding_endive(endiveSpecs)
)

lazy val endiveSpecs = Seq(
  Spec("endive-specs","MC3_Consensus.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_Simple.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_SimpleRegular.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_TwoPhase.tla", 10, inv = "TCConsistent"),
  Spec("endive-specs","MC3_client_server_ae.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_consensus_epr.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_consensus_forall.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_consensus_wo_decide.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_learning_switch.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_lockserv.tla", 10, inv = "Mutex"),
  Spec("endive-specs","MC3_lockserv_automaton.tla", 10, inv = "Mutex"),
  Spec("endive-specs","MC3_lockserver.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_majorityset_leader_election.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_naive_consensus.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_quorum_leader_election.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_sharded_kv.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_sharded_kv_no_lost_keys.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_simple_decentralized_lock.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_toy_consensus.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_toy_consensus_epr.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_toy_consensus_forall.tla", 10, inv = "Inv"),
  Spec("endive-specs","MC3_two_phase_commit.tla", 10, inv = "Safety"),
  Spec("endive-specs","MC3_MongoLoglessDynamicRaft.tla", 10, inv = "Safety")
)

def suiteForEncoding_endive(specs: Seq[Spec]) = {
  val suiteTimeLimit = "1h"

  def checkCmd(cmdPar: CmdPar) = {
    Cmd(
      s"${cmdPar.encoding}-${cmdPar.discardDisabled}-${cmdPar.searchInvMode}",
      Opt("check"),
      Opt("--init", cmdPar.init),
      Opt("--inv", cmdPar.inv),
      Opt("--length", cmdPar.length),
      Opt("--smt-encoding", cmdPar.encoding),
      Opt("--tuning-options", s"search.invariant.mode=${cmdPar.searchInvMode}"),
      Opt("--discard-disabled", cmdPar.discardDisabled),
    )
  }

  def runsForSpec(spec: Spec) = {
    val filePath = s"${spec.folder}/${spec.file}"
    val commands = Seq(
      CmdPar(spec.init, spec.inv, spec.length, "arrays", "before", "true"),
      CmdPar(spec.init, spec.inv, spec.length, "arrays", "before", "false"),
      CmdPar(spec.init, spec.inv, spec.length, "arrays", "after", "true"),
      CmdPar(spec.init, spec.inv, spec.length, "arrays", "after", "false"),
      CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "before", "true"),
      CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "before", "false"),
      CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "after", "true"),
      CmdPar(spec.init, spec.inv, spec.length, "oopsla19", "after", "false"),
    )

    Bench.Runs(
      s"run-${spec.folder}-${spec.file}",
      timelimit = suiteTimeLimit,
      cmds = commands.map(checkCmd),
      tasks = Seq(Tasks(s"task-${spec.file}", Seq(filePath))),
    )
  }

  Bench.Suite(
    name = s"004endive-apalache",
    runs = specs.map(runsForSpec)
  )
}