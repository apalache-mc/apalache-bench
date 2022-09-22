import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("005examples-apalache", testRun, cmdParsDefault)
)

lazy val testRun = Seq(
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC20.tla", init = "Init0", inv = Some("Unforg"))
)

lazy val examplesSpecs = Seq(
  Spec("2PCwithBTM", "MC4_FALSE_FALSE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC4_TRUE_TRUE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC10_FALSE_FALSE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC10_TRUE_TRUE.tla", inv = Some("Consistency")),
  Spec("aba_asyn_byz", "MC4.tla"),
  Spec("aba_asyn_byz", "MC10.tla"),
  Spec("aba_asyn_byz", "MC20.tla"),
  Spec("bakery", "MC3.tla", inv = Some("MutualExclusion")),
  Spec("bakery", "MC5.tla", inv = Some("MutualExclusion")),
  Spec("bakery", "MC10.tla", inv = Some("MutualExclusion")),
  Spec("bakery", "MC3.tla", length = 0, inv = Some("Inv")),
  Spec("bakery", "MC3.tla", length = 1, init = "Inv", inv =  Some("Inv")),
  Spec("bakery", "MC5.tla", length = 0, inv = Some("Inv")),
  Spec("bakery", "MC5.tla", length = 1, init = "Inv", inv = Some("Inv")),
  Spec("bakery", "MC10.tla", length = 0, inv = Some("Inv")),
  Spec("bakery", "MC10.tla", length = 1, init = "Inv", inv = Some("Inv")),
  Spec("changRoberts", "MC4.tla", inv = Some("Correctness")),
  Spec("changRoberts", "MC10.tla", inv = Some("Correctness")),
  Spec("ewd998", "MC4.tla", inv = Some("TerminationDetection")),
  Spec("ewd998", "MC10.tla", inv = Some("TerminationDetection")),
  Spec("paxos", "MC3.tla", length = 13, inv = Some("V!OneValuePerBallot")),
  Spec("readersWriters", "MC4.tla", inv = Some("Safety")),
  Spec("readersWriters", "MC10.tla", inv = Some("Safety")),
  Spec("readersWriters", "MC20.tla", inv = Some("Safety")),
  Spec("royal", "Royal.tla", inv = Some("ContractCantGoNegative"))
)
