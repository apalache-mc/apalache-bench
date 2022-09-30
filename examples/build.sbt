import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("005examples-apalache", testAba, cmdParsDefault),
  suiteGen("005examples-apalache", testTendermint, cmdParsDefault),
)

lazy val testAba = Seq( // not related to a certain Swedish band
  // length is 2T+3, with N > 3T; N is the number on the MC files
  // inv holds for Init0 and does not hold for Init
  /*
  Spec("aba_asyn_byz", "MC4.tla", length = 5, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC7.tla", length = 7, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC10.tla", length = 9, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC13.tla", length = 11, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC16.tla", length = 13, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC19.tla", length = 15, init = "Init0", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC4.tla", length = 5, init = "Init", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC7.tla", length = 7, init = "Init", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC10.tla", length = 9, init = "Init", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC13.tla", length = 11, init = "Init", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC16.tla", length = 13, init = "Init", inv = Some("Unforg")),
  Spec("aba_asyn_byz", "MC19.tla", length = 15, init = "Init", inv = Some("Unforg")),
   */
  Spec("aba_asyn_byz_sets", "MC4.tla", length = 5, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC7.tla", length = 7, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC10.tla", length = 9, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC13.tla", length = 11, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC16.tla", length = 13, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC19.tla", length = 15, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC4.tla", length = 5, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC7.tla", length = 7, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC10.tla", length = 9, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC13.tla", length = 11, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC16.tla", length = 13, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_sets", "MC19.tla", length = 15, init = "Init", inv = Some("NoDecide")),
)

lazy val testTendermint = Seq(
  //Spec("tendermint", "MC_n4_f1.tla", length = 1, init = "TypedInv", cInit = Some("ConstInit"), inv = Some("TypedInv"), features = None),
  Spec("tendermint", "MC_n4_f1.tla", length = 8, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n5_f1.tla", length = 9, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n6_f1.tla", length = 10, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n4_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n5_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n6_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
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
  Spec("royal", "Royal.tla", inv = Some("ContractCantGoNegative")),
  Spec("floodmin", "MC13_4_4_floodmin_k1.tla", length = 20, inv = Some("ValidityInv")),
  //Spec("erc20", "MC_ERC20.tla", inv = Some("NoTransferAboveApproved")), // spec needs updating
  //Spec("egalitarianPaxos", "EgalitarianPaxos.tla", cInit = Some("ConstInit")), // spec is too complex for 1h execution
)
