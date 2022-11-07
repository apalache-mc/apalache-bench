import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("005examples-apalache", examplesSpecs, cmdParsDefault),
  // Suites to check scalability
  //suiteGen("005examples-apalache", abaSpecs, cmdParsDefault),
  //suiteGen("005examples-apalache", tendermintSpecs, cmdParsDefault),
  //suiteGen("005examples-apalache", othersSpecs, cmdParsDefault),
)

lazy val examplesSpecs = Seq(
  Spec("2PCwithBTM", "MC4_FALSE_FALSE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC4_TRUE_TRUE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC10_FALSE_FALSE.tla", inv = Some("Consistency")),
  Spec("2PCwithBTM", "MC10_TRUE_TRUE.tla", inv = Some("Consistency")),
  Spec("aba_asyn_byz", "MC4.tla"),
  Spec("aba_asyn_byz", "MC10.tla"),
  Spec("aba_asyn_byz", "MC19.tla"),
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
  //Spec("egalitarianPaxos", "EgalitarianPaxos.tla", cInit = Some("ConstInit")), // spec is too complex, leads to TO
)

// Not related to a certain Swedish band...
lazy val abaSpecs = Seq(
  // length is 2T+3, with N > 3T; N is the number on the MC files
  // inv holds for Init0 and does not hold for Init
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
  Spec("aba_asyn_byz_fns", "MC4.tla", length = 5, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC7.tla", length = 7, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC10.tla", length = 9, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC13.tla", length = 11, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC16.tla", length = 13, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC19.tla", length = 15, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC4.tla", length = 5, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC7.tla", length = 7, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC10.tla", length = 9, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC13.tla", length = 11, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC16.tla", length = 13, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_fns", "MC19.tla", length = 15, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC4.tla", length = 5, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC7.tla", length = 7, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC10.tla", length = 9, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC13.tla", length = 11, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC16.tla", length = 13, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC19.tla", length = 15, init = "Init0", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC4.tla", length = 5, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC7.tla", length = 7, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC10.tla", length = 9, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC13.tla", length = 11, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC16.tla", length = 13, init = "Init", inv = Some("NoDecide")),
  Spec("aba_asyn_byz_counters", "MC19.tla", length = 15, init = "Init", inv = Some("NoDecide")),
)

lazy val tendermintSpecs = Seq(
  Spec("tendermint", "MC_n4_f1.tla", length = 8, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n5_f1.tla", length = 9, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n6_f1.tla", length = 10, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n4_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n5_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
  Spec("tendermint", "MC_n6_f2.tla", length = 99, cInit = Some("ConstInit"), inv = Some("Agreement"), features = None),
)

lazy val othersSpecs = Seq(
  // length is 2T+3, with N > 3T; N is the number on the MC files
  Spec("bcastByz", "MC4.tla", length = 5, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC7.tla", length = 7, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC10.tla", length = 9, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC13.tla", length = 11, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC16.tla", length = 13, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC19.tla", length = 15, init = "InitNoBcast", inv = Some("Unforg")),
  Spec("bcastByz", "MC4.tla", length = 5, init = "Init", inv = Some("Unforg")),
  Spec("bcastByz", "MC7.tla", length = 7, init = "Init", inv = Some("Unforg")),
  Spec("bcastByz", "MC10.tla", length = 9, init = "Init", inv = Some("Unforg")),
  Spec("bcastByz", "MC13.tla", length = 11, init = "Init", inv = Some("Unforg")),
  Spec("bcastByz", "MC16.tla", length = 13, init = "Init", inv = Some("Unforg")),
  Spec("bcastByz", "MC19.tla", length = 15, init = "Init", inv = Some("Unforg")),
  Spec("bosco", "MC4.tla", length = 5, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC7.tla", length = 7, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC10.tla", length = 9, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC13.tla", length = 11, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC16.tla", length = 13, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC19.tla", length = 15, init = "Init0", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC4.tla", length = 5, init = "Init", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC7.tla", length = 7, init = "Init", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC10.tla", length = 9, init = "Init", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC13.tla", length = 11, init = "Init", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC16.tla", length = 13, init = "Init", inv = Some("OneStep0Mod")),
  Spec("bosco", "MC19.tla", length = 15, init = "Init", inv = Some("OneStep0Mod")),
  Spec("cf1s_folklore", "MC4.tla", length = 6, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC7.tla", length = 8, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC10.tla", length = 10, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC13.tla", length = 12, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC16.tla", length = 14, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC19.tla", length = 16, init = "Init0", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC4.tla", length = 6, init = "Init", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC7.tla", length = 8, init = "Init", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC10.tla", length = 10, init = "Init", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC13.tla", length = 12, init = "Init", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC16.tla", length = 14, init = "Init", inv = Some("OneStep0")),
  Spec("cf1s_folklore", "MC19.tla", length = 16, init = "Init", inv = Some("OneStep0")),
  Spec("nbacg_guer01", "MC4.tla", length = 5, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC7.tla", length = 7, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC10.tla", length = 9, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC13.tla", length = 11, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC16.tla", length = 13, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC19.tla", length = 15, init = "InitYes", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC4.tla", length = 5, init = "Init", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC7.tla", length = 7, init = "Init", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC10.tla", length = 9, init = "Init", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC13.tla", length = 11, init = "Init", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC16.tla", length = 13, init = "Init", inv = Some("Agrr")),
  Spec("nbacg_guer01", "MC19.tla", length = 15, init = "Init", inv = Some("Agrr")),
)