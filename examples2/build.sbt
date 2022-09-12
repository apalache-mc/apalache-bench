import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("006examples2-apalache", examplesSpecs, cmdParsDefault)
)

lazy val examplesSpecs = Seq(
  //Spec("egalitarianPaxos", "EgalitarianPaxos.tla", cInit = Some("ConstInit")),
  //Spec("tendermint", "MC_n4_f1.tla", length = 1, init = "TypedInv", cInit = Some("ConstInit"), inv = Some("TypedInv")),
  //Spec("floodmin", "MC13_4_4_floodmin_k1.tla", length = 20, inv = Some("ValidityInv")),
  Spec("test","MC10_TwoPhaseStr.tla", inv =  Some("TCConsistent")),
  Spec("test","MC10_TwoPhaseInt.tla", inv =  Some("TCConsistent")),
)
