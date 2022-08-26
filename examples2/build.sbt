import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("006examples2-apalache", examplesSpecs, cmdParsDefault)
)

lazy val examplesSpecs = Seq(
  //Spec("specs", "EgalitarianPaxos.tla", cInit = Some("ConstInit")),
  Spec("tendermint", "MC_n4_f1.tla", length = 1, init = "TypedInv", cInit = Some("ConstInit"), inv = Some("TypedInv"))
)
