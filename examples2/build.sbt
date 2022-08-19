import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("006examples2-apalache", examplesSpecs, cmdParsDefault)
)

lazy val examplesSpecs = Seq(
  Spec("specs", "EgalitarianPaxos.tla", cInit = Some("ConstInit"))
)
