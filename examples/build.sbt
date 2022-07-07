import BenchExecDsl._
import ProjectUtils._

enablePlugins(BenchExec)

benchmarks ++= Seq(
  suiteGen("005examples-apalache", examplesSpecs)
)

lazy val examplesSpecs = Seq(
  Spec("2PCwithBTM", "MC4_FALSE_FALSE.tla", inv = "Consistency"),
  Spec("2PCwithBTM", "MC4_TRUE_TRUE.tla", inv = "Consistency"),
  Spec("2PCwithBTM", "MC10_FALSE_FALSE.tla", inv = "Consistency"),
  Spec("2PCwithBTM", "MC10_TRUE_TRUE.tla", inv = "Consistency"),
  Spec("2PCwithBTM", "MC20_FALSE_FALSE.tla", inv = "Consistency"),
  Spec("2PCwithBTM", "MC20_TRUE_TRUE.tla", inv = "Consistency"),
  Spec("aba_asyn_byz", "MC4.tla"),
  Spec("aba_asyn_byz", "MC10.tla"),
  Spec("aba_asyn_byz", "MC20.tla"),
  Spec("bakery", "MC3.tla", inv = "MutualExclusion"),
  Spec("bakery", "MC3.tla", length = 0, inv = "Inv"),
  Spec("bakery", "MC3.tla", length = 1, init = "Inv", inv = "Inv"),
  Spec("changRoberts", "MC4.tla", inv = "Correctness"),
  Spec("changRoberts", "MC10.tla", inv = "Correctness"),
  Spec("changRoberts", "MC20.tla", inv = "Correctness"),
  Spec("paxos", "MC3.tla", length = 13, inv = "V!OneValuePerBallot"),
  Spec("readersWriters", "MC4.tla", inv = "Safety"),
  Spec("readersWriters", "MC10.tla", inv = "Safety"),
  Spec("readersWriters", "MC20.tla", inv = "Safety")
)
