import BenchExecDsl._

enablePlugins(BenchExec)

lazy val setAddSuite = {
  val specs = Seq("array-encoding/SetAdd.tla")
  // TODO: Set to 14
  val maxLengh = 4
  def checkCmd(encoding: String, length: Int) = {
    Cmd(
      s"${encoding}:length:${length}",
      Opt("check"),
      Opt("--init", "Init"),
      Opt("--inv", "Inv"),
      Opt("--next", "Next"),
      Opt("--smt-encoding", encoding),
      Opt("--length", length),
      Opt("--cinit", s"CInit${length}"),
    )
  }

  def runsForEncoding(encoding: String) = {
    val lengths = 0.to(maxLengh, 2)
    Bench.Runs(
      encoding,
      timelimit = "2h",
      tasks = Seq(Tasks(s"SetAdd", specs)),
      cmds = lengths.map(checkCmd(encoding, _)),
    )
  }

  Bench.Suite(
    name = "010encoding-SetAdd",
    runs = Seq(
      runsForEncoding("arrays"),
      runsForEncoding("oopsla19"),
    ),
  )

}

benchmarks ++= Seq(setAddSuite)

// benchmarks +=
//   Bench.Suite(
//     name = "001indinv-apalache",
//     runs = Seq(
//       // Bench.Runs(
//       //   "APABakery",
//       //   timelimit = "1h",
//       //   cmds = Seq(
//       //     Cmd(
//       //       "init with Init",
//       //       Opt("check"),
//       //       Opt("--init", "Init"),
//       //       Opt("--inv", "Inv"),
//       //       Opt("--length", 0),
//       //     ),
//       //     Cmd(
//       //       "init with Inv",
//       //       Opt("check"),
//       //       Opt("--init", "Inv"),
//       //       Opt("--inv", "Inv"),
//       //       Opt("--length", 1),
//       //     ),
//       //   ),
//       //   tasks = Seq(Tasks("APABakery", "Bakery-Boulangerie/APABakery.tla")),
//       // ),
//       // Bench.Runs(
//       //   "APAEWD840",
//       //   timelimit = "3h",
//       //   cmds = Seq(
//       //     Cmd(
//       //       "without init",
//       //       Opt("check"),
//       //       Opt("--inv", "InvAndTypeOK"),
//       //       Opt("--length", 0),
//       //       Opt("--cinit", "ConstInit10"),
//       //     ),
//       //     Cmd(
//       //       "with init",
//       //       Opt("check"),
//       //       Opt("--init", "InvAndTypeOK"),
//       //       Opt("--inv", "InvAndTypeOK"),
//       //       Opt("--length", 1),
//       //       Opt("--cinit", "ConstInit10"),
//       //     ),
//       //   ),
//       //   tasks = Seq(Tasks("APAEWD840.tla", "ewd840/APAEWD840.tla")),
//       // ),
//       Bench.Runs(
//         "APAbcastByz",
//         timelimit = "3h",
//         cmds = Seq(
//           Cmd(
//             "init with InitNoBcast",
//             Opt("check"),
//             Opt("--init", "IndInv_Unforg_NoBcast"),
//             Opt("--inv", "InitNoBcast"),
//             Opt("--length", 0),
//             Opt("--cinit", "ConstInit4"),
//           ),
//           Cmd(
//             "with init IndInv_Unforg_NoBcast",
//             Opt("check"),
//             Opt("--init", "IndInv_Unforg_NoBcast"),
//             Opt("--inv", "IndInv_Unforg_NoBcast"),
//             Opt("--length", 1),
//             Opt("--cinit", "ConstInit4"),
//           ),
//         ),
//         tasks =
//           Seq(Tasks("APAbcastByz.tla", Seq("bcastByz/APAbcastByz.tla"))),
//       ),
//       Bench.Runs(
//         "APATwoPhase",
//         timelimit = "23h",
//         cmds = Seq(
//           Cmd(
//             "no init",
//             Opt("check"),
//             Opt("--inv", "Inv"),
//             Opt("--length", 0),
//             Opt("--cinit", "ConstInit7"),
//           ),
//           Cmd(
//             "init with InitInv",
//             Opt("check"),
//             Opt("--init", "InitInv"),
//             Opt("--inv", "Inv"),
//             Opt("--length", 1),
//             Opt("--cinit", "ConstInit7"),
//           ),
//         ),
//         tasks =
//           Seq(Tasks("APATwoPhase.tla", Seq("two-phase/APATwoPhase.tla"))),
//       ),
//     ),
//   ),
