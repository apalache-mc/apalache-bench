import BenchExecDsl._

enablePlugins(BenchExec)

benchmarks += {
  def checkCmd(enc: String, len: Int) = {
    Cmd(
      s"length:${len}",
      Opt("check"),
      Opt("--init", "Init"),
      Opt("--inv", "Inv"),
      Opt("--next", "Next"),
      Opt("--smt-encoding", enc),
      Opt("--length", len),
      Opt("--cinit", s"CInit$len"),
    )
  }
  val files = Seq("array-encoding/SetAdd.tla")
  // TODO: Set to 14
  val lengths = 0.to(4, 2)
  Bench.Suite(
    name = "010encoding-SetAdd",
    // TODO Refactor with function to abstract over runs, just changing encoding
    runs = Seq(
      Bench.Runs(
        "Array",
        timelimit = "2h",
        tasks = Seq(Tasks("SetAdd", files)),
        cmds = lengths.map(checkCmd("arrays", _)),
      ),
      Bench.Runs(
        "OOPSLA19",
        timelimit = "2h",
        tasks = Seq(Tasks("SetAdd", files)),
        cmds = lengths.map(checkCmd("oopsla19", _)),
      ),
    ),
  )
}
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
