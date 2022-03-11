import org.apache.commons.io.FileUtils
import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.FilenameUtils

description := "The Apalache Benchmarking System"
name := "apalache-bench"
organizationHomepage := Some(url("https://apalache.informal.systems/"))

ThisBuild / version := "0.0.1"
ThisBuild / sbtVersion := "1.6.1"
ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "systems.informal"
import BenchExecDsl._

ThisBuild / apalacheVersion := "#unstable"
ThisBuild / benchmarksToolVersion := apalacheEnableVersion.value

lazy val root = (project in file("."))
  .enablePlugins(Apalache)
  .aggregate(
    // Should aggregate every project that can run reports
    performance
  )

// Configure GH pages site
enablePlugins(GhpagesPlugin)
git.remoteRepo := "git@github.com:informalsystems/apalache-bench.git"
ghpagesNoJekyll := true

lazy val site = (project in file("src/site"))
  .enablePlugins(BenchExec)
  .settings(
    // Versions to include in the reports of performance accross versions
    benchmarksLongitudinalVersions := Set(
      "0.22.0",
      "0.22.1",
      "0.22.2",
      "v0.22.1-151-g3834a20d",
    ),
    benchmarksIndexFile := Some(baseDirectory.value / "index.html"),
  )

lazy val performance = (project in file("performance"))
  .enablePlugins(BenchExec)
  .settings(
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
  )
