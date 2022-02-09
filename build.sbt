import org.apache.commons.io.FileUtils
import java.text.SimpleDateFormat
import scala.sys.process.Process
import java.util.Date
import org.apache.commons.io.FilenameUtils

ThisBuild / version := "0.0.1"
ThisBuild / sbtVersion := "1.6.1"
ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "systems.informal"

import BenchExecDsl._

lazy val performance = (project in file("performance"))
  .settings(
    benchmarks += {
      val length = Seq(2, 10, 15, 20, 30)
      val cmds = length.map(n =>
        Cmd(
          s"length ${n}",
          Opt("check"),
          Opt("--inv", "Inv"),
          Opt("--length", n),
        )
      )
      Benchmark(
        "testing-benchmark",
        cmds,
        tasks = Seq(
          Tasks("prisoners", "Prisoners/APAPrisoners.tla"),
          Tasks("counter", "Counter.tla"),
        ),
      )
    }
  )
