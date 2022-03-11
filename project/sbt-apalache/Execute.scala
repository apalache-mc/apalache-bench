package systems.informal.sbt.apalache

import scala.sys.process.{Process, ProcessBuilder, ProcessLogger}
import sbt._

/** Utilities for running externa processes
  */
object Execute {
  class ExecutionError(msg: String) extends RuntimeException(msg)

  def succeed(cmd: Seq[String], logger: ProcessLogger): Unit = {
    succeed(Process(cmd), logger)
  }
  // Fail hard if process doesn't return 0
  def succeed(cmd: String, logger: ProcessLogger): Unit = {
    succeed(Process(cmd), logger)
  }

  def succeed(cmd: ProcessBuilder, logger: ProcessLogger): Unit = {
    cmd ! logger match {
      case 0 => ()
      case c =>
        throw new ExecutionError(
          s"Execution of ${cmd} failed with return code $c"
        )
    }
  }
}
