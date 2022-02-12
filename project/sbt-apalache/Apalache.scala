package system.informal.sbt.apalache

import scala.sys.process.Process
import sbt._
import Keys._

object Apalache extends AutoPlugin {
  object autoImport {
    lazy val apalacheVersion =
      settingKey[String](
        "The version (@v1.2.3) or branch (#branchname) of Apalache to use"
      )

    lazy val apalacheDir = taskKey[File](
      "The managed resource location where aplache binaries are saved"
    )

    lazy val apalacheExec = taskKey[File](
      "The managed symbolic link to the active Apalache binary"
    )

    lazy val apalacheFetch = taskKey[File](
      "Fetch the `apalacheVersion` of apalache, returning the directory for the binary"
    )

    lazy val useApalache =
      taskKey[Unit]("Add the fetched apalache binary to the head of the path")

    lazy val apalacheSetVersion =
      taskKey[Unit]("Set the current version of apalache to `apalacheVersion`")
  }

  import autoImport._

  override lazy val globalSettings: Seq[Setting[_]] = Seq(
    apalacheVersion := "#unstable"
  )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    apalacheDir := {
      val dir = (Compile / resourceManaged).value / "apalache"
      IO.createDirectory(dir)
      dir
    },
    apalacheExec := apalacheDir.value / "exec",
    apalacheFetch := apalacheFetchImpl.value,
    apalacheSetVersion := apalacheSetVersionImpl.value,
  )

  private def fetchByVersion(version: String, destdir: File) =
    s"curl --fail -L https://github.com/informalsystems/apalache/releases/download/v${version}/apalache.tgz -o ${destdir}"

  private def fetchByBranch(branch: String, destdir: File) =
    s"git clone -b ${branch} --single-branch https://github.com/informalsystems/apalache.git ${destdir}"

  lazy val apalacheFetchImpl: Def.Initialize[Task[File]] = Def.task {
    val log = streams.value.log

    val glyph = apalacheVersion.value.substring(0, 1)
    val version = apalacheVersion.value.substring(1)
    val destDir = apalacheDir.value / version

    glyph match {
      case "@" => {
        IO.createDirectory(destDir)
        val destTar = destDir / "apalache.tgz"
        log.info(s"Fetching Apalache release version ${version} to ${destDir}")
        Process(fetchByVersion(version, destTar)) ! log
        log.info(s"Unpacking Apalache to ${destDir}")
        Process(s"tar zxvf ${destTar} -C ${destDir}") ! log
        destDir
      }
      case "#" => {
        IO.createDirectory(destDir)
        log.info(s"Fetching Apalache branch ${version} to ${destDir}")
        Process(fetchByBranch(version, destDir)) ! log
        log.info("Building Apalache")
        Process(s"make -C ${destDir} package") ! log
        destDir
      }
      case _ => {
        throw new RuntimeException(
          s"Invalid Apalache version '${apalacheVersion.value}'. Must start with '@' if version tag or '#' if branch/commit ref"
        )
      }
    }
  }

  lazy val apalacheSetVersionImpl: Def.Initialize[Task[Unit]] = Def.task {
    val log = streams.value.log
    log.info(s"Symlinking ${apalacheExec.value} -> ${apalacheFetch.value}")
    val cmd = s"ln -sfn ${apalacheFetch.value} ${apalacheExec.value} "
    log.info(cmd)
    Process(cmd) ! log
  }
}
