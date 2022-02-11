package system.informal.sbt.apalache

import scala.sys.process.Process
import sbt._
import Keys._

object Apalache extends AutoPlugin {
  object autoImport {
    lazy val apalacheVersion =
      settingKey[String]("The version (as a tag) or branch of apalache to use")

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
    apalacheVersion := "v0.20.2"
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
    s"curl --fail -L https://github.com/informalsystems/apalache/releases/download/${version}/apalache.tgz -o ${destdir}"

  lazy val apalacheFetchImpl: Def.Initialize[Task[File]] = Def.task {
    val log = streams.value.log
    val version = apalacheVersion.value
    val destDir = apalacheDir.value / version
    val destTar = destDir / "apalache.tgz"
    IO.createDirectory(destDir)
    if (version.startsWith("v")) {
      log.info(s"Fetching Apalache by version tag to ${destTar}")
      Process(fetchByVersion(version, destTar)) ! log
      log.info(s"Unpacking Apalache to ${destDir}")
      Process(s"tar zxvf ${destTar} -C ${destDir}") ! log
    }
    destDir
  }

  lazy val apalacheSetVersionImpl: Def.Initialize[Task[Unit]] = Def.task {
    val log = streams.value.log
    log.info(s"Symlinking ${apalacheExec.value} -> ${apalacheFetch.value}")
    val cmd = s"ln -sfn ${apalacheFetch.value} ${apalacheExec.value} "
    log.info(cmd)
    Process(cmd) ! log
  }
}
