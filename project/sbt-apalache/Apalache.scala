package systems.informal.sbt.apalache

import scala.sys.process.Process
import sbt._
import Keys._

object Apalache extends AutoPlugin {

  object Version {
    sealed abstract class T {
      def version: String
      override def toString: String = version
    }

    case class Branch(version: String) extends T
    case class Release(version: String) extends T

    def ofString: String => T = { s =>
      val version = s.substring(1)
      s.substring(0, 1) match {
        case "@" => Release(version)
        case "#" => Branch(version)
        case _ =>
          throw new RuntimeException(
            s"Invalid Apalache version '${s}': must start with '@' for tagged release version or '#' for git ref"
          )
      }
    }
  }

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

    lazy val apalacheEnableVersion =
      taskKey[String](
        "Set the current version of Apalache to `apalacheVersion`, returning its reported version"
      )
  }

  import autoImport._

  override lazy val globalSettings: Seq[Setting[_]] = Seq(
    apalacheVersion := "#main"
  )

  override lazy val projectSettings: Seq[Setting[_]] = Seq(
    apalacheDir := {
      val dir = (Compile / resourceManaged).value / "apalache"
      IO.createDirectory(dir)
      dir
    },
    apalacheExec := apalacheDir.value / "exec",
    apalacheFetch := apalacheFetchImpl.value,
    apalacheEnableVersion := apalacheEnableVersionImpl.value,
  )

  private def fetchByVersion(version: String, destdir: File) =
    s"curl --fail -L https://github.com/informalsystems/apalache/releases/download/${version}/apalache.tgz -o ${destdir}"

  private def fetchByBranch(branch: String, destdir: File) =
    s"git clone -b ${branch} --single-branch https://github.com/informalsystems/apalache.git ${destdir}"

  private def fetchBranch(destDir: File) =
    s"git -C ${destDir} pull"

  lazy val apalacheFetchImpl: Def.Initialize[Task[File]] = Def.task {
    val log = streams.value.log

    val version = Version.ofString(apalacheVersion.value)

    val destDir = apalacheDir.value / version.toString

    version match {
      case Version.Release(version) => {
        IO.createDirectory(destDir)
        val destTar = destDir / "apalache.tgz"
        log.info(s"Fetching Apalache release version ${version} to ${destDir}")
        Execute.succeed(Process(fetchByVersion(version, destTar)), log)
        log.info(s"Unpacking Apalache to ${destDir}")
        Execute.succeed(
          Process(s"tar zxvf ${destTar} --strip-components=1 -C ${destDir}"),
          log,
        )
      }
      case Version.Branch(version) => {
        if (destDir.exists()) {
          log.info(s"Updating Apalache branch ${version} in ${destDir}")
          Process(fetchBranch(destDir)) ! log
        } else {
          IO.createDirectory(destDir)
          log.info(s"Fetching Apalache branch ${version} to ${destDir}")
          Execute.succeed(Process(fetchByBranch(version, destDir)), log)
        }
        log.info("Building Apalache")
        Execute.succeed(Process(s"make -C ${destDir} package"), log)
      }
    }
    destDir
  }

  // TODO Do not recompile or fetch version if already cached
  lazy val apalacheEnableVersionImpl: Def.Initialize[Task[String]] = Def.task {
    val log = streams.value.log
    val executableDir = apalacheFetch.value
    val symlink = apalacheExec.value
    log.info(s"Symlinking ${symlink} -> ${executableDir}")
    val cmd = s"ln -sfn ${executableDir} ${symlink} "
    log.info(cmd)
    Execute.succeed(Process(cmd), log)

    val exec = symlink / "bin" / "apalache-mc"
    (Process(s"""${exec} version""") !! log).trim()
  }
}
