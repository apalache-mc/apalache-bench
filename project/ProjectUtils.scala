/** Utilities */
object ProjectUtils {

  /** Abstracts over the parameters that vary between the various specs */
  case class Spec(
    folder: String,
    file: String,
    length: Int = 10,
    init: String = "Init",
    inv: String = "")

  /** Abstracts over the parameters that vary between the various commands */
  case class CmdPar(
    init: String,
    inv: String,
    length: Int,
    encoding: String,
    searchInvMode: String,
    discardDisabled: String)

}
