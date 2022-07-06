/** Utilities used in the "examples" project */
object ExamplesProjectUtils {

  /** Abstracts over the parameters that vary between the various specs */
  case class Spec(
      folder: String,
      file: String,
      length: Int,
      init: String = "Inv",
      inv: String = "Inv")

}
