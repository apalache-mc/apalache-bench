package systems.informal.sbt.benchexec

import sbt._

/** XML Utilties */
object BenchExecXml {

  /** DocType's used for BenchExec XML */
  object DocType {

    /** The HTML doctype */
    val html =
      xml.dtd.DocType("html", xml.dtd.SystemID("about:legacy-compat"), Nil)

    /** The doctype for benchexc benchmark definition files
      *
      * See
      * https://github.com/sosy-lab/benchexec/blob/bbf9bc961023b1ccbf4d4645db14b7c8af006456/doc/benchmark.xml
      */
    val benchmark = xml.dtd.DocType(
      "benchmark",
      xml.dtd.PublicID(
        "+//IDN sosy-lab.org//DTD BenchExec benchmark 1.18//EN",
        "https://www.sosy-lab.org/benchexec/benchmark-1.18.dtd",
      ),
      Nil,
    )

    /** The doctype for benchexc table-generator configuration files
      *
      * See
      * https://github.com/sosy-lab/benchexec/blob/bbf9bc961023b1ccbf4d4645db14b7c8af006456/doc/table-generator.xml
      */
    val tableGenerator = xml.dtd.DocType(
      "table",
      xml.dtd.PublicID(
        "+//IDN sosy-lab.org//DTD BenchExec table 1.10//EN",
        "https://www.sosy-lab.org/benchexec/table-1.10.dtd",
      ),
      Nil,
    )
  }

  /** Save pretty-printed xml to a file
    *
    * @param file
    *   the file inwhich to write the XML content
    * @param doctype
    *   the XML doctype to use in the file
    * @param content
    *   the XML content to write to the file
    */
  def save(file: File, doctype: xml.dtd.DocType, content: xml.Elem): Unit = {
    val pp = new xml.PrettyPrinter(100, 2)
    val formatted = pp.format(content)
    IO.writer(file, "", charset = IO.defaultCharset) { w =>
      // First write the encoding and doctype
      xml.XML.write(
        w,
        xml.Text(""),
        "UTF-8",
        xmlDecl = true,
        doctype = doctype,
      )
      w.append(
        "<!-- NOTE: This file is generated. Edit the build.sbt instead. -->\n"
      )
      // Then write the pretty printed XML payload
      w.append(formatted)
    }
  }
}
