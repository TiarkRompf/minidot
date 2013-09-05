package dot

import java.io._
import org.scalatest.FunSuite
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class GenerateElf extends FunSuite with ElfPrinter with DotParsing {
  val overwrite = false
  val src = "src/test/dot/"
  val prefix = "src/main/elf/"
  def readFile(name: String): String = {
    try {
      val buf = new Array[Byte](new File(name).length().toInt)
      val fis = new FileInputStream(name)
      fis.read(buf)
      fis.close()
      new String(buf)
    } catch {
      case e: IOException => ""
    }
  }
  def writeFile(name: String, content: String) {
    val out = new java.io.PrintWriter(new File(name))
    out.write(content)
    out.close()
  }
  def check(label: String, code: String) = {
    val fileprefix = prefix+label
    val name = fileprefix+".check.elf"
    val aname = fileprefix+".actual.elf"
    val expected = readFile(name)
    if (expected != code) {
      val oname = if (overwrite) name else aname
      println((if (overwrite) "over" else "")+"writing " + oname)
      writeFile(oname, code)
    }
    assert(expected == code, name)
  }
  def exec(label: String, code: String) = {
    val fileprefix = prefix+label
    val aname = fileprefix+".actual.elf"
    writeFile(aname, code)
  }

  import scala.collection.JavaConversions._
  def getFileTree(f: File): Stream[File] = f #::
    (if (f.isDirectory) f.listFiles().toStream.flatMap(getFileTree) else Stream.empty)
  def srcTree = getFileTree(new File(src))

  for (f <- srcTree) {
    val name = f.getName
    if (name.endsWith(".dot")) {
      test("sanity-checking elf of "+name) {
        val in = readFile(f.toString)
        phrase(Parser.term)(new lexical.Scanner(in)) match {
          case Success(e, _) => check(name, "%abbrev "+name.substring(0, name.length-4)+" = "+print(e)+".")
          case r@_ => sys.error("error parsing " + name + r)
        }
      }
    }
  }
}
