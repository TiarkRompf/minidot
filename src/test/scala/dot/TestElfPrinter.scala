package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestElfPrinter extends FunSuite with ElfPrinter with DotParsing {
  import terms._
  import types._
  import init._

  def ok[U](f: Term => U)(in: String)(expected: U) = phrase(Parser.term)(new lexical.Scanner(in)) match {
    case Success(t, _) => expectResult(expected)(f(t))
    case r@_ => sys.error("parsing failed: " + r)
  }

  def tags(ls: String*) = ls.toList.map(Tag)

  test("collectTags1") {
    ok(collectTags){"""
      val x = new ( x => type Bar: Bot .. x.Foo ); x
    """}(tags("Bar", "Foo"))
  }

  test("collectTags2") {
    ok(collectTags){"""
      val x = new ( x => def m(y): x.Bar = y; type Foo: Bot .. Top ); x.yo
    """}(tags("m", "Bar", "Foo", "yo"))
  }

  test("collectTagsNoDups") {
    ok(collectTags){"""
      val x = new ( x => def m(y): x.Bar = y; type Foo: Bot .. x.Bar ); x.yo
    """}(tags("m", "Bar", "Foo", "yo"))
  }

  test("printNat") {
    expectResult("(s (s (s z)))"){printNat(3)}
  }
}
