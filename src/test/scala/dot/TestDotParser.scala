package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestDotParser extends FunSuite with DotParsing {
  import terms._
  import types._
  import init._

  def parse[T](p: Parser[T])(in: String) = phrase(p)(new lexical.Scanner(in))

  def ok[T](p: Parser[T], expected: Option[T] = None)(in: String) = parse(p)(in) match {
    case Success(actual, _) => expected.foreach(e => expectResult(e)(actual))
    case _@r => fail("expected success, got " + r)
  }
  def bad[T](p: Parser[T], expectedMsg: Option[String] = None)(in: String) = parse(p)(in) match {
    case Failure(msg, _) => expectedMsg.foreach(e => expectResult(e)(msg))
    case _@r => fail("expected failure, got " + r)
  }

  test("Bot") { ok(Parser.typ)("Bot") }
  test("Top") { ok(Parser.typ)("Top") }

  test("And") { ok(Parser.typ)("Top & Top") }
  test("Or") { ok(Parser.typ)("Top | Top") }
  test("TypeGrouping1") { ok(Parser.typ, Some(Or(And(Top, Top), Top)))("Top & Top | Top") }
  test("TypeGrouping2") { ok(Parser.typ, Some(Or(Top, And(Top, Top))))("Top | Top & Top") }

  test("MemType") { ok(Parser.typ)("{ type A: Bot .. Top }") }
  test("MemDef") { ok(Parser.typ)("{ def m(_: Bot): Top }") }
  test("MemVal") { ok(Parser.typ)("{ val v: Top }") }
  test("TRec/Tsel") { ok(Parser.typ)("{ x => { type A: Bot .. x.B } & { type B: Bot .. Top } }") }

  test("termVar") { ok(Parser.term) ("val x = new { x => }; x") }
  test("termSel") { ok(Parser.term) ("val x = new { x => val v = x}; x.v") }
  test("termApp") { ok(Parser.term) ("val x = new { x => def m(a)=a}; x.m(x)") }
}
