package dot

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._
import util.parsing.combinator.{PackratParsers, ImplicitConversions}
import scala.util.parsing.input.Positional

trait DotParsing extends StdTokenParsers with PackratParsers with DotSyntax with ImplicitConversions with Debug {
  type Tokens = StdLexical; val lexical = new StdLexical {
    override def token: Parser[Token] = delim | super.token
  }
  lexical.delimiters ++= List("=", ";", ".", "(", ")", "{", "}", "=>", "⇒", ":", "..", "->", "→", "!", "&", "∧", "/\\", "|", "∨", "\\/", "⊥", "⊤")
  lexical.reserved ++= List("def", "val", "type", "new", "Top", "Bottom", "Bot")

  type P[T] = PackratParser[T]

  val debugParser: Boolean = false
  def debugParser(msg: String) { if (debugParser) super.debug(msg) }

  private var indent = ""
  def l[T <: Positional](p: => Parser[T])(name: String): P[T] = positioned(Parser{ in =>
    debugParser(indent + "trying " + name)
    val oldIndent = indent
    indent += " "
    val r = p(in)
    indent = oldIndent
    debugParser(indent + name + " --> " + r)
    r
  })

  def li[T <: Positional](t: String => T)(name: String): P[T] = l(ident.withFailureMessage(name + " expected") ^^ t) (name)

  import terms._
  import types._
  import init._

  trait DotParser {
    def suggest[T](parser: Parser[T], pred: T => Boolean, err: T => String): Parser[T] = Parser{ in =>
     parser(in) filterWithError(pred, err, in)
    }
    def only[T](parser: Parser[T], pred: T => Boolean, err: T => String): Parser[T] =
      parser.flatMap{r => if (pred(r)) success(r) else failure(err(r))}

    lazy val tag : P[Tag] = li(Tag) ("tag")
    lazy val name: P[Var] = li(Var) ("var")

    lazy val memDefVar: P[(MemDef, Var)] =
      "def" ~> tag ~ ("(" ~> name) ~ (optType <~ ")") ~ optType ^^
      { case m~x~tyR~tyP => (MemDef(m, tyR, tyP), x) }

    lazy val memDef: P[MemDef] =
      l(memDefVar ^^ { case (d,x) => d }) ("method member")

    lazy val initDef: P[InitDef] =
      l(memDefVar ~ ("=" ~> term) ^^
        { case (d,x)~t => InitDef(d, x, t) }) ("def init")

    lazy val memVal: P[MemVal] =
      l(("val" ~> tag ~ optType) ^^ MemVal) ("value member")

    lazy val initVal: P[InitVal] =
      l(memVal ~ ("=" ~> term) ^^ InitVal) ("val init")

    lazy val memType: P[MemType] =
      l(("type" ~> tag ~ (":" ~> typ <~ "..") ~ typ) ^^ MemType) ("type member") |
      l(("type" ~> tag ~ ("=" ~> typ)) ^^ {case l~ty => MemType(l, ty, ty)}) ("type member alias")

    lazy val initType: P[InitType] =
      l(memType ^^ InitType) ("type init")

    lazy val init1: P[Init] = initType | initVal | initDef

    lazy val init: P[List[Init]] =
      repsep(init1, opt(";"))

    lazy val newTerm: P[New] =
      l("new" ~> opt(typ) ~ ("(" ~> opt(name <~ ("=>" | "⇒"))) ~ init <~ ")" ^^ New) ("new object")

    lazy val letTerm: P[Let] =
      l(initVal ~ (opt(";") ~> term) ^^
        { case InitVal(MemVal(Tag(id), tyx), ex) ~ body =>
          Let(Var(id), tyx, ex, body) })("val binding")

    lazy val term: P[Term] =
      l(term ~ ("." ~> tag) ~ opt("(" ~> term <~ ")") ^^
        { case t1~tag~ot2 => ot2 match {
          case None => Sel(t1, tag)
          case Some(t2) => App(t1, tag, t2)
      }}) ("object selection") |
      newTerm |
      letTerm |
      name |
      l("(" ~> term <~ ")") ("parenthesized term")

    lazy val optType: P[Type] =
      l(opt(":" ~> typ) ^^ { ot => ot.getOrElse(Unknown) }) ("optional type")

    lazy val top: P[Type] =
      l(("Top" | "⊤") ^^^ Top ) ("top type")

    lazy val bot: P[Type] =
      l(("Bottom" | "Bot" | "⊥") ^^^ Bot) ("bottom type")

    lazy val intersection: P[Type] =
      l((typ1 ~ (("&" | "/\\" | "∧") ~> typ2)) ^^ And) ("intersection type")

    lazy val union: P[Type] =
      l((typ2 ~ (("|" | "\\/" | "∨") ~> typ3)) ^^ Or) ("union type")

    lazy val recType: P[Type] =
      l("{" ~> (name <~ ("=>" | "⇒")) ~ (typ <~ "}") ^^
        { case self~ty => TRec(self, ty) }
       ) ("recursive type")

    lazy val tsel: P[Type] =
      l((name ~ ("." ~> tag)) ^^ Tsel) ("type selection")

    lazy val structType: P[Type] =
      "{" ~> (memType | memVal | memDef) <~ "}"

    lazy val typ1: P[Type] =
      top |
      bot |
      recType |
      structType |
      tsel |
      l("(" ~> typ <~ ")") ("parenthesized type")

    lazy val typ2: P[Type] = intersection | typ1
    lazy val typ3: P[Type] = union | typ2
    lazy val typ: P[Type] = typ3
  }
  def Parser = new DotParser {}
}
