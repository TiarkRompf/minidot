package dot

import scala.text.Document
import scala.text.Document._

trait ElfPrinter { this: DotSyntax =>
  import terms._
  import types._
  import init._

  def collectTags(e: Any): List[Tag] = {
    def c(e: Any): List[Tag] = e match {
      case l@Tag(id) => List(l)
      case p: Product => p.productIterator.toList.flatMap(c)
      case _ => Nil
    }
    c(e).toSet.toList
  }

  def printNat(n: Int): String = {
    assert(n>=0, "not a natural number")
    if (n==0) "z" else s"(s ${printNat(n-1)})"
  }

  def print(e: Entity): String = printEntity(collectTags(e), Map.empty, e)

  def printTypeMembers(tags: List[Tag], env: Map[Var,Int], members: Map[Tag, InitType], rtags: List[Tag]): String = rtags match {
    case Nil => "mnil"
    case l::rtags =>
      val (tyS, tyU) = members.get(l) match {
        case None => (Unknown, Unknown)
        case Some(i) => (i.d.tyS, i.d.tyU)
      }
      s"(mcons _ ${printEntity(tags, env, tyS)} ${printEntity(tags, env, tyU)} ${printTypeMembers(tags, env, members, rtags)})"
  }

  def printEntity(tags: List[Tag], env: Map[Var,Int], e: Entity): String = {
    def p(e: Entity) = printEntity(tags, env, e)
    def pbind(x: Var, e: Entity) = printEntity(tags, env.updated(x, env.size), e)
    e match {

      case l@Tag(id) => printNat(tags.size-tags.indexOf(l)-1)

      case v@Var(id) => env.get(v) match {
        case None => assert(false, "syntax error: unbound variable"); ???
        case Some(i) =>
          s"(var ${printNat(env.size-i)})"
      }

      case Sel(o, l) => s"(sel ${p(o)} ${p(l)})"

      case App(f, l, a) => s"(app ${p(f)} ${p(l)} ${p(a)})"

      case New(oself, members) =>
        assert(oself.isEmpty,
             "TODO in elf: support recursive object creation.")
        val typeMembers = members.collect{
          case i: InitType => (i.d.tag, i)
        }
        val typeMemberMap =typeMembers.toMap
        assert(typeMemberMap.size==typeMembers.size,
               "syntax error: duplicate type member")
        val defMembers = members.collect{
          case i: InitDef => (i.d.tag, i)
        }
        val valMembers = members.collect{
          case i: InitVal => (i.d.tag, i)
        }
        val tmem = if (typeMemberMap.isEmpty) "mnil" else printTypeMembers(tags, env, typeMemberMap, tags)
        val dmem = defMembers match {
          case Nil => "z _ empty _"
          case (_,i)::Nil => s"${p(i.d.tag)} ${p(i.d.tyP)} ${pbind(i.param, i.body)} ${p(i.d.tyR)}"
          case _ => assert(false, "TODO in elf: support object creation with more than one def"); ???
        }
        val vmem = valMembers match {
          case Nil => "z empty _"
          case (_,i)::Nil => s"${p(i.d.tag)} ${p(i.t)} ${p(i.d.ty)}"
          case _ => assert(false, "TODO in elf: support object creation with more than one val"); ???
        }
        s"(fun $dmem $vmem $tmem)"

      case Let(x, tyx, ex, body) =>
        s"(let ${p(tyx)} ${p(ex)} ${pbind(x, body)})"

      case Bot => "bot"

      case Top => "top"

      case And(ty1, ty2) =>
        s"(and ${p(ty1)} ${p(ty2)})"

      case Or(ty1, ty2) =>
        assert(false, "TODO in elf: support for unions")
        s"(or ${p(ty1)} ${p(ty2)})"

      case MemType(l, tyS, tyU) =>
        s"(rect ${p(l)} ${p(tyS)} ${p(tyU)})"

      case MemDef(l, tyP, tyR) =>
        s"(arrow ${p(l)} ${p(tyP)} ${p(tyR)})"

      case MemVal(l, ty) =>
        s"(recv ${p(l)} ${p(ty)})"

      case Tsel(x, tag) =>
        s"(tsel ${p(x)} ${p(tag)})"

      case TRec(self, ty) =>
        // TODO: fill env syntactically?
        //    -- at least, we can fix its size...
        s"(bind ${printNat(env.size+1)} _ ${pbind(self, ty)})"

      case Unknown => "_"
    }
  }
}
