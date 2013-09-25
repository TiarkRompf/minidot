package dot

import scala.text.Document
import scala.text.Document._

trait ElfPrinter { this: DotSyntax =>
  import terms._
  import types._
  import init._

  val VERSION = 5

  def collectTags(e: Any): List[Tag] = {
    def c(e: Any): List[Tag] = e match {
      case l@Tag(id) => List(l)
      case p: Product => p.productIterator.toList.flatMap(c)
      case _ => Nil
    }
    c(e).toSet.toList
  }

  def printEnvFromSize(n: Int, hints: Map[Int,String]): String = {
    if (n==0) "tnil" else {
      val sty = hints.get(n-1).getOrElse("_")
      s"(tcons $sty ${printEnvFromSize(n-1, hints)})"
    }
  }

  def printNat(n: Int): String = {
    assert(n>=0, "not a natural number")
    if (n==0) "z" else s"(s ${printNat(n-1)})"
  }

  def print(e: Entity): String = printEntity(collectTags(e), Map.empty, Map.empty, e)

  def printTypeMembers(tags: List[Tag], env: Map[Var,Int], hints: Map[Int,String], members: Map[Tag, InitType], rtags: List[Tag]): String = rtags match {
    case Nil => "mnil"
    case l::rtags =>
      val (tyS, tyU) = members.get(l) match {
        case None => (Bot, Top)
        case Some(i) => (i.d.tyS, i.d.tyU)
      }
      s"(mcons _ ${printEntity(tags, env, hints, tyS)} ${printEntity(tags, env, hints, tyU)} ${printTypeMembers(tags, env, hints, members, rtags)})"
  }

  def inferConstructorType(oself: Option[Var], members: List[Init]): Type = {
    def infer1(m: Init): Type = m.d
    def infer(ms: List[Init]): Type = ms match {
      case Nil => Top
      case m::Nil => infer1(m)
      case m::ms => And(infer1(m), infer(ms))
    }
    val ty = infer(members)
    oself match {
      case None => ty
      case Some(self) => TRec(self, ty)
    }
  }

  def printEntity(tags: List[Tag], env: Map[Var,Int], hints: Map[Int,String], e: Entity): String = {
    def p(e: Entity) = printEntity(tags, env, hints, e)
    def ebind(x: Var) = env.updated(x, env.size)
    def pbind(e: Entity, xs: Var*) = {
      var envp = env
      for (x <- xs) {
        envp = envp.updated(x, envp.size)
      }
      printEntity(tags, envp, hints, e)
    }
    def pbind_hint(e: Entity, x: Var, ty: Type): String = {
      val n = env.size
      val sty = p(ty)
      printEntity(tags, env.updated(x, n), hints.updated(n, sty), e)
    }

    e match {

      case l@Tag(id) => printNat(tags.size-tags.indexOf(l)-1)

      case v@Var(id) => env.get(v) match {
        case None => assert(false, "syntax error: unbound variable "+id); ???
        case Some(i) =>
          s"(var ${printNat(i)})"
      }

      case Sel(o, l) => s"(sel ${p(o)} ${p(l)})"

      case App(f, l, a) => s"(app ${p(f)} ${p(l)} ${p(a)})"

      case New(otc, oself, members) =>
        val self = oself.getOrElse(Var("_"))
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
        val tmem = if (typeMemberMap.isEmpty) "mnil" else printTypeMembers(tags, ebind(self), hints, typeMemberMap, tags)
        val dmem = defMembers match {
          case Nil => "z top empty top"
          case (_,i)::Nil => s"${p(i.d.tag)} ${pbind(i.d.tyP, self)} ${pbind(i.body, self, i.param)} ${pbind(i.d.tyR, self)}"
          case _ => assert(false, "TODO in elf: support object creation with more than one def"); ???
        }
        val vmem = valMembers match {
          case Nil => "z empty top"
          case (_,i)::Nil => s"${p(i.d.tag)} ${p(i.t)} ${pbind(i.d.ty, self)}"
          case _ => assert(false, "TODO in elf: support object creation with more than one val"); ???
        }
        val tc = otc.getOrElse(inferConstructorType(oself, (defMembers++valMembers++typeMembers).map(_._2))) match {
          case tc@TRec(_,_) => tc
          case tc => TShift(tc)
        }
        val stc = if (VERSION <= 4) "" else p(tc)
        s"(fun $stc $dmem $vmem $tmem)"

      case Let(x, tyx, ex, body) =>
        s"(let ${p(tyx)} ${p(ex)} ${pbind_hint(body, x, tyx)})"

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

      case Tsel(x, tag, hint) =>
        val ty = hint.getOrElse(Unknown)
        val sty = if (VERSION<=4) "" else p(ty)
        s"(tsel ${p(x)} $sty ${p(tag)})"

      case TRec(self, ty) =>
        s"(bind ${printNat(env.size)} ${printEnvFromSize(env.size, hints)} ${pbind(ty, self)})"

      case TShift(ty) =>
        pbind(ty, Var("_"))

      case SingletonType(v) =>
        env.get(v) match {
          case None => assert(false, "syntax error: unbound variable"); ???
          case Some(i) => hints.get(i) match {
            case None => assert(false, "syntax error: don't know singleton type"); ???
            case Some(sty) => sty
          }
        }
      case Unknown => "_"
    }
  }
}
