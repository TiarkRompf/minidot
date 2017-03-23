import leon.Annotations._
import leon.Utils._

object Test {
  
  sealed abstract class Type
  case object Nat extends Type
  case object Bot extends Type
  case object Top extends Type
  case class Arrow(arg: Type, res: Type) extends Type
  
  sealed abstract class Term
  case class Lit(x: Int) extends Term
  case class Var(x: Int) extends Term
  case class Lambda(x: Int, tx: Type, y: Term) extends Term
  case class App(x: Term, y: Term) extends Term
  
  sealed abstract class Value
  case class Const(x:Int) extends Value
  case class Closure(e:VEnv,x:Int,tx:Type,y:Term) extends Value
  
  sealed abstract class TEnv
  case object TNil extends TEnv
  case class TCons(x: Int, y: Type, tl: TEnv) extends TEnv
  
  sealed abstract class VEnv
  case object VNil extends VEnv
  case class VCons(x: Int, y: Value, tl: VEnv) extends VEnv

  sealed abstract class TOption
  case object TNone extends TOption
  case class TSome(x: Type) extends TOption
  
  sealed abstract class TEnvOption
  case object TEnvNone extends TEnvOption
  case class TEnvSome(x: TEnv) extends TEnvOption

  sealed abstract class VOption
  case object VNone extends VOption
  case class VSome(x: Value) extends VOption

  def isDef(x: TOption): Boolean = x match {
    case TSome(_) => true
    case _ => false
  }
  def isDef(x: TEnvOption): Boolean = x match {
    case TEnvSome(_) => true
    case _ => false
  }
  def isDef(x: VOption): Boolean = x match {
    case VSome(_) => true
    case _ => false
  }
  def get(x: TOption): Type = { require(isDef(x)); x match {
    case TSome(t) => t
  }}
  def get(x: TEnvOption): TEnv = { require(isDef(x)); x match {
    case TEnvSome(t) => t
  }}
  def get(x: VOption): Value = { require(isDef(x)); x match {
    case VSome(v) => v
  }}

  
  def tlookup(e: TEnv, x: Int): TOption = e match {
    case TCons(x1,t1,tail) => if (x == x1) TSome(t1) else tlookup(tail,x)
    case TNil => TNone
  }
  def vlookup(e: VEnv, x: Int): VOption = e match {
    case VCons(x1,t1,tail) => if (x == x1) VSome(t1) else vlookup(tail,x)
    case VNil => VNone
  }

  def typed(e: TEnv, x: Term): TOption = x match {
    case Lit(x) => TSome(Nat)
    case Var(x) => tlookup(e,x)
    case Lambda(x,tx,y) => typed(TCons(x,tx,e),y)
    case App(x,y) => (typed(e,x),typed(e,y)) match {
      case (TSome(Arrow(tx1,tx2)),TSome(ty)) if ty == tx1 => TSome(tx2)
      case _ => TNone
    }
  }
  
  def typedEnv(e: VEnv): TEnvOption = e match {
    case VCons(x1,v1,tl1) => 
      (typedEnv(tl1),typedVal(tl1,v1)) match {
        case (TEnvSome(tl2),TSome(t1)) => TEnvSome(TCons(x1,t1,tl2))
        case _ => TEnvNone
      }
    case VNil => TEnvSome(TNil)
  }

  def typedVal(e: VEnv, x: Value): TOption = x match {
    case Const(x) => TSome(Nat)
    case Closure(e,x,tx,y) => 
      typedEnv(e) match {
        case TEnvSome(g) =>
          typed(TCons(x,tx,g),y) match {
            case TSome(ty) => TSome(Arrow(tx,ty))
            case TNone => TNone
          }
        case TEnvNone => TNone
      }
  } //ensuring { r => x match { case Closure(e,x,tx,y) => get(typedEnv(e)) }}
  
  def eval0(e: VEnv, x: Term): VOption = {
    x match {
      case Lit(x) => VSome(Const(x))
      case Lambda(x,tx,y) => VSome(Closure(e,x,tx,y))
      case App(x,y) => 
        val v1 = eval0(e,x)
        val v2 = eval0(e,y)
        (v1,v2) match {
          case (VSome(Closure(e1,x1,tx,y1)),VSome(v2)) =>
            eval0(VCons(x1,v2,e1),y1)
          case _ => VNone
        }
      case Var(x) => vlookup(e,x)
    }
  } //ensuring { r => typedVal(e,r) == TSome(t) }

  def evalxs(e: VEnv, x: Term): VOption = {
    require(isDef(typed(get(typedEnv(e)),x)))
    eval0(e,x)
  } ensuring { r => 
    get(typed(get(typedEnv(e)),x)) == 
    get(typedVal(e,get(r))) //&&
    //closwf(e,get(r))
  }

  def evalxxs(e: VEnv, g: TEnv, x: Term, t: Type): VOption = {
    require(get(typed(g,x)) == t && get(typedEnv(e)) == g)
    eval0(e,x)
  } ensuring { r => 
    get(typedVal(e,get(r))) == t
  }



  def closwf(e: VEnv, x: Value): Boolean = {
    require(isDef(typedVal(e,x)))
    x match {
      case Closure(e1,x,tx,ty) => isDef(typedEnv(e1))
      case _ => true
    }
  }


  def evalx(e: VEnv, x: Term): VOption = {
    require(isDef(typed(get(typedEnv(e)),x)))
    //val r = eval0(e,x)
    x match {
      case Lit(x) => VSome(Const(x))
      case Lambda(x,tx,y) => VSome(Closure(e,x,tx,y))
      case App(x,y) => 
        val v1 = evalxs(e,x)
        val v2 = evalxs(e,y)
        (v1,v2) match {
          case (VSome(Closure(e1,x1,tx,y1)),VSome(v2)) =>
            VNone //evalxs(VCons(x1,v2,e1),y1)
          case _ => VNone
        }
      case Var(x) => vlookup(e,x)
    }    
  }
  

  /*def eval(e: VEnv, g: TEnv, x: Term, t: Type): Value = {
    require(typed(g,x) == TSome(t) && typedEnv(e) == TEnvSome(g))
    x match {
      case Lit(x) => Const(x)
      case Lambda(x,tx,y) => Closure(e,g,x,tx,y)
      case App(x,y) => 
        val TSome(Arrow(tx,ty)) = typed(g,x)
        val v1 = evalStub(e,g,x,Arrow(tx,t))
        val v2 = evalStub(e,g,y,tx)
        v1 match {
          case Closure(e1,g1,x1,tx,y1) => 
            evalStub(VCons(x1,v2,e1),TCons(x1,tx,g1),y1,t)
        }
      case Var(x) => vlookups(e,g,x,t)
    }
  } //ensuring { r => typedVal(e,r) == TSome(t) }*/
}
