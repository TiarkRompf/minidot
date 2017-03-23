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
  case class Lambda(x: Int, y: Term) extends Term
  case class App(x: Term, tx: Type, y: Term) extends Term
  
  sealed abstract class Value
  case class Const(x:Int) extends Value
  case class Closure(e:VEnv,g:TEnv,x:Int,y:Term) extends Value
  
  sealed abstract class TEnv
  case object TNil extends TEnv
  case class TCons(x: Int, y: Type, tl: TEnv) extends TEnv
  
  sealed abstract class VEnv
  case object VNil extends VEnv
  case class VCons(x: Int, y: Value, tl: VEnv) extends VEnv

  // -----

  def subtp(t1: Type, t2: Type): Boolean = (t1,t2) match {
    case (Bot,_) => true
    case (_,Top) => true
    case (Nat,Nat) => true
    case (Arrow(t11,t12),Arrow(t21,t22)) => subtp(t21,t11) && subtp(t12,t22)
    case _ => false
  }

/* Viktor says: connect it using '&&' :
def property(....) {
 proof_hint &&
 claim
} holds
*/


  def subtpRefl(t1: Type): Boolean = {
    t1 match {
      case Arrow(t11,t12) => subtpRefl(t11) && subtpRefl(t12)
      case _ => true
    }
    subtp(t1,t1)
  } holds

  def subtpTrans(t1: Type, t2: Type, t3: Type): Boolean = {
    require(subtp(t1,t2) && subtp(t2,t3))
    (t1,t2,t3) match {
      case (Arrow(t11,t12),Arrow(t21,t22),Arrow(t31,t32)) => 
        subtpTrans(t31,t21,t11) && subtpTrans(t12,t22,t32)
      case _ => true
    }
    subtp(t1,t3)
  } holds


  // -----
  
  def tlookup(e: TEnv, x: Int, t: Type): Boolean = e match {
    case TCons(x1,t1,tail) => if (x == x1) t == t1 else tlookup(tail,x,t)
    case TNil => false
  }

  def typed(e: TEnv, x: Term, t: Type): Boolean = x match {
    case Lit(x) => t == Nat
    case Var(x) => tlookup(e,x,t)
    case Lambda(x,y) => 
      t match { 
        case Arrow(tx,ty) => typed(TCons(x,tx,e),y,ty) 
        case _ => false
      }
    case App(x,tx,y) => typed(e,x,Arrow(tx,t)) && typed(e,y,tx)
  }
  
  def typedEnv(e: VEnv, g: TEnv): Boolean = (e,g) match {
    case (VCons(x1,v1,tl1), TCons(x2,t2,tl2)) => 
      x1 == x2 && typedVal(tl1,v1,t2) && typedEnv(tl1,tl2)
    case (VNil,TNil) => true
    case _ => false
  }
  
  def typedVal(e: VEnv, x: Value, t: Type): Boolean = x match {
    case Const(x) => t == Nat
    case Closure(e,g,x,y) => (t match {
      case Arrow(tx,ty) => typed(TCons(x,tx,g),y,ty)
      case _ => false
    }) && typedEnv(e,g)
  }
  
  def vlookup(e: VEnv, g: TEnv, x: Int, t: Type): Value = {
    require(typedEnv(e,g) && tlookup(g,x,t))
    (e,g) match {
      case (VCons(x1,v1,tail), TCons(_,_,ttl)) => if (x == x1) v1 else vlookup(tail,ttl,x,t)
    }
  } ensuring { r => typedVal(e,r,t) }

  def eval(e: VEnv, g: TEnv, x: Term, t: Type): Value = {
    require(typed(g,x,t) && typedEnv(e,g))
    x match {
      case Lit(x) => Const(x)
      case Lambda(x,y) => Closure(e,g,x,y)
      case App(x,tx,y) => 
        val v1 = eval(e,g,x,Arrow(tx,t))
        val v2 = eval(e,g,y,tx)
        v1 match {
          case Closure(e1,g1,x1,y1) => 
            eval(VCons(x1,v2,e1),TCons(x1,tx,g1),y1,t)
        }
      case Var(x) => vlookup(e,g,x,t)
    }
  } ensuring { r => typedVal(e,r,t) }
}
