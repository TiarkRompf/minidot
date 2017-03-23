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
  case class Lambda(x: Int, t: Type, y: Term) extends Term
  case class App(x: Term, y: Term) extends Term

  sealed abstract class Value
  case class Const(x:Int) extends Value
  //case class Closure(e:VEnv,g:TEnv,x:Int,t:Type,y:Term) extends Value
  
  sealed abstract class TEnv
  case object TNil extends TEnv
  case class TCons(x: Int, y: Type, tl: TEnv) extends TEnv
  
  sealed abstract class VEnv
  case object VNil extends VEnv
  case class VCons(x: Int, y: Value, tl: VEnv) extends VEnv

  sealed abstract class TOpt
  case object TNone extends TOpt
  case class TSome(tl: Type) extends TOpt
  
  def tlookup(e: TEnv, x: Int): TOpt = e match {
    case TCons(x1,t1,tail) => if (x == x1) TSome(t1) else tlookup(tail,x)
    case TNil => TNone
  }

  sealed abstract class TypeDeriv
  case class TLit(e: TEnv, x: Term, t: Type) extends TypeDeriv
  case class TVar(e: TEnv, x: Term, t: Type) extends TypeDeriv
  case class TLam(e: TEnv, x: Term, t: Type, ty: TypeDeriv) extends TypeDeriv
  case class TApp(e: TEnv, x: Term, t: Type, tf: TypeDeriv, tx: TypeDeriv) extends TypeDeriv

  def get(td: TypeDeriv): (TEnv, Term, Type) = td match {
    case TLit(e1,x1,t1) => (e1,x1,t1)
    case TVar(e1,x1,t1) => (e1,x1,t1)
    case TLam(e1,x1,t1,_) => (e1,x1,t1)
    case TApp(e1,x1,t1,_,_) => (e1,x1,t1)
  }

  def typeDeriv(d: TypeDeriv): Boolean = d match {
    case TLit(e1,Lit(x),Nat) => true
    case TVar(e1,Var(x),t) => tlookup(e1,x) == TSome(t)
    case TLam(e1,Lambda(x1,t1,y),Arrow(t2,ty),td) if t1 == t2 => 
      typeDeriv(td) && get(td) == (TCons(x1,t1,e1), y, ty)
    case TApp(e1,App(f,x),ty,tdf,tdx) => 
      typeDeriv(tdf) && typeDeriv(tdx) && 
        get(tdf) == (e1,f,Arrow(get(tdx)._3,ty)) &&
        get(tdx)._1 == e1 && get(tdx)._2 == x
    case _ => false
  }

  def typeDerivX(d: TypeDeriv, g: TEnv, x: Term, t: Type): Boolean = 
    typeDeriv(d) && get(d) == (g,x,t)

  case class Closure(e:VEnv,g:TEnv,td:TypeDeriv,x:Int,t:Type,y:Term) extends Value



  def typed(e: TEnv, x: Term): TOpt = x match {
    case Lit(x) => TSome(Nat)
    case Var(x) => tlookup(e,x)
    case Lambda(x,t,y) => 
      typed(TCons(x,t,e),y) match { 
        case TSome(ty) => TSome(Arrow(t,ty))
        case x => x
      }
    case App(x,y) => 
      (typed(e,x), typed(e,y)) match {
        case (TSome(Arrow(tx,ty)), TSome(tx1)) if tx == tx1 => TSome(ty)
        case _ => TNone
      }
  }
  
  
  def typedEnv(e: VEnv, g: TEnv): Boolean = (e,g) match {
    case (VCons(x1,v1,tl1),TCons(x2,t1,tl2)) if x1 == x2 => 
      typedVal(tl1,v1,t1) && typedEnv(tl1,tl2)
    case (VNil, TNil) => true
    case _ => false
  }
  
  def typedVal(e: VEnv, x: Value, t: Type): Boolean = (x,t) match {
    case (Const(x),Nat) => true
    case (Closure(e,g,td,x,tx,y), Arrow(t1,t2)) => 
      typeDerivX(td,g,y,t2) && t1 == tx
    case _ => false
  }
  
  def vlookup(e: VEnv, g: TEnv, x: Int, t: Type): Value = {
    require(typedEnv(e,g) && tlookup(g,x) == TSome(t))
    (e,g) match {
      case (VCons(x1,v1,tail), TCons(_,_,ttl)) => if (x == x1) v1 else vlookup(tail,ttl,x,t)
    }
  } ensuring { r => typedVal(e,r,t) }

  
  def eval0(e: VEnv, g: TEnv, x: Term, t: Type, td: TypeDeriv): Value = {
    require(typeDerivX(td,g,x,t) && typedEnv(e,g))
    Const(9)
  } ensuring { r => typedVal(e,r,t) }


  def eval(e: VEnv, g: TEnv, x: Term, t: Type, td: TypeDeriv): Value = {
    require(typeDerivX(td,g,x,t) && typedEnv(e,g))
    x match {
      case Lit(x) => Const(x)
      case Lambda(x,t,y) => Closure(e,g,td,x,t,y)
      case App(f,x) => 
        td match {
          //case TVar(_,_,_) => Const(7)
          case TApp(_,_,ty,tdf,tdx) =>
            val (_,_,Arrow(tx,ty)) = get(tdf)
            val v1 = eval(e,g,f,Arrow(tx,ty),tdf)
            val v2 = eval(e,g,x,tx,tdx)
            v1 match { case Closure(e1,g1,td1,x1,ty1,y1) =>
              eval(VCons(x1,v2,e1),TCons(x1,tx,g1),y1,ty1,td1)
            }
        }
      case Var(x) => vlookup(e,g,x,t)
    }
  } //ensuring { r => typedVal(e,r,t) }


}
