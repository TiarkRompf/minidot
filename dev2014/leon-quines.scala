object Test {
    
  sealed abstract class Term
  case class Lit(x: Int) extends Term
  case class Var(x: Int) extends Term
  case class Lambda(x: Int, y: Term) extends Term
  case class App(x: Term, y: Term) extends Term
  case object Quote extends Term
  case class MkApp(x: Term, y: Term) extends Term

  sealed abstract class Value
  case class Const(x:Int) extends Value
  case class Closure(e:VEnv,x:Int,y:Term) extends Value
  case class Code(x:Term) extends Value

  sealed abstract class VOpt
  case class Some(x:Value) extends VOpt
  case object None extends VOpt

  
  sealed abstract class TEnv
  case object TNil extends TEnv
  case class TCons(x: Int, tl: TEnv) extends TEnv
  
  sealed abstract class VEnv
  case object VNil extends VEnv
  case class VCons(x: Int, y: Value, tl: VEnv) extends VEnv

  def vlookup(e: VEnv, x: Int): VOpt = {
    e match {
      case VCons(x1,v1,tail) => if (x == x1) Some(v1) else vlookup(tail,x)
      case _ => None
    }
  }

  def eval(n: Int, e: VEnv, x: Term): VOpt = if (n <= 0) None else {
    x match {
      case Lit(x) => Some(Const(x))
      case Lambda(x,y) => Some(Closure(e,x,y))
      case App(Quote,y) => Some(Code(y))
      case Var(x) => vlookup(e,x)
      case MkApp(x,y) => eval(n-1,e,x) match {
        case Some(Code(c1)) => eval(n-1,e,y) match {
          case Some(Code(c2)) => Some(Code(App(c1,c2)))
          case _ => None
        }
        case _ => None
      }
      case App(x,y) => 
        eval(n-1,e,x) match {
          case Some(Closure(e1,x1,y1)) => 
            eval(n-1,e,y) match {
              case Some(v) => eval(n-1,VCons(x1,v,e1),y1)
              case None => None
            }
          case _ => None
        }
      case _ => None
    }
  }
  
  def test1(x: Term) = { eval(VNil,x) == Some(Const(42)) } ensuring { x => !x }

  def test2(x:Int, y: Term) = { 
    eval(VNil,
      App(Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0)))),
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    ) == Some(Code(y)) } ensuring { x => !x }

  def test3(x:Int, y: Term) = { 
    eval(VNil,
      App(Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0)))),
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    ) == Some(Code(
      App(Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0)))),
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    )) } ensuring { x => x }

  def test4(x:Int, y: Term) = { 
    eval(VNil,
      y //boring: Quote(..)
    ) == Some(Code(
      App(Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0)))),
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    )) } ensuring { x => !x }
    
  def test5(x:Int, y: Term) = { 
    eval(VNil,
      App(y,
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    ) == Some(Code(
      App(Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0)))),
      App(Quote,Lambda(0, MkApp(Var(0), MkApp(App(Quote,Quote), Var(0))))))
    )) } ensuring { x => !x }  

/*
  App(Lambda(x, List(x, List(App(Quote,Quote), x))),
  Quote(Lambda(x, List(x, List(App(Quote,Quote), x)))

Code(
  App(Lambda(0, MkApp(Var(0), MkApp(App(Quote, Quote), Var(0)))), 
  App(Quote, Lambda(0, MkApp(Var(0), MkApp(App(Quote, Quote), Var(0)))))))
  
  ((lambda (x)
       (list x (list (quote quote) x)))
      (quote
         (lambda (x)
           (list x (list (quote quote) x)))))
*/



}
