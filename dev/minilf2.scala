package minilf2

import scala.collection.mutable

object Engine {

  // *** run loop

  def run[T](f: Exp[T] => Rel): Unit = {
    var d = 0
    def printd(x: Any) = println(" "*d+x)

    def rec(e: () => Rel)(f: () => Unit): Unit = {
      //printd("rec: "+e)
      if (d == 2000) {
        printd("ABORT depth "+d)
        return
      }
      val d1 = d
      val save = cstore
      try {
        d += 1
        e() match {
          case Or(a,b) =>
            rec(a)(f)
            rec(b)(f)
          case And(a,b) =>
            rec(a) { () =>
              if (propagate())
                rec(b)(f)
            }
          case Yes => f()
        }
      } finally {
        cstore = save
        d = d1
      }
    }

    def propagate(): Boolean = { // propagate constraints and look for contradictions
      //printd("simplify")
      def prop(c1: Constraint, c2: Constraint)(fail: () => Nothing) = (c1,c2) match {
        case (IsEqual(Exp(a),Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
          List(IsTerm(b, key, args))
        case (IsEqual(Exp(a),Exp(b)), IsTerm(b1, key, args)) if b == b1 =>
          List(IsTerm(a, key, args))
        case (IsTerm(a1, key1, args1), IsTerm(a2, key2, args2)) if a1 == a2 =>
          if (key1 != key2 || args1.length != args2.length) fail()
          (args1,args2).zipped map (IsEqual(_,_))
        case _ => Nil
      }

      // self-join on cstore: build hash index to optimize

      //val cnew = cstore flatMap { c1 => cstore flatMap { c2 => prop(c1,c2)(() => return false) }}

      val idx = new mutable.HashMap[Int, List[Constraint]] withDefaultValue Nil

      def keys(c: Constraint) = c match {
        case IsEqual(Exp(a),Exp(b)) => List(a,b)
        case IsTerm(a, _, _) => List(a)
      }

      cstore foreach { c => keys(c) foreach { k => idx(k) = c::idx(k) }}


      val cnew = cstore flatMap { c1 => keys(c1) flatMap { k => idx(k) flatMap { c2 => prop(c1,c2)(() => return false) }}}

      //cnew filterNot (cstore contains _) foreach println

      val cstore0 = cstore
      cstore = (cstore ++ cnew).distinct.sortBy(_.toString)
      (cstore == cstore0) || propagate() // until converged
    }

    def extract(x: Exp[Any]): String = cstore collectFirst { // extract term
      case IsTerm(id, key, args) if id == x.id =>
        if (args.isEmpty) key else
        key+"("+args.map(extract).mkString(",")+")"
    } getOrElse canon(x)


    def dump(x: Exp[Any]): Unit = {
      val idx = cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }
      val stack = new scala.collection.mutable.BitSet(varCount)
      val stack2 = new scala.collection.mutable.BitSet(varCount)
      def rec(x: Exp[Any]): Unit = idx.getOrElse(x.id,Nil) match {
        case IsTerm(id, key, args)::_ =>
          assert(id == x.id)
          if (stack.contains(id)) {
            System.out.print("r"+id) // not doing occurs check during unification, at least catch cycles here
            stack2 += id
            //return
          }
          stack += id
          // hack -- special case. don't print types.
          if (key == "lf") {
            rec(args.head)
            if (!idx.contains(args.head.id)) {
              System.out.print(":")
              rec(args.tail.head)
            }
            if (stack2.contains(id))
              System.out.print("=r"+id)
            stack -= id
            stack2 -= id
            return
          }

          System.out.print(key)
          if (args.nonEmpty) {
            System.out.print("(")
            rec(args.head)
            args.tail.foreach { a => System.out.print(","); rec(a) }
            System.out.print(")")
          }
          if (stack2.contains(id)) {
            System.out.print("=r"+id)
          }
          stack -= id
          stack2 -= id
        case _ =>
          System.out.print(canon(x))
      }
      rec(x)
      System.out.println
      System.out.flush
    }



    def canon(x: Exp[Any]): String = { // canonicalize var name
      val id = (x.id::(cstore collect {
        case IsEqual(`x`,y) if y.id < x.id => y.id
        case IsEqual(y,`x`) if y.id < x.id => y.id
      })).min
      "x"+id
    }


    val saveVarCount = varCount
    try {
      val q = fresh[T]
      rec(() => f(q)){() =>
        if (propagate()) {
          //printd("success!")
          //printd(eval(q))
          //cstore foreach { c => printd("    "+c)}
          dump(q)
        }
      }
    } finally {
      varCount = saveVarCount
    }

    println("----")
  }


  // *** terms and constraints

  case class Exp[+T](id: Int)

  val varCount0 = 0
  var varCount = varCount0
  def fresh[T] = Exp[T] { varCount += 1; varCount - 1 }

  abstract class Constraint
  case class IsTerm(id: Int, key: String, args: List[Exp[Any]]) extends Constraint
  case class IsEqual(x: Exp[Any], y: Exp[Any]) extends Constraint

  abstract class Rel
  case class Or(x: () => Rel, y: () => Rel) extends Rel
  case class And(x: () => Rel, y: () => Rel) extends Rel
  case object Yes extends Rel



  val cstore0: List[Constraint] = Nil
  var cstore: List[Constraint] = cstore0

  def register(c: Constraint): Unit = {
    cstore = c::cstore // start simplify right here?
  }

  def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
    val id = fresh[T]
    val c = IsTerm(id.id, key, args)
    register(c)
    id
  }

  def exists[T](f: Exp[T] => Rel): Rel = {
    f(fresh[T])
  }

  def exists[T,U](f: (Exp[T],Exp[U]) => Rel): Rel = {
    f(fresh[T],fresh[U])
  }

  def exists[T,U,V](f: (Exp[T],Exp[U],Exp[V]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V])
  }

  def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
    val c = IsEqual(a,b)
    register(c)
    Yes
  }
  def infix_&&(a: => Rel, b: => Rel): Rel = {
    And(() => a,() => b)
  }
  def infix_||(a: => Rel, b: => Rel): Rel = {
    Or(() => a,() => b)
  }

  implicit class ExpOps[T](a: Exp[T]) {
    def ===(b: Exp[T]) = infix_===(a,b)
  }
  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }

}

object Base {
  import Engine._

  def list(xs: String*): Exp[List[String]] = if (xs.isEmpty) nil else cons(term(xs.head,Nil),list(xs.tail:_*))

  def cons[T](hd: Exp[T], tl: Exp[List[T]]): Exp[List[T]] = term("cons",List(hd,tl))
  def nil: Exp[List[Nothing]] = term("nil",List())
  def pair[A,B](a: Exp[A], b: Exp[B]): Exp[(A,B)] = term("pair",List(a,b))

  object Cons {
    def unapply[T](x: Exp[List[T]]): Some[(Exp[T],Exp[List[T]])] = {
      val h = fresh[T]
      val t = fresh[List[T]]
      x === cons(h,t)
      Some((h,t))
    }
  }
  object Pair {
    def unapply[A,B](x: Exp[(A,B)]): Some[(Exp[A],Exp[B])] = {
      val a = fresh[A]
      val b = fresh[B]
      x === pair(a,b)
      Some((a,b))
    }
  }
}


object Test1 {

  // *** basic test

  def main(args: Array[String]) {
    import Engine._
    import Base._

    def append[T](as: Exp[List[T]], bs: Exp[List[T]], cs: Exp[List[T]]): Rel =
      (as === nil && bs === cs) ||
      exists[T,List[T],List[T]] { (h,t1,t2) =>
        (as === cons(h,t1)) && (cs === cons(h,t2)) && append(t1,bs,t2)
      }


    run[List[String]] { q =>
      append(list("a","b","c"), list("d","e","f"), q)
    }

    run[List[String]] { q =>
      append(list("a","b","c"), q, list("a","b","c","d","e","f"))
    }

    run[List[String]] { q =>
      append(q, list("d","e","f"), list("a","b","c","d","e","f"))
    }

    run[(List[String],List[String])] { q =>
      val q1,q2 = fresh[List[String]]
      (q === pair(q1,q2)) &&
      append(q1, q2, list("a","b","c","d","e","f"))
    }

    run[(List[String],List[String])] {
      case Pair(q1,q2) =>
        append(q1, q2, list("a","b","c","d","e","f"))
    }

    run[(List[String],List[String])] {
      case Pair(q1,q2) => q1 === q2
    }
  }
}




object TestLF0 {

  def main(args: Array[String]) {
    import Engine._
    import Base._

    trait LF

    run[(LF,LF)] {
      case Pair(q1,q2) =>

        def lf(s: Exp[LF], x: Exp[LF]): Exp[LF] = term("lf", List(s,x))

        val typ = term[LF]("type",Nil)

        val nat = lf(term("nat",Nil),typ)

        val z = lf(term("z",Nil), nat)

        def s(x: Exp[LF]) = { checktp(x,nat); lf(term("s",x::Nil), nat) } // exist[LF] { y => x === lf(y,nat) && lf(term("s",y::Nil), nat) }

        def lte(n1: Exp[LF], n2: Exp[LF]) = { checktp(n1,nat); checktp(n2,nat); lf(term("lte",n1::n2::Nil), typ) }

        def lft(x: Exp[LF])(k: Exp[LF] => Rel): Rel = exists[LF] { y => k(lf(y,x)) }

        def checktp(x: Exp[LF], y: Exp[LF]) = { x === lf(fresh,y) }

        def lteX(n1: Exp[LF], n2: Exp[LF]): Rel = checktp(n1,nat) && checktp(n2,nat) && {
          (n1 === z) ||
          lft(nat) { n11 => lft(nat) { n21 => n1 === s(n11) && n2 === s(n21) && lteX(n11,n21) }}
        }


        def lte_z = {
          val n = fresh[LF]
          lf(term("lte-z",Nil),lte(z,n))
        }

        def lte_s(d: Exp[LF]) = {
          val n1 = fresh[LF]
          val n2 = fresh[LF]
          checktp(d,lte(n1,n2))
          lf(term("lte-s",d::Nil),lte(s(n1),s(n2)))
        }

        def lteZ(d: Exp[LF]): Rel = {
          d === lte_z || exists[LF] { d2 => d === lte_s(d2) }
        }


        // find all derivations Q1 for (lte Q2 Q2)

        lteZ(lf(q1,lte(q2,q2)))

        //val n = lf(term("X",Nil), nat)
        //val ev = lf(term("E",Nil),lte(n,n))

        //lteZ(lf(q1,lte(z,z))) && lteZ(lf(q2,lte(s(n),s(n))))


    }
  }
}


object BaseLF1 {
    import Engine._

    trait LF

    def lf(s: Exp[LF], x: Exp[LF]): Exp[LF] = term("lf", List(s,x))

    def checktp(x: Exp[LF], y: Exp[LF]) = { x === lf(fresh,y); x }

    abstract class Term {
      type Self <: Term
      //def apply(s: String,xs:List[Atom] = Nil): Term
      def apply(s: String,xs:List[Atom] = Nil): Self
    }
    case class Atom(lv: Exp[LF]) extends Term {
      type Self = Atom
      def apply(s: String,xs:List[Atom]) = Atom(lf(term(s,xs.map(_.lv)),lv))
      def apply[B<:Term](f: Atom => B) = For[B](this,f)
      def in[T](f: Atom => T): T = f(this)
      def typed(u: Atom) = { checktp(lv,u.lv); this }
      def ===(u: Atom) = lv === u.lv
    }
    case class For[B<:Term](u: Atom, f: Atom => B) extends Term {
      type Self = For[B#Self]
      //def unapplySeq(x:Atom): Option[Seq[Atom]] =
      def apply(s: String,xs:List[Atom]) = For(u, x => f(x)(s,xs:+x))
      def apply(x:Atom): B = f(x.typed(u))
    }

    object Term {
      def unapply(x: Exp[LF]) = Some(Atom(x))
    }

    def % = Atom(fresh)

    /// XXX init oder -- ok??
    object typ extends Atom(term[LF]("type",Nil)) // { type Self = typ.type }

}


object TestLF1_lte {

  def main(args: Array[String]) {
    import Engine._
    import Base._
    import BaseLF1._


    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>

        val nat = typ("nat")

        val z = nat("z")

        val s = nat { N1 => nat } ("s")


        // val x = s(s(Atom(q2))).lv
        // q1 === x

        val lte = nat { N1 => nat { N2 => typ } } ("lte")

        val lte_z = nat { N1 => lte(z)(N1) } ("lte-z")

        val lte_s = nat { N1 => nat { N2 => lte(N1)(N2) { LTE => lte(s(N1))(s(N2)) }}} ("lte-s")


        def lteZ(d: Atom): Rel = {
          d === lte_z(%) || d === lte_s(%)(%)(%)
        }


        // find all derivations Q1 for (lte Q2 Q2)
        lteZ(q1.typed(lte(q2)(q2)))
    }

  }
}


object TestLF2 {

  def main(args: Array[String]) {
    import Engine._
    import Base._
    import BaseLF1._

    val nat = typ("nat")
    val z = nat("z")
    val s = nat { N1 => nat } ("s")

    val exp = typ("exp")
    val cst = nat { N => exp } ("cst")
    val idn = nat { N => exp } ("idn")
    val fun = exp { E => exp } ("fun")
    val app = exp { E1 => exp { E2 => exp }} ("exp")

    val tpe = typ("tpe")
    val tnat = tpe("tnat")
    val tbot = tpe("tbot")
    val ttop = tpe("ttop")
    val tfun = tpe { T1 => tpe { T1 => tpe }} ("tfun")

    val env = typ("env")
    val nil = env("nil")
    val cons = tpe { T => env { G => env }} ("cons")

    val lookup = env { G => nat { N => tpe { T => typ }}} ("lookup")

    val hit = env { G => tpe { T => lookup(cons(T)(G))(z)(T) }} ("hit")
    
    val miss = env { G => nat { N => tpe { T =>
          lookup(G)(N)(T) { LK => lookup(cons(%)(G))(s(N))(T) }}}} ("miss")


    val tp_exp = env { G => exp { E => tpe { T => typ }}} ("tp-exp")

    val tp_cst = env { G => nat { N => tp_exp(G)(cst(N))(tnat) }} ("tp-cst")

    val tp_var = env { G => nat { N => tpe { T => 
          lookup(G)(N)(T) { L => tp_exp(G)(idn(N))(T) }}}} ("tp-var")

    val tp_fun = env { G => exp { E => { tpe { T1 => tpe { T2 =>
          tp_exp(cons(T1)(G))(E)(T2) { TP => tp_exp(G)(fun(E))(tfun(T1)(T2)) }}}}}} ("tp-fun")

    val tp_app = env { G => exp { E1 => exp { E2 => { tpe { T1 => tpe { T2 =>
          tp_exp(G)(E1)(tfun(T1)(T2)) { TP1 => tp_exp(G)(E2)(T1) { TP2 => tp_exp(G)(app(E1)(E2))(T2) }}}}}}}} ("tp-app")


    def searchLookup(d: Atom): Rel = {
      d === hit(%)(%) || 
      %.in { d1 => d === miss(%)(%)(%)(d1) && searchLookup(d1) }
    }

    def searchTp(d: Atom): Rel = {
      d === tp_cst(%)(%) || 
      %.in { dv => d === tp_var(%)(%)(%)(dv)    && searchLookup(dv) } ||
      %.in { d1 => d === tp_fun(%)(%)(%)(%)(d1) && searchTp(d1) } ||
      %.in { d1 => %.in { d2 => 
        d === tp_app(%)(%)(%)(%)(%)(d1)(d2)     && searchTp(d1) && searchTp(d2) }}
    }

    // test lookup
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env = cons(tnat)(nil)
        val idn = z
        searchLookup(q1.typed(lookup(env)(idn)(q2)))
    }
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env = cons(tbot)(cons(tnat)(nil))
        val idn = z
        searchLookup(q1.typed(lookup(env)(idn)(q2)))
    }
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env = cons(tbot)(cons(tnat)(nil))
        val idn = s(z)
        searchLookup(q1.typed(lookup(env)(idn)(q2)))
    }


    // test typing
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env  = cons(tbot)(cons(tnat)(nil))
        val term = idn(s(z))
        searchTp(q1.typed(tp_exp(env)(term)(q2)))
    }
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env  = nil
        val term = fun(idn(z))
        searchTp(q1.typed(tp_exp(env)(term)(q2)))
    }
    run[(LF,LF)] {
      case Pair(Term(q1),Term(q2)) =>
        val env  = nil
        val term = app(fun(idn(z)))(cst(s(z)))
        searchTp(q1.typed(tp_exp(env)(term)(q2)))
    }



  }
}
