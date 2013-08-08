package minilf1

import scala.collection.mutable

object Test {
  def main(args: Array[String]): Unit = {

    val table = new mutable.HashMap[String,LF]

    var count = 0

    def fresh[A](x:LF)(f: LF => A): A = {
      count += 1
      try f(LFV(s"X$count",x)) finally count -= 1
    }

    def cachefresh[A:scala.reflect.ClassTag](x:LF)(f: LF => A): () => A = {
      val xs = new Array[A](10);
      { () =>
        if (count < xs.size && xs(count) != null) xs(count)
        else {
          count += 1
          val res = try f(LFV(s"X$count",x)) finally count -= 1
          if (count < xs.size) xs(count) = res
          res
        }
      }
    }


    class LF {
      def ===(o: LF): Boolean = toString == o.toString
      def hasType(x:LF) = typ === x
      def conforms(o:LF): Option[LF] = if (this === o) Some(o) else None
      def typ: LF = ???
      def head: LF = ???
      def inst(s:String): LF = LFV(s,this)
      def apply(s:String): LF = {
        val res = inst(s)
        table(s) = res
        res
      }
      def apply(x:LF): LF = Apply(this,x)
      def apply(f: LF => LF) = For(this,f)
    }

    case class LFV(s: String, c: LF) extends LF {
      override def typ = c
      override def toString = s //s"$s:$c"
      override def head = this
    }
    case class For(a: LF, f: LF => LF) extends LF {
      val str = cachefresh(a) { x => s"{$x}${f(x)}" }
      override def toString = str()
      override def apply(x: LF) = {
        if (!(x hasType a)) sys.error(s"expected type $a but got value $x")
        f(x)
      }
      override lazy val typ: LF = For(a, u => f(u).typ)
      override def inst(s:String): LF = {
        val res = For(a, u => f(u).inst(s"($s $u)"))
        assert(res.typ === this)
        res
      }
      override def head = fresh(a) { x => f(x).head }
    }
    case class Apply(x: LF, y: LF) extends LF {
      override def conforms(o:LF) = {
        if (this === o) Some(o) else x conforms o map (z => x(y)) filter ( this === _ )
      }
      override def hasType(c:LF) = super.hasType(c) || x.hasType(c(y))
      override lazy val typ = x.typ(y)
      override def toString = s"($x $y)"
      override def head = x.head
    }

    object typ extends LFV("type", null) {
      override def toString = s"type"
    }



    val nat = typ("nat")
    val z = nat("z")
    val s = nat { N => nat } ("s")

    println(s)

    println(s(z) + " : " + (s(z)).typ)


    println("---")


    val lte = nat { N1 => nat { N2 => typ } } ("lte") 

    println(lte)

    val lte_z = nat { N => lte(z)(N) } ("lte-z")

    println(lte_z)


    val lte_s = nat { N1 => nat { N2 => 
                lte(N1)(N2) { LTE => lte(s(N1))(s(N2)) } } } ("lte-s")

    println(lte_s)

    println("---")


    val lte_refl = nat { N => lte(N)(N) { LTE => typ } } ("lte-refl")

    val lte_refl_z = lte_refl(z)(lte_z(z)) ("lte-refl-z")

    val lte_refl_s = nat { N => lte(N)(N) { LTE => 
      val sub = lte_s(N)(N)(LTE)

      lte_refl(s(N))(sub) 

    } } ("lte-refl-s")


    println(lte_refl)
    println(lte_refl_z)
    println(lte_refl_s)

    println("---")

    println(lte_z(z))
    println(lte_z(z).typ)
    println(lte)
    println(lte(z)(z))
    println(lte_z(z).hasType(lte(z)(z)))

    println(lte_z(z).typ.conforms(lte))


    println("boo!")


    println("---")

    table.foreach(println)

    println("---")

    def saturate(e: LF, d: Int, xs: List[LF]): Unit = {
      if (d == 0) {
        val res = for (x <- xs if (/*true || */x.typ == e)) yield x
        if (res.isEmpty) println("nothing found")
        else {
          val align = res.map(_.toString.length).max
          for (x <- res) {
            println(x.toString.padTo(align,' ') + "     :     " + x.typ)
          }
        }
      } else {

        val idx = xs.collect { case a @ For(u,f) => a } groupBy { case For(u,f) => u.toString }

        val add = for (x <- xs; a <- idx.getOrElse(x.typ.toString,Nil)) yield a(x)
        saturate(e, d-1, (xs ++ add).distinct)
      }
    }

    def search(e: LF, xs: List[LF] = Nil, d: Int = 5) = saturate(e,d,xs++table.values.toList)


    fresh(nat) { N => 

      println("instances of nat:")

      search(nat,N::Nil)

      println("instances of lte:")

      search(lte,N::Nil)

    }

    println("---")


    // prove by induction lte N N 

    // 1) base case

    println("base case: lte z z")

    search(lte(z)(z))

    // 2) inductive case

    println("inductive case: lte (s N) (s N)")

    fresh(nat) { N => fresh(lte(N)(N)) { LTE => 

      println(s"assuming {$N:nat} {$LTE:lte($N)($N)}")

      search(lte(s(N))(s(N)),N::LTE::Nil)

    }}


    println("--- --- ---")


    val tpe    = typ("tpe")
 
    val int    = tpe("int")
    val bool   = tpe("bool")
    val top    = tpe("top")
    val bot    = tpe("bot")
    val arrow  = tpe { T1 => tpe { T2 => tpe } } ("arrow")


    val sub_tp        = tpe { T1 => tpe { T2 => typ } } ("sub-tp")

    val sub_tp_int    = sub_tp(int)(int) ("sub-tp-int")

    val sub_tp_bool   = sub_tp(bool)(bool) ("sub-tp-bool")

    val sub_tp_top    = tpe { T => sub_tp(T)(top) } ("sub-tp-top")

    val sub_tp_bot    = tpe { T => sub_tp(bot)(T) } ("sub-tp-bot")

    val sub_tp_arrow  = tpe { T1 => tpe { T2 => tpe { T3 => tpe { T4 => 
                          sub_tp(T3)(T1) { ST31 => sub_tp(T2)(T4) { ST24 =>
                            sub_tp(arrow(T1)(T2))(arrow(T3)(T4)) }}}}}}


    fresh(tpe) { T =>
      println(s"reflexivity: {$T:tpe} sub-tp $T $T")

      search(sub_tp(T)(T),fresh(tpe)(U=>sub_tp(U)(U))::T::Nil)
    }


    //table.foreach(println)
  }
}














