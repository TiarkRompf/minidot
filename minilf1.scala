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

    class LF {
      def ===(o: LF): Boolean = toString == o.toString
      def hasType(x:LF) = typ === x
      def conforms(o:LF): Option[LF] = if (this === o) Some(o) else None
      def typ: LF = ???
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
    }
    case class For(a: LF, f: LF => LF) extends LF {
      override def toString = fresh(a) { x => s"{$x}${f(x)}" }
      override def apply(x: LF) = {
        if (!(x hasType a)) error(s"expected type $a but got value $x")
        f(x)
      }
      override def typ: LF = For(a, u => f(u).typ)
      // override def inst(s:String): LF = For(a, u => f(u).inst(s"($s $u)"))
    }
    case class Apply(x: LF, y: LF) extends LF {
      override def conforms(o:LF) = {
        if (this === o) Some(o) else x conforms o map (z => x(y)) filter ( this === _ )
      }
      override def hasType(c:LF) = super.hasType(c) || x.hasType(c(y))
      override def typ = x.typ(y)
      override def toString = s"($x $y)"
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
      //println(s"iteration $n")
      //xs.foreach(println)
      //println(s"-----")

      if (d == 0) {
        val res = for (x <- xs if (x.typ conforms e).nonEmpty) yield x
        if (res.isEmpty) println("nothing found")
        else {
          val align = res.map(_.toString.length).max
          for (x <- res) {
            println(x.toString.padTo(align,' ') + "     :     " + x.typ)
          }
        }
      } else {

        def canApply(a: LF, x: LF): Boolean = a.typ match {
          case For(u,f) if x.hasType(u) => true
          case _ => 
            //println(s"nope: $x   --->   $a ")
            false
        }

        val add = for (x <- xs; a <- xs if canApply(a,x)) yield a(x)
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



    //table.foreach(println)
  }
}