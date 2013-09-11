package dot

trait DotSyntax {
  import scala.util.parsing.input.Positional

  sealed trait Entity extends Positional

  case class Tag(id: String) extends Entity

  sealed trait Type extends Entity
  object types {
    case object Bot extends Type
    case object Top extends Type
    case class And(ty1: Type, ty2: Type) extends Type
    case class Or(ty1: Type, ty2: Type) extends Type
    case class MemType(tag: Tag, tyS: Type, tyU: Type) extends Type
    case class MemDef(tag: Tag, tyP: Type, tyR: Type) extends Type
    case class MemVal(tag: Tag, ty: Type) extends Type
    case class Tsel(p: Term, tag: Tag, hint: Option[MemType]) extends Type {
      assert(p.isPath)
    }
    case class TRec(self: terms.Var, ty: Type) extends Type
    case class SingletonType(x: terms.Var) extends Type

    case object Unknown extends Type
  }

  sealed trait Term extends Entity {
    def isVar: Boolean = false
    def isPath: Boolean = false
  }
  object terms {
    case class Var(id: String) extends Term {
      override def isVar = true
      override def isPath = true
    }
    case class Sel(o: Term, tag: Tag) extends Term {
      override def isPath = o.isPath
    }
    case class App(f: Term, tag: Tag, a: Term) extends Term
    case class New(tc: Option[Type], self: Option[Var], members: List[Init]) extends Term
    case class Let(x: Var, tyx: Type, ex: Term, body: Term) extends Term
  }

  sealed trait Init extends Positional {
    def d: Type
  }
  object init {
    case class InitDef(d: types.MemDef, param: terms.Var, body: Term) extends Init
    case class InitVal(d: types.MemVal, t: Term) extends Init
    case class InitType(d: types.MemType) extends Init
  }
}
