package dot

import scala.text.Document
import scala.text.Document._

trait ElfPrinter { this: DotSyntax =>
  import terms._
  import types._
  import init._

  def collectTags(e: Any): List[Tag] = e match {
    case l@Tag(id) => List(l)
    case p: Product => p.productIterator.toList.flatMap(collectTags)
    case _ => Nil
  }
}
