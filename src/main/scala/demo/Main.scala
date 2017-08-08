package demo

object Main extends App {
  val dsl = MyDsl.instance
  import dsl._

  val fac: Nat :->: Nat = dsl { n =>
    forLoop(n)(one ** one)( both(_) { acc => i =>
      times(acc)(i) ** inc(i)
    })._1
  }

  assert(decodeInt(exec(encodeInt(2), encodeInt(2))(plus)) == 4)
  assert(decodeInt(exec(encodeInt(7))(fac)) == 5040)
}
