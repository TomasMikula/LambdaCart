package lambdacart

import demo.MyDsl
import org.scalatest.FunSuite

class ForComprehensionTest extends FunSuite {
  val dsl = MyDsl.instance
  import dsl._

  test("for-comprehension syntax") {

    val plus3 = dsl[Nat, Nat](x => for {
      x1 <- inc(x)
      x2 <- inc(x1)
    } yield inc(x2))

    assert(decodeInt(exec(encodeInt(7))(plus3)) == 10)
  }
}
