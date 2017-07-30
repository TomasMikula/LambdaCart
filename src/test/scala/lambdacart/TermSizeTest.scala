package lambdacart

import demo.MyDsl
import org.scalatest.FunSuite

class TermSizeTest extends FunSuite {
  val dsl = MyDsl.instance
  import dsl._

  type X
  type Y
  type Z

  test("x => x") {
    assert(dsl.parse[X, X](x => x).size == 1)
  }

  test("x => y => x ** y") {
    assert(dsl.parse[X, Y, X**Y]((x, y) => x ** y).size == 94)
  }

  test("x => y => y ** x") {
    assert(dsl.parse[X, Y, Y**X]((x, y) => y ** x).size == 56)
  }

  test("x => y => z => x ** (y ** z)") {
    assert(dsl.parse[X, Y, Z, X**(Y**Z)]((x, y, z) => x ** (y ** z)).size == 343)
  }

  test("x => y => z => (x ** y) ** z") {
    assert(dsl.parse[X, Y, Z, (X**Y)**Z]((x, y, z) => (x ** y) ** z).size == 461)
  }

  test("x => y => x") {
    assert(dsl.parse[X, Y, X]((x, y) => x).size == 4)
  }

  test("x => y => y") {
    assert(dsl.parse[X, Y, Y]((x, y) => y).size == 4)
  }

  test("x => y => z => x") {
    assert(dsl.parse[X, Y, Z, X]((x, y, z) => x).size == 45)
  }

  test("x => y => z => z") {
    assert(dsl.parse[X, Y, Z, Z]((x, y, z) => z).size == 7)
  }

  test("forLoop") {
    assert(sizeOf(forLoop[X]) == 6457)
  }

  test("plus") {
    assert(sizeOf(plus) == 6683)
  }

  test("times") {
    assert(sizeOf(times) == 13364)
  }
}
