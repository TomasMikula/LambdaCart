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
    assert(τ[X, X](x => x).size == 1)
  }

  test("x => y => x ** y") {
    assert(τ[X, Y, X**Y]((x, y) => x ** y).size == 44)
  }

  test("x => y => y ** x") {
    assert(τ[X, Y, Y**X]((x, y) => y ** x).size == 56)
  }

  test("x => y => z => x ** (y ** z)") {
    assert(τ[X, Y, Z, X**(Y**Z)]((x, y, z) => x ** (y ** z)).size == 213)
  }

  test("x => y => z => (x ** y) ** z") {
    assert(τ[X, Y, Z, (X**Y)**Z]((x, y, z) => (x ** y) ** z).size == 169)
  }

  test("x => y => x") {
    assert(τ[X, Y, X]((x, y) => x).size == 4)
  }

  test("x => y => y") {
    assert(τ[X, Y, Y]((x, y) => y).size == 4)
  }

  test("x => y => z => x") {
    assert(τ[X, Y, Z, X]((x, y, z) => x).size == 45)
  }

  test("x => y => z => z") {
    assert(τ[X, Y, Z, Z]((x, y, z) => z).size == 7)
  }

  test("forLoop") {
    assert(sizeOf(forLoop[X]) == 3622)
  }

  test("plus") {
    assert(sizeOf(plus) == 3961)
  }

  test("times") {
    assert(sizeOf(times) == 7793)
  }
}
