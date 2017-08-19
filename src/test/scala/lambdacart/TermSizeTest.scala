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
    assert(φ[X, X](x => x).size == 1)
  }

  test("x => x ** x") {
    assert(φ[X, X**X](x => x ** x).size == 3) // prod(id, id)
  }

  test("x => y => x ** y") {
    assert(φ[X, Y, X**Y]((x, y) => x ** y).size == 2) // curry(id)
  }

  test("x => y => y ** x") {
    assert(φ[X, Y, Y**X]((x, y) => y ** x).size == 4) // curry(prod(snd, fst))
  }

  test("xy => xy._1") {
    assert(φ[X ** Y, X](xy => xy._1).size == 1)
  }

  test("xy => xy._2") {
    assert(φ[X ** Y, Y](xy => xy._2).size == 1)
  }

  test("x => y => z => x ** (y ** z)") {
    assert(φ[X, Y, Z, X**(Y**Z)]((x, y, z) => x ** (y ** z)).size == 33)
  }

  test("x => y => z => (x ** y) ** z") {
    assert(φ[X, Y, Z, (X**Y)**Z]((x, y, z) => (x ** y) ** z).size == 42)
  }

  private def assocR[A, B, C]: φ[(A**B)**C, A**(B**C)] =
    φ(abc => abc._1._1 ** (abc._1._2 ** abc._2))

  private def assocL[A, B, C]: φ[A**(B**C), (A**B)**C] =
    φ(abc => (abc._1 ** abc._2._1) ** abc._2._2)

  test("assocR") {
    assert(assocR[X, Y, Z].size == 19) // should be no more than 9
  }

  test("assocL") {
    assert(assocL[X, Y, Z].size == 9) // should be no more than 9
  }

  test("assocL . assocR") { // should reduce to identity
    assert(φ((xyz: $[(X**Y)**Z]) => assocL(assocR(xyz))).size == 28) // should be 1
  }

  test("assocR . assocL") { // should reduce to identity
    assert(φ((xyz: $[X**(Y**Z)]) => assocR(assocL(xyz))).size == 28) // should be 1
  }

  test("x => y => x") {
    assert(φ[X, Y, X]((x, y) => x).size == 2) // curry(fst)
  }

  test("x => y => y") {
    assert(φ[X, Y, Y]((x, y) => y).size == 2) // curry(snd)
  }

  test("x => y => z => x") {
    assert(φ[X, Y, Z, X]((x, y, z) => x).size == 5) // curry(curry(fst . fst))
  }

  test("x => y => z => z") {
    assert(φ[X, Y, Z, Z]((x, y, z) => z).size == 3) // curry(curry(snd))
  }

  test("flip") {
    assert(φ[X**Y, Y**X](xy => xy._2 ** xy._1).size == 3) // prod(snd, fst)
  }

  test("flip . flip") { // should reduce to identity
    def flip[A, B]: φ[A**B, B**A] = φ(ab => ab._2 ** ab._1)
    assert(φ[X**Y, X**Y](xy => flip(flip(xy))).size == 1) // identity
  }

  test("x => inc(x)") {
    assert(φ[Nat, Nat](x => inc(x)).size == 1)
  }

  test("forLoop") {
    assert(sizeOf(forLoop[X]) == 453)
  }

  test("plus") {
    assert(sizeOf(plus) == 577)
  }

  test("times") {
    assert(sizeOf(times) == 1099)
  }
}
