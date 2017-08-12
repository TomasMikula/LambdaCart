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
    assert(φ[X, X**X](x => x ** x).size == 116) // should be 3
  }

  test("x => y => x ** y") {
    assert(φ[X, Y, X**Y]((x, y) => x ** y).size == 111) // was 44 // should be 2 (curry(id))
  }

  test("x => y => y ** x") {
    assert(φ[X, Y, Y**X]((x, y) => y ** x).size == 183) // was 56 // should be 4 (curry(prod(snd, fst)))
  }

  test("xy => xy._1") {
    assert(φ[X ** Y, X](xy => xy._1).size == 1)
  }

  test("xy => xy._2") {
    assert(φ[X ** Y, Y](xy => xy._2).size == 1)
  }

  test("x => y => z => x ** (y ** z)") {
    assert(φ[X, Y, Z, X**(Y**Z)]((x, y, z) => x ** (y ** z)).size == 848) // was 213
  }

  test("x => y => z => (x ** y) ** z") {
    assert(φ[X, Y, Z, (X**Y)**Z]((x, y, z) => (x ** y) ** z).size == 857) // was 169
  }

  private def assocR[A, B, C]: φ[(A**B)**C, A**(B**C)] =
    φ(abc => abc._1._1 ** (abc._1._2 ** abc._2))

  private def assocL[A, B, C]: φ[A**(B**C), (A**B)**C] =
    φ(abc => (abc._1 ** abc._2._1) ** abc._2._2)

  test("assocR") {
    assert(assocR[X, Y, Z].size == 242) // should be no more than 9
  }

  test("assocL") {
    assert(assocL[X, Y, Z].size == 323) // should be no more than 9
  }

  test("assocL . assocR") { // should reduce to identity
    assert(φ((xyz: $[(X**Y)**Z]) => assocL(assocR(xyz))).size == 564) // should be 1
  }

  test("assocR . assocR") { // should reduce to identity
    assert(φ((xyz: $[X**(Y**Z)]) => assocR(assocL(xyz))).size == 564) // should be 1
  }

  test("x => y => x") {
    assert(φ[X, Y, X]((x, y) => x).size == 40) // was 4
  }

  test("x => y => y") {
    assert(φ[X, Y, Y]((x, y) => y).size == 4)
  }

  test("x => y => z => x") {
    assert(φ[X, Y, Z, X]((x, y, z) => x).size == 78) // was 45
  }

  test("x => y => z => z") {
    assert(φ[X, Y, Z, Z]((x, y, z) => z).size == 7)
  }

  test("flip") {
    assert(φ[X**Y, Y**X](xy => xy._2 ** xy._1).size == 145) // should be 3
  }

  test("flip . flip") { // should reduce to identity
    def flip[A, B]: φ[A**B, B**A] = φ(ab => ab._2 ** ab._1)
    assert(φ[X**Y, X**Y](xy => flip(flip(xy))).size == 289) // should be 1 (identity)
  }

  test("x => inc(x)") {
    assert(φ[Nat, Nat](x => inc(x)).size == 1)
  }

  test("forLoop") {
    assert(sizeOf(forLoop[X]) == 10008) // was 3622
  }

  test("plus") {
    assert(sizeOf(plus) == 11486) // was 3961
  }

  test("times") {
    assert(sizeOf(times) == 21871) // was 7793
  }
}
