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
    assert(φ[X, X](x => x).size == 1) // id
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
    assert(φ[X ** Y, X](xy => xy._1).size == 1) // fst
  }

  test("xy => xy._2") {
    assert(φ[X ** Y, Y](xy => xy._2).size == 1) // snd
  }

  test("x => y => z => x ** (y ** z)") {
    assert(φ[X, Y, Z, X**(Y**Z)]((x, y, z) => x ** (y ** z)).size == 11)
  }

  test("x => y => z => (x ** y) ** z") {
    assert(φ[X, Y, Z, (X**Y)**Z]((x, y, z) => (x ** y) ** z).size == 3) // curry(curry(id))
  }

  private def assocR[A, B, C]: φ[(A**B)**C, A**(B**C)] =
    φ(abc => abc._1._1 ** (abc._1._2 ** abc._2))

  private def assocL[A, B, C]: φ[A**(B**C), (A**B)**C] =
    φ(abc => (abc._1 ** abc._2._1) ** abc._2._2)

  test("assocR") {
    assert(assocR[X, Y, Z].size == 9) // should be no more than 9
  }

  test("assocL") {
    assert(assocL[X, Y, Z].size == 9) // should be no more than 9
  }

  test("assocL . assocR") { // should reduce to identity
    assert(φ((xyz: $[(X**Y)**Z]) => assocL(assocR(xyz))).size == 1) // identity
  }

  test("assocR . assocL") { // should reduce to identity
    assert(φ((xyz: $[X**(Y**Z)]) => assocR(assocL(xyz))).size == 1) // identity
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

  test("flip . flip") {
    def flip[A, B]: φ[A**B, B**A] = φ(ab => ab._2 ** ab._1)
    assert(φ[X**Y, X**Y](xy => flip(flip(xy))).size == 1) // identity
  }

  test("x => inc(x)") {
    assert(φ[Nat, Nat](x => inc(x)).size == 1) // inc
  }

  test("x => inc(inc(x))") {
    assert(φ[Nat, Nat](x => inc(inc(x))).size == 3) // inc >>> inc
  }

  test("forLoop") {
    assert(sizeOf(forLoop[X]) == 270)
  }

  test("plus") {
    assert(sizeOf(plus) == 290)
  }

  test("plus, relative to forLoop") {
    val plus: φ[Nat, Nat ->: Nat] =
      φ[Nat, Nat, Nat]((a, b) => forLoop(a)(b)(inc))

    assert(plus.size == 17)
  }

  test("times") {
    assert(sizeOf(times) == 623)
  }
}
