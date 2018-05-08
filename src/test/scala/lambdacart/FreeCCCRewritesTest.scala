package lambdacart

import org.scalatest.FunSuite
import lambdacart.util.typealigned.AList1
import lambdacart.{Projection => Prj}

class FreeCCCRewritesTest extends FunSuite {

  final class ->[A, B](name: String) {
    require(name != "")
    override def toString = name
  }

  type **[A, B] = (A, B)
  type :=>:[A, B] = FreeCCC[->, **, Unit, ->, A, B]

  def lift[A, B](f: ->[A, B])                    : A :=>: B        = FreeCCC.Lift(f)
  def id[A]                                      : A :=>: A        = FreeCCC.Id()
  def prod[A, B, C](f: A :=>: B, g: A :=>: C)    : A :=>: (B, C)   = FreeCCC.Prod(f, g)
  def terminal[A]                                : A :=>: Unit     = FreeCCC.Terminal()
  def fst[A, B]                                  : (A, B) :=>: A   = FreeCCC.Fst()
  def snd[A, B]                                  : (A, B) :=>: B   = FreeCCC.Snd()
  def curry[A, B, C](f: (A, B) :=>: C)           : A :=>: (B -> C) = FreeCCC.Curry(f)
  def uncurry[A, B, C](f: A :=>: (B -> C))       : (A, B) :=>: C   = FreeCCC.Uncurry(f)
  def const[A, B, C](f: B :=>: C)                : A :=>: (B -> C) = FreeCCC.Const(f)
  def andThen[A, B, C](f: A :=>: B, g: B :=>: C) : A :=>: C        = FreeCCC.Sequence(f :: AList1(g))

  def sequence[A, B, C, D](f: A :=>: B, g: B :=>: C, h: C :=>: D): A :=>: D = FreeCCC.Sequence(f :: g :: AList1(h))
  def eval[A, B]: (A -> B, A) :=>: B = uncurry(id)
  def swap[A, B]: (A ** B) :=>: (B ** A) = FreeCCC.swap

  def primitive[A, B](name: String): A :=>: B = lift(new ->[A, B](name))

  type U
  type V
  type W
  type X
  type Y
  type Z

  test("curry(uncurry(f)) -> f") {
    val f = curry(uncurry(id[X -> Y]))
    val f0 = id
    assert(f.optim0 == f0)
  }

  test("factor leading projection in fst out of uncurry") {
    val f: ((X, Y), Z) :=>: (X, Z) =
      uncurry(
        andThen(
          fst[X, Y],
          curry(id[(X, Z)])
        )
      )

    val f0: ((X, Y), Z) :=>: (X, Z) =
      prod(
        andThen(fst, fst[X, Y]),
        snd
      )

    assert(f.optim0 == f0)
  }

  test("rewrite `prod(e andThen curry(f), g) andThen uncurry(id)` to `prod(e, g) andThen f`") {
    val f: (X, Y) :=>: (X, Y) =
      andThen(
        prod(
          andThen(fst[X, Y], curry(id[(X, Y)])),
          snd[X, Y]
        ),
        uncurry[Y -> (X, Y), Y, (X, Y)](id[Y -> (X, Y)])
      )

    val f0: (X, Y) :=>: (X, Y) =
      id[(X, Y)]

    assert(f.optim0 == f0)
  }

  test("defer adding unit (1)") {
    val g = primitive[X, Y]("g")
    val h = primitive[(Unit, Y), Z]("h")

    val f : X :=>: (Z, Y) = prod(terminal[X], g) andThen prod(h, snd)
    val f0: X :=>: (Z, Y) = g andThen prod(prod(terminal[Y], id[Y]) andThen h, id[Y])

    assert(f.optim0 == f0)
  }

  test("defer adding unit (2)") {
    val g = primitive[X, Y]("g")
    val h = primitive[X, Z]("h")
    val i = primitive[(Y, Unit), U]("i")
    val j = primitive[(Y, Z), V]("j")

    val f: X :=>: (U, V) =
      andThen(
        prod(
          prod(g, terminal[X]),
          h
        ),
        prod(
          fst[(Y, Unit), Z] andThen i,
          andThen(
            prod(
              fst[(Y, Unit), Z] andThen fst[Y, Unit],
              snd[(Y, Unit), Z]
            ),
            j
          )
        )
      )

    val f0: X :=>: (U, V) =
      andThen(
        prod(g, h),
        prod(
          sequence(fst[Y, Z], prod(id[Y], terminal[Y]), i),
          j
        )
      )

    assert(f.optim0 == f0)
  }

  test("optimize evaluation when argument is not used") {
    val y: Unit :=>: Y = primitive("y")

    val f1: X :=>: X = curry(fst[X, Y]) andThen prod(id, terminal[Y -> X] andThen y) andThen eval
    val f2: X :=>: X = prod(curry(fst[X, Y]), terminal[X] andThen y) andThen eval
    val f0: X :=>: X = id

    assert(f1.optim0 == f0)
    assert(f2.optim0 == f0)
  }

  test("gcd(fst, snd >>> fst)") {
    val p1: Prj[**, Unit, (X, (Y, Z)), X] = Prj.Fst()
    val p2: Prj[**, Unit, (X, (Y, Z)), Y] = Prj.Snd() andThen Prj.Fst()

    val gcd = (p1 gcd p2)._1

    assert(gcd == Prj.par(Prj.Id[**, Unit, X](), Prj.Fst[**, Unit, Y, Z]()))
  }

  test("extract leading projection from prod(fst >>> snd, snd)") {
    val f: ((X, Y), Z) :=>: (Y, Z) =
      prod(fst[(X, Y), Z] andThen snd, snd)

    val pg = Prj.extractFrom(f)
    val (p, g) = (pg._1, pg._2)

    assert(p == Prj.par(Prj.Snd[**, Unit, X, Y](), Prj.Id[**, Unit, Z]()))
    assert(g == id)
  }

  test("extract leading projection from prod(fst, snd >>> snd)") {
    val f: (X, (Y, Z)) :=>: (X, Z) =
      prod(fst[X, (Y, Z)], snd[X, (Y, Z)] andThen snd)

    val pg = Prj.extractFrom(f)
    val (p, g) = (pg._1, pg._2)

    assert(p == Prj.par(Prj.Id[**, Unit, X](), Prj.Snd[**, Unit, Y, Z]()))
    assert(g == id)
  }

  test("restrict prod(fst, snd >>> fst) by projection Snd") {
    val f: (X, (Y, Z)) :=>: (X, Y) =
      prod(
        fst[X, (Y, Z)],
        andThen(snd[X, (Y, Z)], fst[Y, Z])
      )

    val p: Prj[**, Unit, (X, Y), Y] = Prj.Snd()

    val f1 = Prj.restrictResult(f)(p)

    val f0: (X, (Y, Z)) :=>: Y = andThen(snd[X, (Y, Z)], fst[Y, Z])

    assert(f1 == Some(f0))
  }

  test("extract leading projection from prod(fst, snd >>> fst) >>> snd") {
    val f: (X, (Y, Z)) :=>: Y =
      andThen(
        prod(
          fst[X, (Y, Z)],
          andThen(snd[X, (Y, Z)], fst[Y, Z])
        ),
        snd[X, Y]
      )

    val p = Prj.extractFrom(f)._1

    val p0: Prj[**, Unit, (X, (Y, Z)), Y] =
      Prj.Snd() andThen Prj.Fst()

    assert(p == p0)
  }

  test("restrict prod(snd, fst) by projection par(id, snd)") {
    val f: ((X ** Y) ** Z) :=>: (Z ** (X ** Y)) =
      prod(snd,fst)
                      
    val p: Prj[**, Unit, Z ** (X ** Y), Z ** Y] =
      Prj.Par(Prj.Id(), Prj.Snd())

    val f0: ((X ** Y) ** Z) :=>: (Z ** Y) =
      prod(
        snd[X ** Y, Z],
        andThen(fst[X ** Y, Z], snd[X, Y])
      )

    val f1 = Prj.restrictResult(f)(p)

    assert(f1 == Some(f0))
  }

  test("extract leading projection from a mix of shuffle and projection") {
    val f: (W ** (X ** (Y ** Z))) :=>: ((Y ** Z) ** X) =
      andThen(
        andThen(
          prod(
            prod(
              fst[W, X ** (Y ** Z)],
              andThen(snd[W, X ** (Y ** Z)], fst[X, Y ** Z])
            ),
            andThen(snd[W, X ** (Y ** Z)], snd[X, Y ** Z])
          ),
          prod(snd[W ** X, Y ** Z], fst[W ** X, Y ** Z])
        ),
        prod(
          fst[Y ** Z, W ** X],
          andThen(snd[Y ** Z, W ** X], snd[W, X])
        )
      )


    val pg = Prj.extractFrom(f)
    val (p, g) = (pg._1, pg._2)

    val p0: Prj[**, Unit, W ** (X ** (Y ** Z)), X ** (Y ** Z)] =
      Prj.Snd()

    assert(p == p0)
    assert(g == swap)
  }

  test("shuffle normalization: swap >>> swap") {
    val s = Shuffle.Swap[**, X, Y] andThen Shuffle.Swap[**, Y, X]

    assert(s == Shuffle.Id())
  }

  test("shuffle normalization: assocLR >>> assocRL") {
    val s = Shuffle.AssocLR[**, X, Y, Z] andThen Shuffle.AssocRL[**, X, Y, Z]

    assert(s == Shuffle.Id())
  }

  test("shuffle normalization: assocRL >>> assocLR") {
    val s = Shuffle.AssocRL[**, X, Y, Z] andThen Shuffle.AssocLR[**, X, Y, Z]

    assert(s == Shuffle.Id())
  }

  test("shuffle normalization: par(swap, id) >>> par(id, swap)") {
    val s =
      Shuffle.par(Shuffle.Swap[**, X, Y], Shuffle.Id[**, U ** V]) andThen
      Shuffle.par(Shuffle.Id[**, Y ** X], Shuffle.Swap[**, U, V])

    val s0 = Shuffle.par(Shuffle.Swap[**, X, Y], Shuffle.Swap[**, U, V])

    assert(s == s0)
  }

  test("shuffle normalization: swap >>> par(swap, swap) >>> swap") {
    val s: Shuffle[**, (X ** Y) ** (U ** V), (Y ** X) ** (V ** U)] =
      Shuffle.Swap[**, X ** Y, U ** V] andThen
      Shuffle.par(
        Shuffle.Swap[**, U, V],
        Shuffle.Swap[**, X, Y]
      ) andThen
      Shuffle.Swap[**, V ** U, Y ** X]

    val s0: Shuffle[**, (X ** Y) ** (U ** V), (Y ** X) ** (V ** U)] =
      Shuffle.par(
        Shuffle.Swap[**, X, Y],
        Shuffle.Swap[**, U, V]
      )

    assert(s == s0)
  }

  test("extract leading shuffle from prod(snd, fst)") {
    val f: (X, Y) :=>: (Y, X) =
      prod(snd, fst)

    val sg = Shuffle.extractFrom(f)

    assert(sg._1 == Shuffle.Swap())
  }

  test("extract leading shuffle from prod(fst, snd) >>> prod(snd, fst)") {
    val f: (X, Y) :=>: (Y, X) =
      andThen(
        prod(
          fst[X, Y],
          snd[X, Y]
        ),
        prod(
          snd[X, Y],
          fst[X, Y]
        )
      )

    val sg = Shuffle.extractFrom(f)

    assert(sg._1 == Shuffle.Swap())
  }

  test("extract leading shuffle from id >>> prod(snd, fst)") {
    val f: (X, Y) :=>: (Y, X) =
      andThen(
          id[(X, Y)],
          prod(
            snd[X, Y],
            fst[X, Y]
          )
      )

    val sg = Shuffle.extractFrom(f)

    assert(sg._1 == Shuffle.Swap())
  }

  test("extract leading shuffle from assocLR") {
    val f: ((X, Y), Z) :=>: (X, (Y, Z)) =
      prod(
        fst[(X, Y), Z] andThen fst,
        prod(
          fst[(X, Y), Z] andThen snd,
          snd[(X, Y), Z]
        )
      )

    val sg = Shuffle.extractFrom(f)
    val (s, g) = (sg._1, sg._2)

    assert(s == Shuffle.AssocLR())
  }

  test("extract leading shuffle from assocRL") {
    val f: (X, (Y, Z)) :=>: ((X, Y), Z) =
      prod(
        prod(
          fst[X, (Y, Z)],
          snd[X, (Y, Z)] andThen fst
        ),
        snd[X, (Y, Z)] andThen snd
      )

    val sg = Shuffle.extractFrom(f)
    val (s, g) = (sg._1, sg._2)

    assert(s == Shuffle.AssocRL())
  }

  test("extract leading shuffle from prod(fst, snd >> prod(snd, fst))") {
    val f: (X, (Y, Z)) :=>: (X, (Z, Y)) =
      prod(
        fst[X, (Y, Z)],
        andThen(snd[X, (Y, Z)], prod(snd[Y, Z], fst[Y, Z]))
      )

    val sg = Shuffle.extractFrom(f)
    val (s, g) = (sg._1, sg._2)

    val s0: Shuffle[**, X ** (Y ** Z), X ** (Z ** Y)] =
      Shuffle.par(Shuffle.Id[**, X], Shuffle.Swap[**, Y, Z])

    assert(s == s0)
  }

test("extract leading shuffle from prod(snd >>> fst, prod(fst, snd >>> snd))") {
  val f: (X, (Y, Z)) :=>: (Y, (X, Z)) =
    prod(
      snd andThen fst,
      prod(
        fst,
        snd andThen snd
      )
    )

  val sg = Shuffle.extractFrom(f)
  val (s, g) = (sg._1, sg._2)

  val s0: Shuffle[**, X ** (Y ** Z), Y ** (X ** Z)] =
    Shuffle.AssocRL() andThen Shuffle.par(Shuffle.Swap[**, X, Y](), Shuffle.Id[**, Z]()) andThen Shuffle.AssocLR()

  assert(s == s0)
  assert(g.optim0 == id)
}

  test("incorporate assocLR") {
    val g: ((X ** (Y ** U)) ** Z) :=>: X = primitive("g")

    val f: ((X ** (Y ** U)) ** Z) :=>: ((X ** Y) ** Z) =
      prod(
        prod(
          g,
          sequence(fst[X ** (Y ** U), Z], snd[X, Y ** U], fst[Y, U])
        ),
        snd[X ** (Y ** U), Z]
      )

    val f1Opt: Option[((X ** (Y ** U)) ** Z) :=>: (X ** (Y ** Z))] =
      Shuffle.shuffleResult(f)(Shuffle.AssocLR())

    val f0: ((X ** (Y ** U)) ** Z) :=>: (X ** (Y ** Z)) =
      prod(
        g,
        prod(
          sequence(fst[X ** (Y ** U), Z], snd[X, Y ** U], fst[Y, U]),
          snd[X ** (Y ** U), Z]
        )
      )

    assert(f1Opt.map(_.optim0) == Some(f0))
  }

  test("extract and incorporate assocLR") {
    val g: ((X ** (Y ** U)) ** Z) :=>: X = primitive("g")

    val f: ((X ** (Y ** U)) ** Z) :=>: (X ** (Y ** Z)) =
      andThen(
        prod(
          prod(
            g,
            sequence(fst[X ** (Y ** U), Z], snd[X, Y ** U], fst[Y, U])
          ),
          snd[X ** (Y ** U), Z]
        ),
        prod(
          andThen(fst[X ** Y, Z], fst[X, Y]),
          prod(
            andThen(fst[X ** Y, Z], snd[X, Y]),
            snd[X ** Y, Z]
          )
        )
      )

    val f0: ((X ** (Y ** U)) ** Z) :=>: (X ** (Y ** Z)) =
      prod(
        g,
        prod(
          sequence(fst[X ** (Y ** U), Z], snd[X, Y ** U], fst[Y, U]),
          snd[X ** (Y ** U), Z]
        )
      )

    assert(f.optim0 == f0)
  }

  test("extract and incorporate assocRL") {
    val f: ((X -> Y, (X, U)), Z) :=>: (Y, Z) =
      andThen(
        prod(
          andThen(fst[(X -> Y, (X, U)), Z], fst[X -> Y, (X, U)]),
          prod(
            sequence(fst[(X -> Y, (X, U)), Z], snd[X -> Y, (X, U)], fst[X, U]),
            snd[(X -> Y, (X, U)), Z]
          )
        ),
        prod(
          andThen(
            prod(
              fst[X -> Y, (X, Z)],
              andThen(snd[X -> Y, (X, Z)], fst[X, Z])
            ),
            eval[X, Y]
          ),
          andThen(snd[X -> Y, (X, Z)], snd[X, Z])
        )
      )

    val f0: ((X -> Y, (X, U)), Z) :=>: (Y, Z) =
      prod(
        sequence(
          fst[(X -> Y, (X, U)), Z],
          prod(
            fst[X -> Y, (X, U)],
            andThen(snd[X -> Y, (X, U)], fst[X, U])
          ),
          eval[X, Y]
        ),
        snd[(X -> Y, (X, U)), Z]
      )

    assert(f.optim0 == f0)
  }

  test("unshuffle") {
    val fv = primitive[U, V]("fv")
    val fw = primitive[U, W]("fw")
    val fx = primitive[U, X]("fx")
    val fy = primitive[U, Y]("fy")

    val f: U :=>: ((V, Y), (W, X)) =
      prod(prod(fv, fw), prod(fx, fy)) andThen
      prod(
        prod(
          fst andThen fst,
          snd andThen snd
        ),
        prod(
          fst andThen snd,
          snd andThen fst
        )
      )

    val f0: U :=>: ((V, Y), (W, X)) =
      prod(prod(fv, fy), prod(fw, fx))

    assert(f.optim0 == f0)
  }
}
