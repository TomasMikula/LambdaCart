package lambdacart

import scalaz.Category

/** Cartesian closed category. */
trait CCC[:=>:[_, _]] extends Category[:=>:] {
  /** product */
  type **[A, B]

  /** terminal object (empty product) */
  type Unit

  /** internal hom object (function space as an object; also exponential object) */
  type Hom[A, B]

  // category
  def id[A]: A :=>: A
  def compose[A, B, C](f: B :=>: C, g: A :=>: B): A :=>: C

  // cartesian
  def fst[A, B]: (A ** B) :=>: A
  def snd[A, B]: (A ** B) :=>: B
  def prod[A, B, C](f: A :=>: B, g: A :=>: C): A :=>: (B ** C)
  def terminal[A]: A :=>: Unit

  // closed
  def curry[A, B, C](f: (A ** B) :=>: C): A :=>: Hom[B, C]
  def uncurry[A, B, C](f: A :=>: Hom[B, C]): (A ** B) :=>: C

  // derived methods
  def andThen[A, B, C](f: A :=>: B, g: B :=>: C): A :=>: C = compose(g, f)
  def const[A, B, C](f: B :=>: C): A :=>: Hom[B, C] = curry(andThen(snd[A, B], f))
}

object CCC {
  type Aux[:=>:[_, _], &[_, _], T, H[_, _]] = CCC[:=>:] {
    type **[A, B] = A & B
    type Unit = T
    type Hom[A, B] = H[A, B]
  }

  /** "Homoiconic" CCC, meaning that the morphisms have
    * the same representation as internal hom-objects.
    */
  type HI[:=>:[_, _]] = CCC[:=>:] {
    type Hom[A, B] = A :=>: B
  }

  type AuxHI[:=>:[_, _], &[_, _], T] = Aux[:=>:, &, T, :=>:]
}
