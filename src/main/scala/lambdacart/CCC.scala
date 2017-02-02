package lambdacart

/** Cartesian closed category. */
trait CCC[:=>:[_, _]] {
  /** product */
  type **[A, B]

  /** terminal object */
  type Unit

  def id[A]: A :=>: A
  def compose[A, B, C](f: B :=>: C, g: A :=>: B): A :=>: C
  def fst[A, B]: (A ** B) :=>: A
  def snd[A, B]: (A ** B) :=>: B
  def prod[A, B, C](f: A :=>: B, g: A :=>: C): A :=>: (B ** C)
  def terminal[A]: A :=>: Unit
  def curry[A, B, C](f: (A ** B) :=>: C): A :=>: B :=>: C
  def uncurry[A, B, C](f: A :=>: B :=>: C): (A ** B) :=>: C
}

object CCC {
  type Aux[:=>:[_, _], &[_, _], T] = CCC[:=>:] {
    type **[A, B] = A & B
    type Unit = T
  }
}
