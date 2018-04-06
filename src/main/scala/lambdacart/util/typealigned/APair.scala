package lambdacart.util.typealigned

object APair {
  def apply[F[_], G[_], A](fa: F[A], ga: G[A]): APair[F, G] =
    BoundedAPair[Any, F, G, A](fa, ga)

  def unapply[F[_], G[_]](p: APair[F, G]): Option[(F[p.A], G[p.A])] =
    Some((p._1, p._2))

  /** Defer specifying `A`, so that it could possibly be inferred. */
  def of[F[_], G[_]] = BoundedAPair.of[Any, F, G]
}

sealed abstract class BoundedAPair[U, F[_ <: U], G[_ <: U]] {
  type A <: U
  val _1: F[A]
  val _2: G[A]

  def swap: BoundedAPair[U, G, F] = BoundedAPair(_2, _1)
}

object BoundedAPair {
  def apply[U, F[_ <: U], G[_ <: U], A0 <: U](fa: F[A0], ga: G[A0]): BoundedAPair[U, F, G] =
    new BoundedAPair[U, F, G] { type A = A0; val _1 = fa; val _2 = ga }

  def unapply[U, F[_ <: U], G[_ <: U]](p: BoundedAPair[U, F, G]): Option[(F[p.A], G[p.A])] =
    Some((p._1, p._2))

  /** Defer specifying `A`, so that it could possibly be inferred. */
  def of[U, F[_ <: U], G[_ <: U]]: Builder[U, F, G] = new Builder[U, F, G]

  class Builder[U, F[_ <: U], G[_ <: U]] private[BoundedAPair] {
    def apply[A <: U](fa: F[A], ga: G[A]): BoundedAPair[U, F, G] =
      BoundedAPair[U, F, G, A](fa, ga)
  }
}

sealed abstract class A2Pair[F[_,_], G[_,_]] {
  type A
  type B
  val _1: F[A, B]
  val _2: G[A, B]

  def swap: A2Pair[G, F] = A2Pair(_2, _1)
}

object A2Pair {
  def apply[F[_,_], G[_,_], X, Y](f: F[X,Y], g: G[X,Y]): A2Pair[F, G] =
    new A2Pair[F, G] { type A = X; type B = Y; val _1 = f; val _2 = g }

  def of[F[_,_], G[_,_]]: Builder[F, G] = new Builder[F, G]

  class Builder[F[_,_], G[_,_]] private[A2Pair] {
    def apply[A, B](f: F[A, B], g: G[A, B]): A2Pair[F, G] =
      A2Pair(f, g)
  }
}
