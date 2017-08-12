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
}

object BoundedAPair {
  def apply[U, F[_ <: U], G[_ <: U], A0 <: U](fa: F[A0], ga: G[A0]): BoundedAPair[U, F, G] =
    new BoundedAPair[U, F, G] { type A = A0; val _1 = fa; val _2 = ga }

  def unapply[U, F[_ <: U], G[_ <: U]](p: BoundedAPair[U, F, G]): Option[(F[p.A], G[p.A])] =
    Some((p._1, p._2))

  /** Defer specifying `A`, so that it could possibly be inferred. */
  def of[U, F[_ <: U], G[_ <: U]]: Builder[U, F, G] = new Builder[U, F, G]

  class Builder[U, F[_ <: U], G[_ <: U]] {
    def apply[A <: U](fa: F[A], ga: G[A]): BoundedAPair[U, F, G] =
      BoundedAPair[U, F, G, A](fa, ga)
  }
}
