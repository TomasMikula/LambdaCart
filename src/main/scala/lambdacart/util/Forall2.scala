package lambdacart.util

/** Universally quantified value in two variables. */
trait Forall2[F[_, _]] {
  def apply[A, B]: F[A, B]
}
