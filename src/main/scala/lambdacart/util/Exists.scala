package lambdacart.util

sealed abstract class Exists[F[_]] private {
  type A
  val value: F[A]
}

object Exists {
  def apply[F[_], X](fx: F[X]): Exists[F] = new Exists[F] {
    type A = X
    val value = fx
  }
}
