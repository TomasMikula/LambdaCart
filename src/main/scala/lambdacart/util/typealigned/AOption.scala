package lambdacart.util.typealigned

import scalaz.Leibniz
import scalaz.Leibniz.===

/** Similar to `Option[F[A, B]]`, but the empty case witnesses type equality
  * between `A` and `B`.
  */
sealed abstract class AOption[F[_, _], A, B]

case class ASome[F[_, _], A, B](value: F[A, B]) extends AOption[F, A, B]

/**
  * The empty case contains evidence of type equality
  * to overcome the limitations of pattern-matching on GADTs.
  */
sealed abstract case class ANone[F[_, _], A, B]() extends AOption[F, A, B] {
  def   subst[G[_]](ga: G[A]): G[B]
  def unsubst[G[_]](gb: G[B]): G[A]
  def leibniz: A === B = subst[A === ?](Leibniz.refl)
}

object AOption {
  def empty[F[_, _], A]: AOption[F, A, A] = None.asInstanceOf[AOption[F, A, A]]

  private val None = none[Nothing, Nothing]
  private def none[F[_, _], A]: AOption[F, A, A] = new ANone[F, A, A] {
    def   subst[G[_]](ga: G[A]): G[A] = ga
    def unsubst[G[_]](gb: G[A]): G[A] = gb
  }
}
