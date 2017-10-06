package lambdacart.util.typealigned

import scalaz.Leibniz
import scalaz.Leibniz.===

/**
 * Isomorphic to `AOption[λ[(α, β) => APair[F[α, ?], G[?, β]]], A, B]`,
 * but avoids allocating an `APair` instance.
 */
sealed abstract class AOption2[F[_, _], G[_, _], A, B]

case class ASome2[F[_, _], G[_, _], A, X, B](f: F[A, X], g: G[X, B]) extends AOption2[F, G, A, B] {
  type Pivot = X
}

abstract case class ANone2[F[_, _], G[_, _], A, B]() extends AOption2[F, G, A, B] {
  def   subst[H[_]](ha: H[A]): H[B]
  def unsubst[H[_]](hb: H[B]): H[A]
  def leibniz: A === B = subst[A === ?](Leibniz.refl)
}

object AOption2 {
  def empty[F[_, _], G[_, _], A](): AOption2[F, G, A, A] = None.asInstanceOf[AOption2[F, G, A, A]]
  def some[F[_, _], G[_, _], A, X, B](f: F[A, X], g: G[X, B]): AOption2[F, G, A, B] = ASome2(f, g)

  def apply[F[_, _], G[_, _], A](): AOption2[F, G, A, A] = empty[F, G, A]
  def apply[F[_, _], G[_, _], A, X, B](f: F[A, X], g: G[X, B]): AOption2[F, G, A, B] = some(f, g)
  def of[F[_, _], G[_, _]]: MkAOption2[F, G] = new MkAOption2[F, G]

  final class MkAOption2[F[_, _], G[_, _]](private val dummy: Boolean = false) extends AnyVal {
    def apply[A, X, B](f: F[A, X], g: G[X, B]): AOption2[F, G, A, B] = some(f, g)
    def apply[A](): AOption2[F, G, A, A] = empty[F, G, A]
  }

  private val None = none[Nothing, Nothing, Nothing]
  private def none[F[_, _], G[_, _], A]: AOption2[F, G, A, A] = new ANone2[F, G, A, A] {
    def   subst[H[_]](ha: H[A]): H[A] = ha
    def unsubst[H[_]](hb: H[A]): H[A] = hb
  }
}
