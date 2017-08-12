package lambdacart.util

import scalaz.Compose

package object typealigned {

  /**
    * Type-aligned pair. Isomorphic to
    *
    * {{{
    * (F[A], G[A]) forSome { type A }
    * }}}
    *
    * The "pivot" type `A` is intentionally "hidden" as a type member
    * (as opposed to being a type parameter), so that pairs that differ
    * only in the pivot are considered to be of the same type and thus
    * can be used as arguments to tail-optimized recursive calls.
    */
  type APair[F[_], G[_]] = BoundedAPair[Any, F, G]

  /** Right universally quantified action of `F` on `G`. */
  type RightAction[G[_], F[_, _]] = Forall2[λ[(α, β) => (G[α], F[α, β]) => G[β]]]

  object RightAction {

    def fromLeft[G[_], F[_, _]](act: LeftAction[G, F]): RightAction[G, λ[(α, β) => F[β, α]]] =
      ν[RightAction[G, λ[(α, β) => F[β, α]]]][α, β]((g, f) => act.apply(f, g))

    def compose[F[_, _], A](implicit F: Compose[F]): RightAction[F[A, ?], F] =
      ν[RightAction[F[A, ?], F]][α, β]((fa, f) => F.compose(f, fa))
  }

  /** Left universally quantified action of `F` on `G`. */
  type LeftAction[G[_], F[_, _]] = Forall2[λ[(α, β) => (F[α, β], G[β]) => G[α]]]

  object LeftAction {

    def fromRight[G[_], F[_, _]](act: RightAction[G, F]): LeftAction[G, λ[(α, β) => F[β, α]]] =
      ν[LeftAction[G, λ[(α, β) => F[β, α]]]][α, β]((f, g) => act.apply(g, f))

    def compose[F[_, _], Z](implicit F: Compose[F]): LeftAction[F[?, Z], F] =
      ν[LeftAction[F[?, Z], F]][α, β]((f, fy) => F.compose(fy, f))
  }
}
