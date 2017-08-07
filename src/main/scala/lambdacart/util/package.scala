package lambdacart

import scalaz.Leibniz
import scalaz.Leibniz.===

/** This package contains auxiliary things that are needed,
  * but are not the focus of this project, and are not found
  * in a suitable form elsewhere.
  */
package object util {
  /** A function universally quantified  in two variables
    * Isomorphic to `scalaz.~~>` (`BiNaturalTransformation`),
    * but this formulation admits more concise syntax via
    * P∀scal (https://github.com/TomasMikula/pascal).
    */
  type ~~>[F[_, _], G[_, _]] = Forall2[λ[(A, B) => F[A, B] => G[A, B]]]
  object ~~> {
    def identity[F[_, _]]: F ~~> F =
      Λ[A, B](fab => fab): F ~~> F
  }

  implicit class LeibnizOps[X, Y](ev: X === Y) {
    def lift[F[_]]: F[X] === F[Y] = ev.subst[λ[α => F[X] === F[α]]](Leibniz.refl)
  }
}
