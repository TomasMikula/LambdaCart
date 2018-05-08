package lambdacart

import scalaz.{@@, Leibniz, Writer}
import scalaz.Leibniz.===
import scalaz.Tags.Disjunction

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
    def lift2[F[_,_]]: Lift2[F] = Lift2()

    case class Lift2[F[_,_]]() {
      def apply[A, B](implicit ev1: A === B): F[X, A] === F[Y, B] =
        ev.subst[λ[x => F[X, A] === F[x, B]]](
          ev1.subst[λ[a => F[X, A] === F[X, a]]](Leibniz.refl))
    }
  }

  type Improvement[A] = Writer[Boolean @@ Disjunction, A]
  object Improvement {
    def improved[A](a: A) = Writer(Disjunction(true), a)
    def unchanged[A](a: A) = Writer(Disjunction(false), a)
    implicit class ImprovementOps[A](i: Improvement[A]) {
      def getImproved: Option[A] = if(Disjunction.unwrap(i.run._1)) Some(i.run._2) else None
    }
  }
}
