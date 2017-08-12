package lambdacart.util.typealigned

import lambdacart.util.~~>
import scalaz.{\/, \/-, ~>, Category, Monoid}

/**
 * A potentially empty type-aligned list.
 */
final class AList[F[_, _], A, B] private (val uncons: AOption[AList1[F, ?, ?], A, B]) extends AnyVal {
  import AList._

  def ::[Z](fza: F[Z, A]): AList1[F, Z, B] =
    uncons match {
      case ANone(ev)   => ev.subst[AList1[F, Z, ?]](AList1(fza))
      case ASome(list) => fza :: list
    }

  def +:[Z](fza: F[Z, A]): AList[F, Z, B] = (fza :: this).toList

  def :::[Z](that: AList[F, Z, A]): AList[F, Z, B] =
    uncons match {
      case ANone(ev)   => ev.subst[AList[F, Z, ?]](that)
      case ASome(list) => AList(that ::: list)
    }

  def reverse: Composed[F, A, B] =
    uncons match {
      case ANone(ev)   => ev.subst[AList[Op[F, ?, ?], ?, A]](empty[Op[F, ?, ?], A])
      case ASome(list) => AList[Op[F, ?, ?], B, A](list.reverse)
    }

  def foldLeft[G[_]](ga: G[A])(φ: RightAction[G, F]): G[B] =
    uncons match {
      case ANone(ev)   => ev.subst(ga)
      case ASome(list) => list.foldLeft(ga)(φ)
    }

  def foldLeftWhile[G[_], H[_]](ga: G[A])(tr: λ[α => APair[G, F[?, α]]] ~> λ[α => H[α] \/ G[α]]): APair[H, AList[F, ?, B]] \/ G[B] =
    uncons match {
      case ANone(ev)   => \/-(ev.subst(ga))
      case ASome(list) => list.foldLeftWhile(ga)(tr)
    }

  def foldRight[G[_]](gb: G[B])(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft(gb)(RightAction.fromLeft(φ))

  /**
   * Compose the elements of this list in a balanced binary fashion.
   */
  def fold(implicit F: Category[F]): F[A, B] =
    uncons match {
      case ASome(list) => list.fold
      case ANone(ev)   => ev.subst[F[A, ?]](F.id[A])
    }

  /**
   * Map and then compose the elements of this list in a balanced binary fashion.
   */
  def foldMap[G[_, _]](φ: F ~~> G)(implicit G: Category[G]): G[A, B] =
    uncons match {
      case ASome(list) => list.foldMap(φ)
      case ANone(ev)   => ev.subst[G[A, ?]](G.id[A])
    }

  def map[G[_, _]](φ: F ~~> G): AList[G, A, B] =
    uncons match {
      case ASome(list) => AList(list.map(φ))
      case ANone(ev)   => ev.subst[AList[G, A, ?]](empty[G, A])
    }

  def flatMap[G[_, _]](φ: F ~~> AList[G, ?, ?]): AList[G, A, B] =
    foldRight[AList[G, ?, B]](empty[G, B])(ν[LeftAction[AList[G, ?, B], F]][α, β]((f, acc) => φ.apply(f) ::: acc))

  def sum[M](φ: F ~~> λ[(α, β) => M])(implicit M: Monoid[M]): M =
    foldMap[λ[(α, β) => M]](φ)(M.category)
}

object AList {

  type Op[F[_, _], A, B] = F[B, A]
  type Composed[F[_, _], A, B] = AList[Op[F, ?, ?], B, A]

  def apply[F[_, _], A, B](l: AList1[F, A, B]): AList[F, A, B] = new AList(ASome(l))
  def apply[F[_, _], A](): AList[F, A, A] = empty
  def empty[F[_, _], A]: AList[F, A, A] = new AList[F, A, A](AOption.empty)
}
