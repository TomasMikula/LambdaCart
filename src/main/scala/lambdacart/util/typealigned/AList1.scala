package lambdacart.util.typealigned

import lambdacart.util.~~>
import scalaz.{-\/, \/, \/-, ~>, Compose, Semigroup}


/**
 * Type-aligned list with at least 1 element.
 * Example:
 *
 * {{{
 * F[A, X], F[X, Y], F[Y, Z], F[Z, B]
 * }}}
 */
sealed abstract class AList1[F[_, _], A, B] {
  import AList1._

  type A1

  def head: F[A, A1]
  def tail: AList[F, A1, B]

  def ::[Z](fza: F[Z, A]): AList1[F, Z, B] =
    ACons1(fza, this.toList)

  def uncons: Either[F[A, B], APair[F[A, ?], AList1[F, ?, B]]] =
    tail match {
      case ev @ ANil() => Left(ev.subst[F[A, ?]](head))
      case ACons(h, t) => Right(APair.of[F[A, ?], AList1[F, ?, B]](head, ACons1(h, t)))
    }

  def uncons1: APair[F[A, ?], AList[F, ?, B]] =
    APair.of[F[A, ?], AList[F, ?, B]](head, tail)

  def unsnoc: Either[F[A, B], APair[AList1[F, A, ?], F[?, B]]] =
    reverse.uncons match {
      case Left(f)  => Left(f)
      case Right(p) => Right(APair.of[AList1[F, A, ?], F[?, B]](p._2.reverse, p._1))
    }

  def unsnoc1: APair[AList[F, A, ?], F[?, B]] = {
    val p = reverse.uncons1
    APair.of[AList[F, A, ?], F[?, B]](p._2.reverse, p._1)
  }

  def :::[Z](that: AList1[F, Z, A]): AList1[F, Z, B] =
    that.reverse reverse_::: this

  def reverse_:::[Z](that: Composed1[F, Z, A]): AList1[F, Z, B] =
    that.toList reverse_::: this

  def reverse_:::[Z](that: AList.Composed[F, Z, A]): AList1[F, Z, B] =
    (that reverse_::: this.toList) match {
      case ACons(h, t) => ACons1(h, t)
      case ANil()      => sys.error("unreachable code")
    }

  def :::[Z](that: AList[F, Z, A]): AList1[F, Z, B] =
    (that ::: this.toList) match {
      case ACons(h, t) => ACons1(h, t)
      case ANil()      => sys.error("unreachable code")
    }

  def ++[C](that: AList1[F, B, C]): AList1[F, A, C] =
    this ::: that

  def :+[C](f: F[B, C]): AList1[F, A, C] =
    this ::: AList1(f)

  def reverse: Composed1[F, A, B] = 
    tail reverse_::: AList1[λ[(α, β) => F[β, α]], A1, A](head)

  def foldLeft[G[_]](ga: G[A])(φ: RightAction[G, F]): G[B] =
    tail.foldLeft[G](φ.apply(ga, head))(φ)

  def foldLeft1[G[_]](init: F[A, ?] ~> G)(φ: RightAction[G, F]): G[B] =
    tail.foldLeft[G](init.apply(head))(φ)

  def foldLeftWhile[G[_], H[_]](ga: G[A])(tr: λ[α => APair[G, F[?, α]]] ~> λ[α => H[α] \/ G[α]]): APair[H, AList[F, ?, B]] \/ G[B] =
    tr.apply(APair.of[G, F[?, A1]](ga, head)) match {
      case \/-(ga1) => tail.foldLeftWhile[G, H](ga1)(tr)
      case -\/(ha1) => -\/(APair.of[H, AList[F, ?, B]](ha1, tail))
    }

  def foldRight[G[_]](gb: G[B])(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft(gb)(RightAction.fromLeft(φ))

  def foldRight1[G[_]](init: F[?, B] ~> G)(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft1[G](init)(RightAction.fromLeft(φ))

  /**
   * Compose the elements of this list in a balanced binary fashion.
   */
  def fold(implicit F: Compose[F]): F[A, B] =
    tail.foldLeft[PostComposeBalancer[F, A, ?]](PostComposeBalancer(head))(PostComposeBalancer.rightAction).result

  /**
   * Map and then compose the elements of this list in a balanced binary fashion.
   */
  def foldMap[G[_, _]](φ: F ~~> G)(implicit G: Compose[G]): G[A, B] =
    tail.foldLeft[PostComposeBalancer[G, A, ?]](PostComposeBalancer(φ.apply(head)))(PostComposeBalancer.rightAction(φ)).result

  def map[G[_, _]](φ: F ~~> G): AList1[G, A, B] =
    ACons1(φ.apply(head), tail.map(φ))

  def flatMap[G[_, _]](φ: F ~~> AList1[G, ?, ?]): AList1[G, A, B] =
    foldRight1[AList1[G, ?, B]](λ[F[?, B] ~> AList1[G, ?, B]](φ.apply(_)))(ν[LeftAction[AList1[G, ?, B], F]][α, β]((f, gs) => φ.apply(f) ::: gs))

  def sum[S](φ: F ~~> λ[(α, β) => S])(implicit S: Semigroup[S]): S =
    foldMap[λ[(α, β) => S]](φ)(S.compose)

  def all(p: F ~~> λ[(α, β) => Boolean]): Boolean =
    p.apply(head) && tail.all(p)

  def exists(p: F ~~> λ[(α, β) => Boolean]): Boolean =
    p.apply(head) || tail.exists(p)

  def size: Int = 1 + tail.size

  def toList: AList[F, A, B] = head :: tail

  def mkString(prefix: String, delim: String, suffix: String)(show: F[_, _] => String): String = {
    val sb = new StringBuilder(prefix)
    foldLeft1[λ[α => StringBuilder]](λ[F[A, ?] ~> λ[α => StringBuilder]](f => sb.append(show(f))))(ν[RightAction[λ[α => StringBuilder], F]][α, β]((buf, f) => buf.append(delim).append(show(f)))).append(suffix).toString
  }

  override def toString: String = mkString("AList1(", ", ", ")")(_.toString)
}

final case class ACons1[F[_, _], A, X, B](head: F[A, X], tail: AList[F, X, B]) extends AList1[F, A, B] {
  type A1 = X
}

object AList1 {
  /**
   * Reversed type-aligned list is type-aligned with flipped type constructor.
   * For example, when we reverse
   *
   * {{{
   * A => B, B => C, C => D, D => E
   * }}}
   *
   * we get
   *
   * {{{
   * D => E, C => D, B => C, A => B
   * }}}
   *
   * which is type-aligned if we flip the arrows:
   *
   * {{{
   * E <= D, D <= C, C <= B, B <= A
   * }}}
   *
   * The first list has type `AList1[=>, A, E]`, while
   * the reversed list has type `Composed1[=>, A, E]`.
   */
  type Composed1[F[_, _], A, B] = AList1[λ[(α, β) => F[β, α]], B, A]

  def apply[F[_, _], A, B](f: F[A, B]): AList1[F, A, B] = ACons1(f, AList.empty)
  def op[F[_, _], A, B](f: F[A, B]): Composed1[F, A, B] = apply[λ[(α, β) => F[β, α]], B, A](f)
}
