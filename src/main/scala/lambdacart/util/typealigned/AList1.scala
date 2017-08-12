package lambdacart.util.typealigned

import lambdacart.util.~~>
import scala.annotation.tailrec
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
    ACons(fza, this)

  def uncons: Either[F[A, B], APair[F[A, ?], AList1[F, ?, B]]] =
    this match {
      case AJust(f) => Left(f)
      case ACons(h, t) => Right(APair.of[F[A, ?], AList1[F, ?, B]](h, t))
    }

  def :::[Z](that: AList1[F, Z, A]): AList1[F, Z, B] =
    that.reverse reverse_::: this

  def reverse_:::[Z](that: Composed1[F, Z, A]): AList1[F, Z, B] = {
    @inline def pair[X](rev: Composed1[F, Z, X], fs: AList1[F, X, B]) =
      APair[Composed1[F, Z, ?], AList1[F, ?, B], X](rev, fs)

    @tailrec def go(p: APair[Composed1[F, Z, ?], AList1[F, ?, B]]): AList1[F, Z, B] = {
      val (rev, fs) = (p._1, p._2)
      rev.uncons match {
        case Left(f) => f :: fs
        case Right(ht) => go(pair(ht._2, ht._1 :: fs))
      }
    }

    go(pair(that, this))
  }

  def :::[Z](that: AList[F, Z, A]): AList1[F, Z, B] =
    that.uncons match {
      case ANone(ev) => ev.flip.subst[AList1[F, ?, B]](this)
      case ASome(list) => list ::: this
    }

  def ++[C](that: AList1[F, B, C]): AList1[F, A, C] =
    this ::: that

  def reverse: Composed1[F, A, B] = {
    @inline def pair[X](acc: Composed1[F, A, X], fs: AList1[F, X, B]) =
      APair[Composed1[F, A, ?], AList1[F, ?, B], X](acc, fs)

    @tailrec def go(p: APair[Composed1[F, A, ?], AList1[F, ?, B]]): Composed1[F, A, B] = {
      val (acc, fs) = (p._1, p._2)
      fs match {
        case AJust(f) => f :: acc
        case ACons(h, t) => go(pair(h :: acc, t))
      }
    }

    this match {
      case AJust(f) => AList1.op[F, A, B](f)
      case ACons(h, t) => go(pair(AList1.op(h), t))
    }
  }

  def foldLeft[G[_]](ga: G[A])(φ: RightAction[G, F]): G[B] = {
    @inline def pair[X](gx: G[X], fb: AList1[F, X, B]) =
      APair[G, AList1[F, ?, B], X](gx, fb)

    @tailrec def go(p: APair[G, AList1[F, ?, B]]): G[B] = {
      val (gx, fs) = (p._1, p._2)
      fs match {
        case AJust(f) => φ.apply(gx, f)
        case ACons(f, g) => go(pair(φ.apply(gx, f), g))
      }
    }

    go(pair(ga, this))
  }

  def foldLeft1[G[_]](init: F[A, ?] ~> G)(φ: RightAction[G, F]): G[B] =
    this match {
      case AJust(f)     => init(f)
      case ACons(f, fs) => fs.foldLeft[G](init(f))(φ)
    }

  def foldLeftWhile[G[_], H[_]](ga: G[A])(tr: λ[α => APair[G, F[?, α]]] ~> λ[α => H[α] \/ G[α]]): APair[H, AList[F, ?, B]] \/ G[B] = {
    @inline def pair[X](gx: G[X], fb: AList1[F, X, B]) =
      APair[G, AList1[F, ?, B], X](gx, fb)

    @tailrec def go(p: APair[G, AList1[F, ?, B]]): APair[H, AList[F, ?, B]] \/ G[B] = {
      val (gx, fs) = (p._1, p._2)
      fs match {
        case AJust(f) => tr[B](APair[G, F[?, B], p.A](gx, f)) match {
          case -\/(hb) => -\/(APair[H, AList[F, ?, B], B](hb, AList.empty[F, B]))
          case \/-(gb) => \/-(gb)
        }
        case fs @ ACons(f, gs) => tr(APair[G, F[?, fs.A1], p.A](gx, f)) match {
          case -\/(hy) => -\/(APair[H, AList[F, ?, B], fs.A1](hy, gs.toList))
          case \/-(gy) => go(pair(gy, gs))
        }
      }
    }

    go(pair(ga, this))
  }

  def foldRight[G[_]](gb: G[B])(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft(gb)(RightAction.fromLeft(φ))

  def foldRight1[G[_]](init: F[?, B] ~> G)(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft1[G](init)(RightAction.fromLeft(φ))

  /**
   * Compose the elements of this list in a balanced binary fashion.
   */
  def fold(implicit F: Compose[F]): F[A, B] =
    this match {
      case ACons(f, g) => g.foldLeft[PostComposeBalancer[F, A, ?]](PostComposeBalancer(f))(PostComposeBalancer.rightAction).result
      case AJust(f) => f
    }

  /**
   * Map and then compose the elements of this list in a balanced binary fashion.
   */
  def foldMap[G[_, _]](φ: F ~~> G)(implicit G: Compose[G]): G[A, B] =
    this match {
      case ACons(f, fs) => fs.foldLeft[PostComposeBalancer[G, A, ?]](PostComposeBalancer(φ.apply(f)))(PostComposeBalancer.rightAction(φ)).result
      case AJust(f)     => φ.apply(f)
    }

  def map[G[_, _]](φ: F ~~> G): AList1[G, A, B] =
    this match {
      case AJust(f)     => AJust(φ.apply(f))
      case ACons(f, fs) => fs.foldLeft[Composed1[G, A, ?]](AList1.op(φ.apply(f)))(AList1.opConsMapAction(φ)).reverse
    }

  def flatMap[G[_, _]](φ: F ~~> AList1[G, ?, ?]): AList1[G, A, B] =
    this match {
      case AJust(f)     => φ.apply(f)
      case ACons(f, fs) => fs.foldLeft[Composed1[G, A, ?]](φ.apply(f).reverse)(ν[RightAction[Composed1[G, A, ?], F]][α, β]((acc, f) => φ.apply(f) reverse_::: acc)).reverse
    }

  def sum[S](φ: F ~~> λ[(α, β) => S])(implicit S: Semigroup[S]): S =
    foldMap[λ[(α, β) => S]](φ)(S.compose)

  def toList: AList[F, A, B] = AList(this)
}

final case class AJust[F[_, _], A, B](value: F[A, B]) extends AList1[F, A, B] {
  type A1 = B
  def head = value
  def tail = AList.empty
}

final case class ACons[F[_, _], A, B, C](head: F[A, B], tail1: AList1[F, B, C]) extends AList1[F, A, C] {
  type A1 = B
  def tail = tail1.toList
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

  def apply[F[_, _], A, B](f: F[A, B]): AList1[F, A, B] = AJust(f)
  def op[F[_, _], A, B](f: F[A, B]): Composed1[F, A, B] = apply[λ[(α, β) => F[β, α]], B, A](f)

  def consAction[F[_, _], B]: LeftAction[AList1[F, ?, B], F] =
    ν[LeftAction[AList1[F, ?, B], F]][α, β]((f, fs) => f :: fs)

  def consMapAction[G[_, _], F[_, _], B](φ: F ~~> G): LeftAction[AList1[G, ?, B], F] =
    ν[LeftAction[AList1[G, ?, B], F]][α, β]((f, gs) => φ.apply(f) :: gs)

  def opConsAction[F[_, _], A]: RightAction[Composed1[F, A, ?], F] =
    ν[RightAction[Composed1[F, A, ?], F]][α, β]((fs, f) => f :: fs)

  def opConsMapAction[G[_, _], F[_, _], A](φ: F ~~> G): RightAction[Composed1[G, A, ?], F] =
    ν[RightAction[Composed1[G, A, ?], F]][α, β]((gs, f) => φ.apply(f) :: gs)
}
