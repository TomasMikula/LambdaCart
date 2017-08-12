package lambdacart.util.typealigned

import scala.annotation.tailrec
import scalaz.Compose

/**
 * `FreeCompose` is a non-empty type-aligned sequence represented
 * as a (non-balanced) binary tree, in order to support O(1) addition
 * to either side and O(1) concatenation.
 */
sealed abstract class FreeCompose[=>:[_, _], A, B] {
  import FreeCompose._

  def compose[Z](that: FreeCompose[=>:, Z, A]): FreeCompose[=>:, Z, B] =
    Chain(that, this)

  def <<<[Z](that: FreeCompose[=>:, Z, A]): FreeCompose[=>:, Z, B] =
    this compose that

  def >>>[C](that: FreeCompose[=>:, B, C]): FreeCompose[=>:, A, C] =
    that compose this

  def :+[C](f: B =>: C): FreeCompose[=>:, A, C] =
    Chain(this, Lift(f))

  def +:[Z](f: Z =>: A): FreeCompose[=>:, Z, B] =
    Chain(Lift(f), this)

  final def foldLeft[F[_]](fa: F[A])(φ: RightAction[F, =>:]): F[B] = {
    @inline def pair[X](fx: F[X], f: FreeCompose[=>:, X, B]) = APair[F, FreeCompose[=>:, ?, B], X](fx, f)
    @tailrec def go(step: APair[F, FreeCompose[=>:, ?, B]]): F[B] =
      step._2 match {
        case Chain(Chain(f, g), h) => go(pair(step._1, f >>> (g >>> h)))
        case Chain(Lift(f), g) => go(pair(φ.apply(step._1, f), g))
        case Lift(f) => φ.apply(step._1, f)
      }
    go(pair(fa, this))
  }

  def foldRight[F[_]](fb: F[B])(φ: LeftAction[F, =>:]): F[A] = {
    @inline def pair[X](f: FreeCompose[=>:, A, X], fx: F[X]) = APair[FreeCompose[=>:, A, ?], F, X](f, fx)
    @tailrec def go(step: APair[FreeCompose[=>:, A, ?], F]): F[A] =
      step._1 match {
        case Chain(f, Chain(g, h)) => go(pair((f >>> g) >>> h, step._2))
        case Chain(f, Lift(g)) => go(pair(f, φ.apply(g, step._2)))
        case Lift(f) => φ.apply(f, step._2)
      }
    go(pair(this, fb))
  }

  /**
   * Compose the leafs in a balanced binary fashion.
   */
  @tailrec
  final def reduce(implicit ev: Compose[=>:]): A =>: B = this match {
    case Chain(Chain(f, g), h) => (f >>> (g >>> h)).reduce
    case Chain(Lift(f), g) => g.foldLeft[PostComposeBalancer[=>:, A, ?]](PostComposeBalancer(f))(PostComposeBalancer.rightAction).result
    case Lift(f) => f
  }
}

object FreeCompose {
  private[FreeCompose] final case class Lift[=>:[_, _], A, B](f: A =>: B) extends FreeCompose[=>:, A, B]
  private[FreeCompose] final case class Chain[=>:[_, _], A, B, C](f: FreeCompose[=>:, A, B], g: FreeCompose[=>:, B, C]) extends FreeCompose[=>:, A, C]

  def lift[F[_, _], A, B](f: F[A, B]): FreeCompose[F, A, B] =
    Lift(f)
}
