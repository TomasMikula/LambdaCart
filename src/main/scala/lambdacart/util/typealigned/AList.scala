package lambdacart.util.typealigned

import scala.annotation.tailrec
import lambdacart.util.~~>
import scalaz.{@@, \/, -\/, \/-, ~>, Category, Compose, Leibniz, Monoid, Tag}
import scalaz.Leibniz.===
import scalaz.Tags.{Conjunction, Disjunction}
import scalaz.std.anyVal._

/**
 * A potentially empty type-aligned list.
 */
sealed abstract class AList[F[_, _], A, B] {
  import AList._

  def ::[Z](fza: F[Z, A]): AList[F, Z, B] = ACons(fza, this)

  def +:[Z](fza: F[Z, A]): AList1[F, Z, B] = ACons1(fza, this)

  def :::[Z](that: AList[F, Z, A]): AList[F, Z, B] =
    that.reverse reverse_::: this

  def reverse: Composed[F, A, B] = {
    @tailrec def go(p: APair[AList[F, ?, B], Composed[F, A, ?]]): Composed[F, A, B] = {
      val (fs, acc) = (p._1, p._2)
      fs match {
        case ACons(h, t)  => go(APair.of[AList[F, ?, B], Composed[F, A, ?]](t, h :: acc))
        case nil @ ANil() => nil.subst[Composed[F, A, ?]](acc)
      }
    }
    go(APair.of[AList[F, ?, B], Composed[F, A, ?]](this, empty[λ[(α, β) => F[β, α]], A]))
  }

  def reverse_:::[Z](that: Composed[F, Z, A]): AList[F, Z, B] = {
    @tailrec def go[G[_, _]](p: APair[AList[G, ?, Z], Composed[G, B, ?]]): Composed[G, B, Z] = {
      val (gs, acc) = (p._1, p._2)
      gs match {
        case ACons(g, gs) => go(APair.of[AList[G, ?, Z], Composed[G, B, ?]](gs, g :: acc))
        case nil @ ANil() => nil.subst[Composed[G, B, ?]](acc)
      }
    }
    go[λ[(α, β) => F[β, α]]](APair.of[AList[λ[(α, β) => F[β, α]], ?, Z], Composed[λ[(α, β) => F[β, α]], B, ?]](that, this))
  }

  def foldLeft[G[_]](ga: G[A])(φ: RightAction[G, F]): G[B] = {
    @tailrec def go(p: APair[G, AList[F, ?, B]]): G[B] = {
      val (g, fs) = (p._1, p._2)
      fs match {
        case ACons(h, t)  => go(APair.of[G, AList[F, ?, B]](φ.apply(g, h), t))
        case nil @ ANil() => nil.subst(g)
      }
    }
    go(APair.of[G, AList[F, ?, B]](ga, this))
  }

  def foldLeftWhile[G[_], H[_]](ga: G[A])(φ: λ[α => APair[G, F[?, α]]] ~> λ[α => H[α] \/ G[α]]): APair[H, AList[F, ?, B]] \/ G[B] = {
    @tailrec def go(p: APair[G, AList[F, ?, B]]): APair[H, AList[F, ?, B]] \/ G[B] = {
      val (gx, lxb) = (p._1, p._2)
      lxb match {
        case c @ ACons(h, t) => φ(APair.of[G, F[?, c.Joint]](gx, h)) match {
          case \/-(gy) => go(APair.of[G, AList[F, ?, B]](gy, t))
          case -\/(hy) => -\/(APair.of[H, AList[F, ?, B]](hy, t))
        }
        case nil @ ANil() => \/-(nil.subst(gx))
      }
    }
    go(APair.of[G, AList[F, ?, B]](ga, this))
  }

  def foldRight[G[_]](gb: G[B])(φ: LeftAction[G, F]): G[A] =
    reverse.foldLeft(gb)(RightAction.fromLeft(φ))

  /**
   * Compose the elements of this list in a balanced binary fashion.
   */
  def fold(implicit F: Category[F]): F[A, B] =
    this match {
      case ACons(h, t)  => t.foldLeft[PostComposeBalancer[F, A, ?]](PostComposeBalancer(h))(PostComposeBalancer.rightAction).result
      case nil @ ANil() => nil.subst[F[A, ?]](F.id[A])
    }

  /**
   * Compose the elements of this list in a balanced binary fashion.
   */
  def foldOpt(implicit F: Compose[F]): AOption[F, A, B] =
    this match {
      case ACons(h, t)  => ASome(t.foldLeft[PostComposeBalancer[F, A, ?]](PostComposeBalancer(h))(PostComposeBalancer.rightAction).result)
      case nil @ ANil() => nil.subst[AOption[F, A, ?]](AOption.empty[F, A])
    }

  /**
   * Map and then compose the elements of this list in a balanced binary fashion.
   */
  def foldMap[G[_, _]](φ: F ~~> G)(implicit G: Category[G]): G[A, B] =
    this match {
      case ACons(h, t)  => t.foldLeft[PostComposeBalancer[G, A, ?]](PostComposeBalancer(φ.apply(h)))(PostComposeBalancer.rightAction(φ)).result
      case nil @ ANil() => nil.subst[G[A, ?]](G.id[A])
    }

  /**
   * Map and then compose the elements of this list in a balanced binary fashion.
   */
  def foldMapOpt[G[_, _]](φ: F ~~> G)(implicit G: Compose[G]): AOption[G, A, B] =
    this match {
      case ACons(h, t)  => ASome(t.foldLeft[PostComposeBalancer[G, A, ?]](PostComposeBalancer(φ.apply(h)))(PostComposeBalancer.rightAction(φ)).result)
      case nil @ ANil() => nil.subst[AOption[G, A, ?]](AOption.empty[G, A])
    }

  def map[G[_, _]](φ: F ~~> G): AList[G, A, B] =
    foldRight[AList[G, ?, B]](empty[G, B])(ν[LeftAction[AList[G, ?, B], F]][α, β]((f, gs) => φ.apply(f) :: gs))

  def flatMap[G[_, _]](φ: F ~~> AList[G, ?, ?]): AList[G, A, B] =
    foldRight[AList[G, ?, B]](empty[G, B])(ν[LeftAction[AList[G, ?, B], F]][α, β]((f, gs) => φ.apply(f) ::: gs))

  def sum[M](φ: F ~~> λ[(α, β) => M])(implicit M: Monoid[M]): M =
    foldMap[λ[(α, β) => M]](φ)(M.category)

  def all(p: F ~~> λ[(α, β) => Boolean]): Boolean = {
    val q = Tag.subst[Boolean, λ[b => F ~~> λ[(α, β) => b]], Conjunction](p)
    Tag.unwrap(sum[Boolean @@ Conjunction](q))
  }

  def exists(p: F ~~> λ[(α, β) => Boolean]): Boolean = {
    val q = Tag.subst[Boolean, λ[b => F ~~> λ[(α, β) => b]], Disjunction](p)
    Tag.unwrap(sum[Boolean @@ Disjunction](q))
  }

  def filterNot(p: F ~~> λ[(α, β) => Option[α === β]]): AList[F, A, B] = {
    @tailrec def go[X](revAcc: Composed[F, A, X], fs: AList[F, X, B]): AList[F, A, B] =
      fs match {
        case ACons(h, t) => p.apply(h) match {
          case Some(ev) => go(ev.subst[Composed[F, A, ?]](revAcc), t)
          case None     => go(h :: revAcc, t)
        }
        case nil @ ANil() => nil.subst[Composed[F, A, ?]](revAcc).reverse
      }

    go(AList.empty[Op[F, ?, ?], A], this)
  }

  def size: Int = {
    @tailrec def go(acc: Int, fs: AList[F, _, _]): Int = fs match {
      case ACons(_, t) => go(acc + 1, t)
      case ANil()      => acc
    }
    go(0, this)
  }
}

final case class ACons[F[_, _], A, X, B](head: F[A, X], tail: AList[F, X, B]) extends AList[F, A, B] {
  final type Joint = X
}

sealed abstract case class ANil[F[_, _], A, B]() extends AList[F, A, B] {
  def   subst[G[_]](ga: G[A]): G[B]
  def unsubst[G[_]](gb: G[B]): G[A]
  def leibniz: A === B = subst[A === ?](Leibniz.refl[A])
}

object AList {

  type Op[F[_, _], A, B] = F[B, A]
  type Composed[F[_, _], A, B] = AList[Op[F, ?, ?], B, A]

  def apply[F[_, _], A](): AList[F, A, A] = empty
  def apply[F[_, _], A, B](f: F[A, B]): AList[F, A, B] = f :: empty
  def empty[F[_, _], A]: AList[F, A, A] = Nil.asInstanceOf[AList[F, A, A]]

  private val Nil = nil[Nothing, Nothing]
  private def nil[F[_, _], A]: ANil[F, A, A] = new ANil[F, A, A] {
    def   subst[G[_]](ga: G[A]): G[A] = ga
    def unsubst[G[_]](gb: G[A]): G[A] = gb
  }
}
