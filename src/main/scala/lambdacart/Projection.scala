package lambdacart

import lambdacart.util.{Exists, Improvement, LeibnizOps}
import lambdacart.util.Improvement._
import lambdacart.util.typealigned.{A2Pair, ACons, AList, ANil, APair}
import scalaz.{Either3, Left3, Middle3, Right3, Leibniz}
import scalaz.Leibniz.===
import scalaz.std.anyVal._

/**
 * Represents projection from a data type,
 * i.e. forgetting some part of the data.
 *
 * During program optimization pushed to the front, i.e. as early
 * as possible. (Don't carry around something only to ignore it later;
 * ignore as soon as possible.)
 */
sealed trait Projection[**[_,_], T, A, B] {
  import Projection._

  type Prj[X, Y] = Projection[**, T, X, Y]
  type Visitor[R] = Projection.Visitor[**, T, A, B, R]
  type VisitorNT[R] = Projection.VisitorNT[**, T, A, B, R]
  type OptVisitor[R] = Projection.OptVisitor[**, T, A, B, R]

  def visit[R](v: Visitor[R]): R

  def switchTerminal: (T === B) Either NonTerminal[**, T, A, B]

  def castA[C](implicit ev: C === A): Prj[C, B] = ev.flip.subst[Prj[?, B]](this)
  def castB[C](implicit ev: B === C): Prj[A, C] = ev.subst[Prj[A, ?]](this)

  def andThen[C](that: Prj[B, C]): Prj[A, C] =
    this.switchTerminal match {
      case Left(ev) => Unit().castB(that.unital(ev.flip).flip)
      case Right(thiz) =>
        that.switchTerminal match {
          case Left(ev) => Unit[**, T, A].castB(ev)
          case Right(that) => thiz andThenNT that
        }
    }

  def after[Z](that: Prj[Z, A]): Prj[Z, B] =
    that andThen this

  def prependTo[:->:[_,_], H[_,_], C](f: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    f compose this.toFreeCCC

  def appendTo[:->:[_,_], H[_,_], A0](f: FreeCCC[:->:, **, T, H, A0, A]): FreeCCC[:->:, **, T, H, A0, B] =
    f andThen this.toFreeCCC

  def unital(implicit ev: A === T): B === T =
    visit(new Visitor[B === T] {
      def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)) = sys.error("impossible")
      def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)) = sys.error("impossible")
      def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) =
        sys.error("impossible")
      def apply(p: Unit[A])(implicit ev1: T === B) = ev1.flip
      def apply(p: Id[A])(implicit ev1: A === B) = ev1.flip andThen ev
      def apply[X](p: AndThen[A, X, B]) = p.q.unital(p.p.unital)
    })

  def isUnit: Option[B === T] =
    visit(new OptVisitor[B === T] {
      override def apply(p: Unit[A])(implicit ev: T === B) = Some(ev.flip)
    })

  final def isId: Option[A === B] =
    visit(new OptVisitor[A === B] {
      override def apply(p: Id[A])(implicit ev: A === B) = Some(ev)
    })

  def size: Int = visit(new Visitor[Int] {
    def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)) = 1
    def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)) = 1
    def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) = 1 + p.p1.size + p.p2.size
    def apply(p: Unit[A])(implicit ev: T === B) = 1
    def apply(p: Id[A])(implicit ev: A === B) = 1
    def apply[X](p: AndThen[A, X, B]) = 1 + p.p.size + p.q.size
  })

  def toFreeCCC[:=>:[_,_], :->:[_,_]]: FreeCCC[:=>:, **, T, :->:, A, B] =
    visit(new Visitor[FreeCCC[:=>:, **, T, :->:, A, B]] {
      def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)) = FreeCCC.fst[:=>:, **, T, :->:, B, Y].castA
      def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)) = FreeCCC.snd[:=>:, **, T, :->:, X, B].castA
      def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) =
        FreeCCC.parallel(p.p1.toFreeCCC[:=>:, :->:], p.p2.toFreeCCC[:=>:, :->:]).castA[A].castB
      def apply(p: Unit[A])(implicit ev: T === B) = FreeCCC.terminal[:=>:, **, T, :->:, A].castB
      def apply(p: Id[A])(implicit ev: A === B) = FreeCCC.id[:=>:, **, T, :->:, A].castB
      def apply[X](p: AndThen[A, X, B]) = FreeCCC.andThen(p.p.toFreeCCC, p.q.toFreeCCC)
    })

  /** Greatest common prefix of this projection and that projection. */
  final def gcd[C](that: Prj[A, C]): APair[Prj[A, ?], λ[a => (Prj[a, B], Prj[a, C])]] = {
    def ret[X](p: Prj[A, X], q: Prj[X, B], r: Prj[X, C]) =
      APair[Prj[A, ?], λ[a => (Prj[a, B], Prj[a, C])], X](p, (q, r))

    (this.switchTerminal, that.switchTerminal) match {
      case (Left(ev1), Left(ev2)) => ret(Unit(), Id().castB(ev1), Id().castB(ev2))
      case (Left(ev1), Right(p2)) => ret(p2, Unit().castB(ev1), Id())
      case (Right(p1), Left(ev2)) => ret(p1, Id(), Unit().castB(ev2))
      case (Right(p1), Right(p2)) =>
        val r = p1 gcdNT p2
        ret(r._1, r._2._1, r._2._2)
    }
  }

  def ignoresSnd[X, Y](implicit ev: A === (X ** Y)): Option[Prj[X, B]] =
    switchTerminal match {
      case Left(ev) => Some(Unit().castB(ev))
      case Right(p) => p.split[X, Y] match {
        case Left3(p1) => Some(p1)
        case _         => None
      }
    }

  def ignoresFst[X, Y](implicit ev: A === (X ** Y)): Option[Prj[Y, B]] =
    switchTerminal match {
      case Left(ev) => Some(Unit().castB(ev))
      case Right(p) => p.split[X, Y] match {
        case Right3(p2) => Some(p2)
        case _          => None
      }
    }

  private[Projection] implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
    def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
    def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
  }
}

object Projection {

  sealed trait NonTerminal[**[_,_], T, A, B] extends Projection[**, T, A, B] {
    def visitNT[R](v: VisitorNT[R]): R

    final override def visit[R](v: Visitor[R]): R = visitNT(v)

    def andThenNT[C](that: NonTerminal[**, T, B, C]): NonTerminal[**, T, A, C] =
      (this.isId map {
        ev => that.castA(ev)
      }) orElse (that.isId map {
        ev => this.castB(ev)
      }) orElse this.visit(new this.OptVisitor[NonTerminal[**, T, A, C]] {
        // TODO handle anything ending in product type, not just Par
        override def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit
            ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) =
          that.split[B1, B2](ev2.flip) match {
            case Left3(q)   => Some(Fst[A1, A2].castA[A] andThenNT p.p1 andThenNT q)
            case Right3(q)  => Some(Snd[A1, A2].castA[A] andThenNT p.p2 andThenNT q)
            case Middle3(_) => None
          }
      }) getOrElse (
        AndThen(this, that)
      )

    final def gcdNT[C](that: NonTerminal[**, T, A, C]): APair[NonTerminal[**, T, A, ?], λ[a => (NonTerminal[**, T, a, B], NonTerminal[**, T, a, C])]] = {
      type τ[X, Y] = NonTerminal[**, T, X, Y]

      def ret[X, P, Y, Z](p: τ[X, P], q1: τ[P, Y], q2: τ[P, Z]) =
        APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])], P](p, (q1, q2))

      def flipRet[X, Y, Z](r: APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]): APair[τ[X, ?], λ[a => (τ[a, Z], τ[a, Y])]] =
        APair.of[τ[X, ?], λ[a => (τ[a, Z], τ[a, Y])]](r._1, (r._2._2, r._2._1))

      def seq[X, Y](ps: AList[τ, X, Y]): τ[X, Y] = ps match {
        case ev @ ANil() => Id[**, T, X].castB(ev.leibniz)
        case ACons(h, t) => h andThenNT seq(t)
      }

      def go[X, Y, Z](ps: AList[τ, X, Y], qs: AList[τ, X, Z]): APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]] =
        ps match {
          case ev @ ANil() => ret(Id[**, T, X], Id[**, T, X].castB(ev.leibniz), seq(qs))
          case ps @ ACons(ph, pt) => qs match {
            case ev @ ANil() => ret(Id[**, T, X], seq(ps), Id[**, T, X].castB(ev.leibniz))
            case qs @ ACons(qh, qt) =>
              ph.visit(new ph.Visitor[APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]] {
                def apply(p: Unit[X])(implicit ev: T === ps.Joint) = sys.error("NonTerminal cannot be Unit")
                def apply(p: Id[X])(implicit ev: X === ps.Joint) = go[X, Y, Z](ev.flip.subst[AList[τ, ?, Y]](pt), qs)
                def apply[P](p: AndThen[X, P, ps.Joint]) = go(p.p :: p.q :: pt, qs)
                def apply[Q](p: Fst[ps.Joint, Q])(implicit ev: X === (ps.Joint ** Q)) =
                  qh.visit(new qh.Visitor[APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]] {
                    def apply(q: Unit[X])(implicit ev: T === qs.Joint) = sys.error("NonTerminal cannot be Unit")
                    def apply(q: Id[X])(implicit ev: X === qs.Joint) = go[X, Y, Z](ps, ev.flip.subst[AList[τ, ?, Z]](qt))
                    def apply[U](q: AndThen[X, U, qs.Joint]) = go(ps, q.p :: q.q :: qt)
                    def apply[V](q: Fst[qs.Joint, V])(implicit ev: X === (qs.Joint ** V)) = {
                      val r = go[qs.Joint, Y, Z](pt, qt) // compiler bug that this passes without casting pt
                      ret(Fst[qs.Joint, V].castA[X] andThenNT r._1, r._2._1, r._2._2)
                    }
                    def apply[U](q: Snd[U, qs.Joint])(implicit ev1: X === (U ** qs.Joint)) = {
                      implicit val ev2: X === (ps.Joint ** qs.Joint) = (ev.flip andThen ev1).snd.subst[λ[q => X === (ps.Joint ** q)]](ev)
                      ret[X, Y ** Z, Y, Z](par(seq(pt), seq(qt)).castA[X], Fst[Y, Z], Snd[Y, Z])
                    }
                    def apply[A1, A2, B1, B2](q: Par[A1, A2, B1, B2])(implicit ev1: X === (A1 ** A2), ev2: (B1 ** B2) === qs.Joint) =
                      flipRet(go(qs, ps))
                  })
                def apply[P](p: Snd[P, ps.Joint])(implicit ev: X === (P ** ps.Joint)) =
                  qh.visit(new qh.Visitor[APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]] {
                    def apply(q: Unit[X])(implicit ev: T === qs.Joint) = sys.error("NonTerminal cannot be Unit")
                    def apply(q: Id[X])(implicit ev: X === qs.Joint) = go[X, Y, Z](ps, ev.flip.subst[AList[τ, ?, Z]](qt))
                    def apply[U](q: AndThen[X, U, qs.Joint]) = go(ps, q.p :: q.q :: qt)
                    def apply[V](q: Fst[qs.Joint, V])(implicit ev1: X === (qs.Joint ** V)) = {
                      implicit val ev2: X === (qs.Joint ** ps.Joint) = (ev1.flip andThen ev).snd.subst[λ[v => X === (qs.Joint ** v)]](ev1)
                      ret[X, Z ** Y, Y, Z](par(seq(qt), seq(pt)).castA[X], Snd[Z, Y], Fst[Z, Y])
                    }
                    def apply[U](q: Snd[U, qs.Joint])(implicit ev: X === (U ** qs.Joint)) = {
                      val r = go[qs.Joint, Y, Z](pt, qt) // compiler bug that this passes without casting pt
                      ret(Snd[U, qs.Joint].castA[X] andThenNT r._1, r._2._1, r._2._2)
                    }
                    def apply[A1, A2, B1, B2](q: Par[A1, A2, B1, B2])(implicit ev1: X === (A1 ** A2), ev2: (B1 ** B2) === qs.Joint) =
                      flipRet(go(qs, ps))
                  })
                def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: X === (A1 ** A2), ev2: (B1 ** B2) === ps.Joint) =
                  seq(pt).split[B1, B2](ev2.flip) match {
                    case Left3(pt1)  => go(Fst[A1, A2].castA[X] :: p.p1 :: AList(pt1), qs)
                    case Right3(pt2) => go(Snd[A1, A2].castA[X] :: p.p2 :: AList(pt2), qs)
                    case Middle3(pt12) =>
                      val ((pt1, pt2), ev3) = (pt12._1, pt12._2)
                      val p1 = p.p1 andThenNT pt1
                      val p2 = p.p2 andThenNT pt2
                      qh.visit(new qh.Visitor[APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]] {
                        def apply(q: Unit[X])(implicit ev: T === qs.Joint) = sys.error("NonTerminal cannot be Unit")
                        def apply(q: Id[X])(implicit ev: X === qs.Joint) = go[X, Y, Z](ps, ev.flip.subst[AList[τ, ?, Z]](qt))
                        def apply[U](q: AndThen[X, U, qs.Joint]) = go(ps, q.p :: q.q :: qt)
                        def apply[V](q: Fst[qs.Joint, V])(implicit ev: X === (qs.Joint ** V)) = {
                          val r1pq = p1 gcdNT seq(qt).castA[A1](ev1.flip.andThen(ev).fst)
                          val (r1, (r1p, r1q)) = (r1pq._1, r1pq._2)
                          ret(par(r1, p2).castA(ev1), par(r1p, Id[pt12.B]).castB(ev3), Fst[r1pq.A, pt12.B] andThenNT r1q)
                        }
                        def apply[U](q: Snd[U, qs.Joint])(implicit ev: X === (U ** qs.Joint)) = {
                          val r2pq = p2 gcdNT seq(qt).castA[A2](ev1.flip.andThen(ev).snd)
                          val (r2, (r2p, r2q)) = (r2pq._1, r2pq._2)
                          ret(par(p1, r2).castA(ev1), par(Id[pt12.A], r2p).castB(ev3), Snd[pt12.A, r2pq.A] andThenNT r2q)
                        }
                        def apply[C1, C2, D1, D2](q: Par[C1, C2, D1, D2])(implicit ev4: X === (C1 ** C2), ev5: (D1 ** D2) === qs.Joint) =
                          seq(qt).split[D1, D2](ev5.flip) match {
                            case Left3(qt1)  => go(ps, Fst[C1, C2].castA(ev4) :: q.p1 :: AList(qt1))
                            case Right3(qt2) => go(ps, Snd[C1, C2].castA(ev4) :: q.p2 :: AList(qt2))
                            case Middle3(qt12) =>
                              val ((qt1, qt2), ev6) = (qt12._1, qt12._2)
                              val q1 = q.p1 andThenNT qt1
                              val q2 = q.p2 andThenNT qt2
                              val r1pq = p1 gcdNT q1.castA[A1](ev1.flip.andThen(ev4).fst)
                              val r2pq = p2 gcdNT q2.castA[A2](ev1.flip.andThen(ev4).snd)
                              val (r1, (r1p, r1q)) = (r1pq._1, r1pq._2)
                              val (r2, (r2p, r2q)) = (r2pq._1, r2pq._2)
                              ret(par(r1, r2).castA(ev1), par(r1p, r2p).castB(ev3), par(r1q, r2q).castB(ev6))
                          }
                      })
                  }
              })
          }
        }
      go[A, B, C](AList(this), AList(that))
    }

    def switchTerminal: (T === B) Either NonTerminal[**, T, A, B] = Right(this)

    override def castA[A0](implicit ev: A0 === A): NonTerminal[**, T, A0, B] =
      ev.flip.subst[NonTerminal[**, T, ?, B]](this)

    override def castB[B1](implicit ev: B === B1): NonTerminal[**, T, A, B1] =
      ev.subst[NonTerminal[**, T, A, ?]](this)

    /**
     * Deconstructs a projection from product type.
     * If this projection discards the second part,
     * returns the remaining projection from the first part (in `Left3`).
     * If this projection discards the first part,
     * returns the remaining projection from the second part (in `Right3`).
     * Otherwise, decomposes into projections from each of the two parts (returned in `Middle3`).
     */
    final def split[A1, A2](implicit ev: A === (A1 ** A2)): Either3[
      NonTerminal[**, T, A1, B],
      A2Pair[
        λ[(b1, b2) => (NonTerminal[**, T, A1, b1], NonTerminal[**, T, A2, b2])],
        λ[(b1, b2) => (b1 ** b2) === B]
      ],
      NonTerminal[**, T, A2, B]
    ] = {
      def ret[B1, B2](p1: NonTerminal[**, T, A1, B1], p2: NonTerminal[**, T, A2, B2])(implicit ev: (B1 ** B2) === B) =
        A2Pair[
          λ[(b1, b2) => (NonTerminal[**, T, A1, b1], NonTerminal[**, T, A2, b2])],
          λ[(b1, b2) => (b1 ** b2) === B],
          B1, B2
        ]((p1, p2), ev)

      visitNT(new VisitorNT[Either3[
        NonTerminal[**, T, A1, B],
        A2Pair[
          λ[(b1, b2) => (NonTerminal[**, T, A1, b1], NonTerminal[**, T, A2, b2])],
          λ[(b1, b2) => (b1 ** b2) === B]
        ],
        NonTerminal[**, T, A2, B]
      ]] {
        def apply[Y](p: Fst[B, Y])(implicit ev1: A === (B ** Y)) = Left3(Id[A1].castB((ev.flip andThen ev1).fst))
        def apply[X](p: Snd[X, B])(implicit ev1: A === (X ** B)) = Right3(Id[A2].castB((ev.flip andThen ev1).snd))
        def apply[X1, X2, Y1, Y2](p: Par[X1, X2, Y1, Y2])(implicit ev1: A === (X1 ** X2), ev2: (Y1 ** Y2) === B) =
          Middle3(ret(p.p1.castA(ev.flip.andThen(ev1).fst), p.p2.castA(ev.flip.andThen(ev1).snd)))
        def apply(p: Id[A])(implicit ev1: A === B) = Middle3(ret(Id[A1], Id[A2])(ev.flip andThen ev1))
        def apply[X](p: AndThen[A, X, B]) =
          p.p.split[A1, A2] match {
            case Left3(p1)  => Left3(AndThen(p1, p.q))
            case Right3(p1) => Right3(AndThen(p1, p.q))
            case Middle3(p12) =>
              val ((p1, p2), ev) = (p12._1, p12._2)
              p.q.castA(ev).split[p12.A, p12.B] match {
                case Left3(q) => Left3(AndThen(p1, q))
                case Right3(q) => Right3(AndThen(p2, q))
                case Middle3(q12) => Middle3(ret(AndThen(p1, q12._1._1), AndThen(p2, q12._1._2))(q12._2))
              }
          }
      })
    }

    /**
     * Permutes input `A` into parts `B ** Y`, for some `Y`.
     * If this projection is an identity projection, returns evidence that `A` = `B`.
     */
    def toShuffle: Either[A === B, Exists[λ[y => Shuffle[**, A, B ** y]]]] = {
      def shuffle[Y](s: Shuffle[**, A, B ** Y]): Exists[λ[y => Shuffle[**, A, B ** y]]] =
        Exists[λ[y => Shuffle[**, A, B ** y]], Y](s)

      visitNT(new VisitorNT[Either[A === B, Exists[λ[y => Shuffle[**, A, B ** y]]]]] {
        def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)) =
          Right(shuffle(Shuffle.Id[**, B ** Y]().castA[A]))

        def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)) =
          Right(shuffle(Shuffle.Swap[**, X, B]().castA[A]))

        def apply(p: Id[A])(implicit ev: A === B) =
          Left(ev)

        def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) =
          (p.p1.toShuffle, p.p2.toShuffle) match {
            case (Left(ev3), Left(ev4)) =>
              Left(ev1 andThen (ev3 lift2[**] ev4) andThen ev2)
            case (Left(ev3), Right(s2)) =>
              Right(shuffle[s2.A](Shuffle.par(Shuffle.Id[**, A1]().castB(ev3), s2.value).andThen(Shuffle.AssocRL()).castA[A].castB(ev2 lift2[**] implicitly)))
            case (Right(s1), Left(ev4)) =>
              Right(shuffle[s1.A](
                Shuffle.par(s1.value, Shuffle.Id[**, A2]().castB(ev4)).castA[A] andThen
                Shuffle.AssocLR() andThen
                Shuffle.par(Shuffle.Id(), Shuffle.Swap()) andThen
                Shuffle.AssocRL().castB(ev2 lift2[**] implicitly)
              ))
            case (Right(s1), Right(s2)) =>
              Right(shuffle[s1.A ** s2.A](
                Shuffle.par(s1.value, s2.value).castA[A] andThen
                Shuffle.AssocLR() andThen
                Shuffle.par(
                  Shuffle.Id(),
                  Shuffle.AssocRL() andThen Shuffle.par(Shuffle.Swap[**, s1.A, B2](), Shuffle.Id[**, s2.A]()) andThen Shuffle.AssocLR()
                ) andThen
                Shuffle.AssocRL().castB(ev2 lift2[**] implicitly)
              ))
          }

        def apply[X](p: AndThen[A, X, B]) =
          p.p.toShuffle match {
            case Left(ev) => p.q.castA(ev).toShuffle
            case Right(s) => p.q.toShuffle match {
              case Left(ev) => Right(ev.subst[λ[α => Exists[λ[y => Shuffle[**, A, α ** y]]]]](s))
              case Right(t) => Right(shuffle[t.A ** s.A](s.value andThen Shuffle.par(t.value, Shuffle.Id()) andThen Shuffle.AssocLR()))
            }
          }
      })
    }
  }

  case class Fst[**[_,_], T, A, B]() extends NonTerminal[**, T, A ** B, A] {
    def visitNT[R](v: VisitorNT[R]): R = v(this)

    def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): A === X =
      Leibniz.force[Nothing, Any, A, X]
  }

  case class Snd[**[_,_], T, A, B]() extends NonTerminal[**, T, A ** B, B] {
    def visitNT[R](v: VisitorNT[R]): R = v(this)

    def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): B === Y =
      Leibniz.force[Nothing, Any, B, Y]
  }

  case class Par[**[_,_], T, A1, A2, B1, B2](p1: NonTerminal[**, T, A1, B1], p2: NonTerminal[**, T, A2, B2]) extends NonTerminal[**, T, A1 ** A2, B1 ** B2] {
    def visitNT[R](v: VisitorNT[R]): R = v(this)
  }

  case class Unit[**[_,_], T, A]() extends Projection[**, T, A, T] {
    def visit[R](v: Visitor[R]): R = v(this)

    def switchTerminal: (T === T) Either NonTerminal[**, T, A, T] = Left(implicitly)
  }

  case class Id[**[_,_], T, A]() extends NonTerminal[**, T, A, A] {
    def visitNT[R](v: VisitorNT[R]): R = v(this)
  }

  case class AndThen[**[_,_], T, A, B, C](p: NonTerminal[**, T, A, B], q: NonTerminal[**, T, B, C]) extends NonTerminal[**, T, A, C] {
    def visitNT[R](v: VisitorNT[R]): R = v(this)
  }

  trait VisitorNT[**[_,_], T, A, B, R] {
    type π[X, Y] = Projection[**, T, X, Y]
    type Π[X, Y] = Projection.NonTerminal[**, T, X, Y]

    type Fst[X, Y]           = Projection.Fst[**, T, X, Y]
    type Snd[X, Y]           = Projection.Snd[**, T, X, Y]
    type Par[X1, X2, Y1, Y2] = Projection.Par[**, T, X1, X2, Y1, Y2]
    type Unit[X]             = Projection.Unit[**, T, X]
    type Id[X]               = Projection.Id[**, T, X]
    type AndThen[X, Y, Z]    = Projection.AndThen[**, T, X, Y, Z]

    def Fst[X, Y]                                         : Fst[X, Y]           = Projection.Fst()
    def Snd[X, Y]                                         : Snd[X, Y]           = Projection.Snd()
    def Par[X1, X2, Y1, Y2](p1: Π[X1, Y1], p2: Π[X2, Y2]) : Par[X1, X2, Y1, Y2] = Projection.Par(p1, p2)
    def Unit[X]                                           : Unit[X]             = Projection.Unit()
    def Id[X]                                             : Id[X]               = Projection.Id()
    def AndThen[X, Y, Z](p: Π[X, Y], q: Π[Y, Z])          : AndThen[X, Y, Z]    = Projection.AndThen(p, q)

    def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)): R
    def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)): R
    def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B): R
    def apply(p: Id[A])(implicit ev: A === B): R
    def apply[X](p: AndThen[A, X, B]): R
  }

  trait Visitor[**[_,_], T, A, B, R] extends VisitorNT[**, T, A, B, R] {
    def apply(p: Unit[A])(implicit ev: T === B): R
  }

  trait OptVisitor[**[_,_], T, A, B, R] extends Visitor[**, T, A, B, Option[R]] {
    def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)) = Option.empty[R]
    def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)) = Option.empty[R]
    def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) = Option.empty[R]
    def apply(p: Unit[A])(implicit ev: T === B) = Option.empty[R]
    def apply(p: Id[A])(implicit ev: A === B) = Option.empty[R]
    def apply[X](p: AndThen[A, X, B]) = Option.empty[R]
  }

  def par[**[_,_], T, A1, A2, B1, B2](p1: NonTerminal[**, T, A1, B1], p2: NonTerminal[**, T, A2, B2]): NonTerminal[**, T, A1 ** A2, B1 ** B2] =
    (p1.isId, p2.isId) match {
      case (Some(ev1), Some(ev2)) => Id[**, T, A1 ** A2]().castB(ev1 lift2[**] ev2)
      case _ => Par(p1, p2)
    }

  private[lambdacart] def extractFrom[:->:[_,_], **[_,_], T, H[_,_], A, B](
    f: FreeCCC[:->:, **, T, H, A, B]
  ): APair[Projection[**, T, A, ?], FreeCCC[:->:, **, T, H, ?, B]] = {

    type :=>:[X, Y] = FreeCCC[:->:, **, T, H, X, Y]
    type Prj[X, Y] = Projection[**, T, X, Y]

    f.visit(new f.Visitor[APair[Prj[A, ?], ? :=>: B]] {
      def pair[X](p: Prj[A, X], f: X :=>: B): APair[Prj[A, ?], ? :=>: B] =
        APair[Prj[A, ?], ? :=>: B, X](p, f)

      override def apply(f: Lift[A, B]) =
        pair(Projection.Id(), f)

      override def apply(f: Id[A])(implicit ev: A === B) =
        pair(Projection.Id(), f.castB)

      override def apply[X](f: Fst[B, X])(implicit ev: A === (B ** X)) =
        pair(Projection.Fst[**, T, B, X].castA[A], Id[B])

      override def apply[X](f: Snd[X, B])(implicit ev: A === (X ** B)) =
        pair(Projection.Snd[**, T, X, B].castA[A], Id[B])

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        pair(Projection.Unit(), Id[T].castB)

      override def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        val pf1 = extractFrom(f.f)
        val pf2 = extractFrom(f.g)
        val (p1, f1) = (pf1._1, pf1._2)
        val (p2, f2) = (pf2._1, pf2._2)
        val gcd = p1 gcd p2
        val (r, (r1, r2)) = (gcd._1, gcd._2)
        pair(r, (r1.prependTo(f1) prod r2.prependTo(f2)).castB)
      }

      override def apply(f: Sequence[A, B]) = {
        val qt = extractFrom(FreeCCC.sequence(f.fs.tail))
        val (q, t) = (qt._1, qt._2)
        restrictResult(f.fs.head)(q) match {
          case Some(h0) =>
            val ph = extractFrom(h0)
            val (p, h) = (ph._1, ph._2)
            pair(p, h andThen t)
          case None =>
            val ph = extractFrom(f.fs.head)
            val (p, h) = (ph._1, ph._2)
            h.isId match {
              case None => pair(p, FreeCCC.sequence(h :: f.fs.tail))
              case Some(ev) => pair(p.castB(ev) andThen q, t)
            }
        }
      }

      override def apply[X, Y](g: Curry[A, X, Y])(implicit ev: H[X, Y] === B) = {
        // TODO
        pair(Projection.Id(), f)
      }
      override def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        val pg = extractFrom(f.f)
        val (p, g) = (pg._1, pg._2)
        p.switchTerminal match {
          case Left(ev1) => pair(Projection.Snd[**, T, X, Y].castA[A], Prod(Terminal[Y].castB(ev1), Id[Y]) andThen Uncurry(g))
          case Right(p) => pair(Projection.par[**, T, X, Y, pg.A, Y](p, Projection.Id()).castA[A], Uncurry(g))
        }
      }

      override def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) =
        pair(Projection.Unit(), Const(f.f).castB)
    })
  }


  private def restrictResultI[:->:[_,_], **[_,_], T, H[_,_], A, B, B0](
      f: FreeCCC[:->:, **, T, H, A, B]
  )(  p: Projection[**, T, B, B0]
  ): Improvement[FreeCCC[:->:, **, T, H, A, B0]] =
    restrictResult(f)(p) match {
      case Some(f) => improved(f)
      case None    => unchanged(p appendTo f)
    }

  private[lambdacart] def restrictResult[:->:[_,_], **[_,_], T, H[_,_], A, B, B0](
      f: FreeCCC[:->:, **, T, H, A, B],
  )(  p: Projection[**, T, B, B0]
  ): Option[FreeCCC[:->:, **, T, H, A, B0]] = {

    type :=>:[X, Y] = FreeCCC[:->:, **, T, H, X, Y]

    f.visit(new f.Visitor[Option[A :=>: B0]] { v =>
      def apply(f: Lift[A, B]) =
        p.isUnit map { ev => Terminal[A].castB(ev.flip) }

      def apply(f: Id[A])(implicit ev: A === B) = p.isId match {
        case Some(_) => None
        case None => Some(p.castA[A].toFreeCCC)
      }

      def apply(f: Terminal[A])(implicit ev: T === B) = None

      def apply[X](f: Fst[B, X])(implicit ev: A === (B ** X)) =
        p.isUnit map { ev1 => Terminal[A].castB(ev1.flip) }

      def apply[X](f: Snd[X, B])(implicit ev: A === (X ** B)) =
        p.isUnit map { ev1 => Terminal[A].castB(ev1.flip) }

      def apply(f: Sequence[A, B]) = (for {
        t <- restrictResultI(FreeCCC.sequence(f.fs.tail))(p)
        tpf = extractFrom(t)
        (tp, tf) = (tpf._1, tpf._2)
        h <- restrictResultI(f.fs.head)(tp)
      } yield (h andThen tf)).getImproved

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        p.switchTerminal match {
          case Left(ev1) => Some(Terminal[A].castB(ev1))
          case Right(p) => p.isId match {
            case Some(_) => None
            case None    => p.split[X, Y](ev.flip) match {
              case Left3(p1) => Some(restrictResultI(f.f)(p1).value)
              case Right3(p2) => Some(restrictResultI(f.g)(p2).value)
              case Middle3(p12) =>
                val ((p1, p2), ev1) = (p12._1, p12._2)
                val f1 = restrictResultI(f.f)(p1).value
                val f2 = restrictResultI(f.g)(p2).value
                Some(Prod(f1, f2).castB(ev1))
            }
          }
        }
      }

      def apply[X, Y](f: Curry[A, X, Y])(implicit ev: H[X, Y] === B) = p.switchTerminal match {
        case Left(ev1) =>
          Some(Terminal[A].castB(ev1))
        case Right(p) =>
          // XXX: not using p at all
          restrictResultI(f.f)(Projection.Id()).flatMap[A :=>: B] { g =>
            val qh = extractFrom(g)
            val (q, h) = (qh._1, qh._2)
            q.switchTerminal match {
              case Left(ev1) => improved(Terminal[A].andThen(h.castA(ev1).constA[X]).castB[B])
              case Right(q) => q.split[A, X] match {
                case Left3(q1) =>
                  q1.isId match {
                    case Some(_) => unchanged(g.curry[A, X].castB[B])
                    case None => improved(q1 prependTo h.constA[X].castB[B])
                  }
                case Middle3(q12) =>
                  val ((q1, q2), ev1) = (q12._1, q12._2)
                  q1.isId match {
                    case Some(_) => unchanged(g.curry[A, X].castB[B])
                    case None =>
                      val p1 = Projection.par[**, T, q12.A, X, q12.A, q12.B](Projection.Id[**, T, q12.A](), q2)
                      improved(q1 prependTo (p1.castB(ev1).toFreeCCC andThen h).curry[q12.A, X].castB[B])
                  }
                case Right3(q2) =>
                  improved(Terminal() andThen Const(q2 prependTo h).castB[B])
              }
            }
          }.getImproved.map(p appendTo _)
      }

      def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) =
        p.isUnit map { ev1 => Terminal[A].castB(ev1.flip) }

      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        (restrictResultI(f.f)(Projection.Id()) flatMap[A :=>: B] { g =>
          val qh = extractFrom(g)
          val (q, h) = (qh._1, qh._2)
          q.isId match {
            case Some(_) => unchanged(Uncurry(g).castA[A])
            case None => q.switchTerminal match {
              case Right(q) => improved(Uncurry(h) compose Projection.par(q, Projection.Id[**, T, Y]()).toFreeCCC.castA[A])
              case Left(ev1) => improved(
                Projection.Snd[**, T, X, Y].castA[A] prependTo
                Prod(
                  Terminal[Y].castB(ev1) andThen h,
                  Id[Y]
                ).andThen(FreeCCC.eval)
              )
            }
          }
        }).getImproved.map(p appendTo _)
      }
    })
  }
}
