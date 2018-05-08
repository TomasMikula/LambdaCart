package lambdacart

import lambdacart.util.{Improvement, LeibnizOps}
import lambdacart.util.Improvement._
import lambdacart.util.typealigned.{ACons, ANil, APair, A2Pair}
import scalaz.Leibniz
import scalaz.Leibniz.===
import scalaz.std.anyVal._

sealed trait Shuffle[**[_,_], A1, A2] {
  type Visitor[R]     = Shuffle.Visitor[**, A1, A2, R]
  type OptVisitor[R]  = Shuffle.OptVisitor[**, A1, A2, R]
  type GlueVisitor[R] = Shuffle.GlueVisitor[**, A1, A2, R]

  def visit[R](v: Visitor[R]): R
  def invert: Shuffle[**, A2, A1]
  def isId: Option[A1 === A2] = None
  def isSwap: Option[A2Pair[λ[(x, y) => A1 === (x ** y)], λ[(x, y) => (y ** x) === A2]]] = None

  def castA[A0](implicit ev: A0 === A1): Shuffle[**, A0, A2] = ev.flip.subst[Shuffle[**, ?, A2]](this)
  def castB[A3](implicit ev: A2 === A3): Shuffle[**, A1, A3] = ev.subst[Shuffle[**, A1, ?]](this)
  def andThen[A3](that: Shuffle[**, A2, A3]): Shuffle[**, A1, A3] = Shuffle.andThen(this, that)

  final def toFreeCCC[:->:[_,_], T, H[_,_]]: FreeCCC[:->:, **, T, H, A1, A2] =
    visit(new Visitor[FreeCCC[:->:, **, T, H, A1, A2]] {
      def apply(s: Id[A1])(implicit ev: A1 === A2) = FreeCCC.id.castB[A2]
      def apply[X](s: AndThen[A1, X, A2]) = FreeCCC.andThen(s.p.toFreeCCC[:->:, T, H], s.q.toFreeCCC[:->:, T, H])
      def apply[X1, X2, Y1, Y2](s: Par[X1, X2, Y1, Y2])(implicit ev1: A1 === (X1 ** Y1), ev2: (X2 ** Y2) === A2) =
        FreeCCC.parallel(s.a.toFreeCCC[:->:, T, H], s.b.toFreeCCC[:->:, T, H]).castA[A1].castB[A2]
      def apply[X, Y](s: Swap[X, Y])(implicit ev1: A1 === (X ** Y), ev2: (Y ** X) === A2) =
        FreeCCC.swap[:->:, **, T, H, X, Y].castA[A1].castB[A2]
      def apply[X, Y, Z](s: AssocLR[X, Y, Z])(implicit ev1: A1 === ((X ** Y) ** Z), ev2: (X ** (Y ** Z)) === A2) =
        FreeCCC.assocR.castA[A1].castB[A2]
      def apply[X, Y, Z](s: AssocRL[X, Y, Z])(implicit ev1: A1 === (X ** (Y ** Z)), ev2: ((X ** Y) ** Z) === A2) =
        FreeCCC.assocL.castA[A1].castB[A2]
    })
}
object Shuffle {
  case class Id[**[_,_], A]() extends Shuffle[**, A, A] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = this
    override def isId = Some(implicitly)
  }
  case class AndThen[**[_,_], A1, A2, A3](p: ShuffleOp[**, A1, A2], q: Shuffle[**, A2, A3]) extends Shuffle[**, A1, A3] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = q.invert andThen p.invert
  }

  sealed trait ShuffleOp[**[_,_], A1, A2] extends Shuffle[**, A1, A2] {
    override def castA[A0](implicit ev: A0 === A1): ShuffleOp[**, A0, A2] = ev.flip.subst[ShuffleOp[**, ?, A2]](this)
    override def castB[A3](implicit ev: A2 === A3): ShuffleOp[**, A1, A3] = ev.subst[ShuffleOp[**, A1, ?]](this)
  }

  case class Par[**[_,_], A1, A2, B1, B2](a: Shuffle[**, A1, A2], b: Shuffle[**, B1, B2]) extends ShuffleOp[**, A1 ** B1, A2 ** B2] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = Par(a.invert, b.invert)
  }
  case class Swap[**[_,_], A, B]() extends ShuffleOp[**, A ** B, B ** A] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = Swap()
    override def isSwap =
      Some(A2Pair[λ[(x, y) => (A ** B) === (x ** y)], λ[(x, y) => (y ** x) === (B ** A)], A, B](implicitly, implicitly))
  }
  case class AssocLR[**[_,_], A, B, C]() extends ShuffleOp[**, (A ** B) ** C, A ** (B ** C)] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = AssocRL()
  }
  case class AssocRL[**[_,_], A, B, C]() extends ShuffleOp[**, A ** (B ** C), (A ** B) ** C] {
    def visit[R](v: Visitor[R]) = v(this)
    def invert = AssocLR()
  }

  trait OpVisitor[**[_,_], A, B, R] {
    type Par[X1, Y1, X2, Y2] = Shuffle.Par[**, X1, Y1, X2, Y2]
    type Swap[X, Y] = Shuffle.Swap[**, X, Y]
    type AssocLR[X, Y, Z] = Shuffle.AssocLR[**, X, Y, Z]
    type AssocRL[X, Y, Z] = Shuffle.AssocRL[**, X, Y, Z]

    def apply[A1, B1, A2, B2](s: Par[A1, B1, A2, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B): R
    def apply[X, Y](s: Swap[X, Y])(implicit ev1: A === (X ** Y), ev2: (Y ** X) === B): R
    def apply[X, Y, Z](s: AssocLR[X, Y, Z])(implicit ev1: A === ((X ** Y) ** Z), ev2: (X ** (Y ** Z)) === B): R
    def apply[X, Y, Z](s: AssocRL[X, Y, Z])(implicit ev1: A === (X ** (Y ** Z)), ev2: ((X ** Y) ** Z) === B): R


    private[Shuffle] implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
      def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
      def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
      def swap: (X2 ** X1) === (Y2 ** Y1) = snd lift2[**] fst
    }

    private[Shuffle] implicit class ProductLProductLeibnizOps[X1, X2, X3, Y1, Y2, Y3](ev: ((X1 ** X2) ** X3) === ((Y1 ** Y2) ** Y3)) {
      def assocLR: (X1 ** (X2 ** X3)) === (Y1 ** (Y2 ** Y3)) = {
        val ev1 = ev.fst.fst
        val ev2 = ev.fst.snd
        val ev3 = ev.snd
        ev1 lift2[**] (ev2 lift2[**] ev3)
      }
    }

    private[Shuffle] implicit class ProductRProductLeibnizOps[X1, X2, X3, Y1, Y2, Y3](ev: (X1 ** (X2 ** X3)) === (Y1 ** (Y2 ** Y3))) {
      def assocRL: ((X1 ** X2) ** X3) === ((Y1 ** Y2) ** Y3) = {
        val ev1 = ev.fst
        val ev2 = ev.snd.fst
        val ev3 = ev.snd.snd
        (ev1 lift2[**] ev2) lift2[**] ev3
      }
    }
  }

  trait Visitor[**[_,_], A, B, R] extends OpVisitor[**, A, B, R] {
    type Id[X] = Shuffle.Id[**, X]
    type AndThen[X, Y, Z] = Shuffle.AndThen[**, X, Y, Z]

    def apply(s: Id[A])(implicit ev: A === B): R
    def apply[X](s: AndThen[A, X, B]): R
  }

  trait GlueVisitor[**[_,_], A, B, R] extends Visitor[**, A, B, R] {
    def caseOp(op: ShuffleOp[**, A, B]): R

    final def apply[A1, B1, A2, B2](s: Par[A1, B1, A2, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) = caseOp(s.castA(ev1).castB(ev2))
    final def apply[X, Y](s: Swap[X, Y])(implicit ev1: A === (X ** Y), ev2: (Y ** X) === B)                        = caseOp(s.castA(ev1).castB(ev2))
    final def apply[X, Y, Z](s: AssocLR[X, Y, Z])(implicit ev1: A === ((X ** Y) ** Z), ev2: (X ** (Y ** Z)) === B) = caseOp(s.castA(ev1).castB(ev2))
    final def apply[X, Y, Z](s: AssocRL[X, Y, Z])(implicit ev1: A === (X ** (Y ** Z)), ev2: ((X ** Y) ** Z) === B) = caseOp(s.castA(ev1).castB(ev2))
  }

  trait OptVisitor[**[_,_], A, B, R] extends Visitor[**, A, B, Option[R]] {
    override def apply(s: Id[A])(implicit ev: A === B) = Option.empty[R]
    override def apply[X](s: AndThen[A, X, B]) = Option.empty[R]
    override def apply[A1, B1, A2, B2](s: Par[A1, B1, A2, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) = Option.empty[R]
    override def apply[X, Y](s: Swap[X, Y])(implicit ev1: A === (X ** Y), ev2: (Y ** X) === B) = Option.empty[R]
    override def apply[X, Y, Z](s: AssocLR[X, Y, Z])(implicit ev1: A === ((X ** Y) ** Z), ev2: (X ** (Y ** Z)) === B) = Option.empty[R]
    override def apply[X, Y, Z](s: AssocRL[X, Y, Z])(implicit ev1: A === (X ** (Y ** Z)), ev2: ((X ** Y) ** Z) === B) = Option.empty[R]
  }

  def par[**[_,_], A1, A2, B1, B2](a: Shuffle[**, A1, A2], b: Shuffle[**, B1, B2]): Shuffle[**, A1 ** B1, A2 ** B2] = {
    (a.isId, b.isId) match {
      case (Some(eva), Some(evb)) => Id[**, A1 ** B1]().castB(eva lift2[**] evb)
      case _ => Par(a, b)
    }
  }

  def andThen[**[_,_], A1, A2, A3](thiz: Shuffle[**, A1, A2], that: Shuffle[**, A2, A3]): Shuffle[**, A1, A3] =
    thiz.visit(new thiz.GlueVisitor[Shuffle[**, A1, A3]] {
      def apply(s: Id[A1])(implicit ev: A1 === A2) = that.castA(ev)
      def apply[X](s: AndThen[A1, X, A2]) = andThen(s.p, andThen(s.q, that))
      def caseOp(op1: ShuffleOp[**, A1, A2]) =
        that.visit(new that.GlueVisitor[Option[Shuffle[**, A1, A3]]] {
          def apply(s: Id[A2])(implicit ev: A2 === A3) = Some(thiz.castB(ev))
          def caseOp(op2: ShuffleOp[**, A2, A3]) = andThenOp(op1, op2)
          def apply[X](s: AndThen[A2, X, A3]) = {
            andThenOp(op1, s.p) map (r => andThen(r, s.q))
          } orElse {
            s.q.visit(new s.q.GlueVisitor[Option[Shuffle[**, A1, A3]]] {
              def apply(q: Id[X])(implicit ev: X === A3) = Some(Shuffle.AndThen(op1, s.p).castB[A3])
              def caseOp(q: ShuffleOp[**, X, A3]) = andThenOp3(op1, s.p, q)
              def apply[Y](q: AndThen[X, Y, A3]) = andThenOp3(op1, s.p, q.p) map (r => andThen(r, q.q))
            })
          }
        }) getOrElse {
          Shuffle.AndThen(op1, that)
        }
    })

  private def andThenOp[**[_,_], A1, A2, A3](thiz: ShuffleOp[**, A1, A2], that: ShuffleOp[**, A2, A3]): Option[Shuffle[**, A1, A3]] = {
    {
      // cancel out successive swaps
      thiz.visit(new thiz.OptVisitor[Shuffle[**, A1, A3]] {
        override def apply[X, Y](s: Swap[X, Y])(implicit ev1: A1 === (X ** Y), ev2: (Y ** X) === A2) =
          that.visit(new that.OptVisitor[Shuffle[**, A1, A3]] {
            override def apply[U, V](t: Swap[U, V])(implicit ev3: A2 === (U ** V), ev4: (V ** U) === A3) = {
              val ev: A1 === A3 = ev1 andThen (ev2 andThen ev3).swap andThen ev4
              Some(Shuffle.Id[**, A1].castB(ev))
            }
          })
      })
    } orElse {
      // cancel out AssocLR andThen AssocRL
      thiz.visit(new thiz.OptVisitor[Shuffle[**, A1, A3]] {
        override def apply[X, Y, Z](s: AssocLR[X, Y, Z])(implicit ev1: A1 === ((X ** Y) ** Z), ev2: (X ** (Y ** Z)) === A2) =
          that.visit(new that.OptVisitor[Shuffle[**, A1, A3]] {
            override def apply[U, V, W](t: AssocRL[U, V, W])(implicit ev3: A2 === (U ** (V ** W)), ev4: ((U ** V) ** W) === A3) = {
              val ev: A1 === A3 = ev1 andThen (ev2 andThen ev3).assocRL andThen ev4
              Some(Shuffle.Id[**, A1].castB(ev))
            }
          })
        override def apply[X, Y, Z](s: AssocRL[X, Y, Z])(implicit ev1: A1 === (X ** (Y ** Z)), ev2: ((X ** Y) ** Z) === A2) =
          that.visit(new that.OptVisitor[Shuffle[**, A1, A3]] {
            override def apply[U, V, W](t: AssocLR[U, V, W])(implicit ev3: A2 === ((U ** V) ** W), ev4: (U ** (V ** W)) === A3) = {
              val ev: A1 === A3 = ev1 andThen (ev2 andThen ev3).assocLR andThen ev4
              Some(Shuffle.Id[**, A1].castB(ev))
            }
          })
      })
    } orElse {
      // fuse Pars
      thiz.visit(new thiz.OptVisitor[Shuffle[**, A1, A3]] {
        override def apply[X1, Y1, X2, Y2](s: Par[X1, Y1, X2, Y2])(implicit ev1: A1 === (X1 ** X2), ev2: (Y1 ** Y2) === A2) =
          that.visit(new that.OptVisitor[Shuffle[**, A1, A3]] {
            override def apply[U1, V1, U2, V2](t: Par[U1, V1, U2, V2])(implicit ev3: A2 === (U1 ** U2), ev4: (V1 ** V2) === A3) = {
              val yu = ev2 andThen ev3
              Some(Shuffle.par(
                s.a.castB(yu.fst) andThen t.a,
                s.b.castB(yu.snd) andThen t.b
              ).castA(ev1).castB(ev4))
            }
          })
      })
    } orElse {
      // push Par after Swap
      thiz.visit(new thiz.OptVisitor[Shuffle[**, A1, A3]] {
        override def apply[X1, Y1, X2, Y2](s: Par[X1, Y1, X2, Y2])(implicit ev1: A1 === (X1 ** X2), ev2: (Y1 ** Y2) === A2) =
          that.visit(new that.OptVisitor[Shuffle[**, A1, A3]] {
            override def apply[U, V](t: Swap[U, V])(implicit ev3: A2 === (U ** V), ev4: (V ** U) === A3) =
              Some(
                Shuffle.Swap[**, X1, X2].castA(ev1) andThen
                Shuffle.par(s.b, s.a).castB[A3]((ev2 andThen ev3).swap andThen ev4)
              )
          })
      })
    } orElse {
      // associate AndThens to the right
      thiz.visit(new thiz.OptVisitor[Shuffle[**, A1, A3]] {
        override def apply[X](s: AndThen[A1, X, A2]) = Some(s.p andThen (s.q andThen that))
      })
    } orElse {
      // TODO: push Pars after AssocLR/RL
      None
    }
  }

  private def andThenOp3[**[_,_], A1, A2, A3, A4](
    op1: ShuffleOp[**, A1, A2],
    op2: ShuffleOp[**, A2, A3],
    op3: ShuffleOp[**, A3, A4]
  ): Option[Shuffle[**, A1, A4]] = {
    // rewrite Swap >>> AssocRL >>> Par(Swap, Id)
    // to      AssocLR >>> Par(Id, Swap) >>> AssocRL
    op1.visit(new op1.OptVisitor[Shuffle[**, A1, A4]] {
      override def apply[X, Y](sw1: Swap[X, Y])(implicit ev1: A1 === (X ** Y), ev2: (Y ** X) === A2) =
        op2.visit(new op2.OptVisitor[Shuffle[**, A1, A4]] {
          override def apply[U, V, W](rl: AssocRL[U, V, W])(implicit ev3: A2 === (U ** (V ** W)), ev4: ((U ** V) ** W) === A3) =
            op3.visit(new op3.OptVisitor[Shuffle[**, A1, A4]] {
              override def apply[P1, Q1, P2, Q2](p: Par[P1, Q1, P2, Q2])(implicit ev5: A3 === (P1 ** P2), ev6: (Q1 ** Q2) === A4) =
                p.a.visit(new p.a.OptVisitor[Shuffle[**, A1, A4]] {
                  override def apply[R, S](sw2: Swap[R, S])(implicit ev7: P1 === (R ** S), ev8: (S ** R) === Q1) =
                    p.b.visit(new p.b.OptVisitor[Shuffle[**, A1, A4]] {
                      override def apply(id: Id[P2])(implicit ev9: P2 === Q2) = {
                        val x_vw: X === (V ** W) = (ev2 andThen ev3).snd
                        val y_u : Y === U        = (ev2 andThen ev3).fst
                        val a1_vwu: A1 === ((V ** W) ** U) = ev1 andThen (x_vw lift2[**] y_u)
                        val vu_sr: (V ** U) === (S ** R)   = ((ev4 andThen ev5).fst andThen ev7).swap
                        val vuw_a4: ((V ** U) ** W) === A4 = ((vu_sr andThen ev8) lift2[**] (ev4 andThen ev5).snd.andThen(ev9)) andThen ev6
                        Some(
                          AssocLR[**, V, W, U].castA(a1_vwu)  andThen
                          par(Id[**, V], Swap[**, W, U])      andThen
                          AssocRL[**, V, U, W].castB(vuw_a4)
                        )
                      }
                    })
                })
            })
        })
    })
  } orElse {
    // rewrite Swap >>> AssocLR >>> Par(Id, Swap)
    // to      AssocRL >>> Par(Swap, Id) >>> AssocLR
    op1.visit(new op1.OptVisitor[Shuffle[**, A1, A4]] {
      override def apply[X, Y](sw1: Swap[X, Y])(implicit ev1: A1 === (X ** Y), ev2: (Y ** X) === A2) =
        op2.visit(new op2.OptVisitor[Shuffle[**, A1, A4]] {
          override def apply[U, V, W](rl: AssocLR[U, V, W])(implicit ev3: A2 === ((U ** V) ** W), ev4: (U ** (V ** W)) === A3) =
            op3.visit(new op3.OptVisitor[Shuffle[**, A1, A4]] {
              override def apply[P1, Q1, P2, Q2](p: Par[P1, Q1, P2, Q2])(implicit ev5: A3 === (P1 ** P2), ev6: (Q1 ** Q2) === A4) =
                p.b.visit(new p.b.OptVisitor[Shuffle[**, A1, A4]] {
                  override def apply[R, S](sw2: Swap[R, S])(implicit ev7: P2 === (R ** S), ev8: (S ** R) === Q2) =
                    p.a.visit(new p.a.OptVisitor[Shuffle[**, A1, A4]] {
                      override def apply(id: Id[P1])(implicit ev9: P1 === Q1) = {
                        val x_w : X === W        = (ev2 andThen ev3).snd
                        val y_uv: Y === (U ** V) = (ev2 andThen ev3).fst
                        val a1_wuv: A1 === (W ** (U ** V)) = ev1 andThen (x_w lift2[**] y_uv)
                        val wv_sr: (W ** V) === (S ** R)   = ((ev4 andThen ev5).snd andThen ev7).swap
                        val uwv_a4: (U ** (W ** V)) === A4 = ((ev4 andThen ev5).fst.andThen(ev9) lift2[**] (wv_sr andThen ev8)) andThen ev6
                        Some(
                          AssocRL[**, W, U, V].castA(a1_wuv)  andThen
                          par(Swap[**, W, U], Id[**, V])      andThen
                          AssocLR[**, U, W, V].castB(uwv_a4)
                        )
                      }
                    })
                })
            })
        })
    })
  }


  def extractFrom[:->:[_,_], **[_,_], T, H[_,_], A, B](
    f: FreeCCC[:->:, **, T, H, A, B]
  ): APair[Shuffle[**, A, ?], FreeCCC[:->:, **, T, H, ?, B]] = {
    type :=>:[X, Y] = FreeCCC[:->:, **, T, H, X, Y]

    f.visit(new f.Visitor[APair[Shuffle[**, A, ?], ? :=>: B]] {
      def pair[X](p: Shuffle[**, A, X], f: X :=>: B): APair[Shuffle[**, A, ?], ? :=>: B] =
        APair.of[Shuffle[**, A, ?], ? :=>: B](p, f)

      def noShuffle = pair(Shuffle.Id(), f)

      def apply      (f:     Lift[A, B]   )                              = noShuffle
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = noShuffle
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = noShuffle
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = noShuffle
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = noShuffle
      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = noShuffle
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = noShuffle // TODO
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = noShuffle // TODO
      def apply      (f: Sequence[A, B]   )                              = {
        val qt = extractFrom(FreeCCC.sequence(f.fs.tail))
        val (q, t) = (qt._1, qt._2)
        shuffleResult(f.fs.head)(q) match {
          case Some(h0) =>
            val ph = extractFrom(h0)
            val (p, h) = (ph._1, ph._2)
            pair(p, h andThen t)
          case None =>
            val ph = extractFrom(f.fs.head)
            val (p, h) = (ph._1, ph._2)
            pair(p, FreeCCC.sequence(h :: f.fs.tail))
        }
      }
      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        val pf1 = Projection.extractFrom(f.f)
        val (p1, f1) = (pf1._1, pf1._2)
        val pf2 = Projection.extractFrom(f.g)
        val (p2, f2) = (pf2._1, pf2._2)
        (p1.switchTerminal, p2.switchTerminal) match {
          case (Left(ev1), _) =>
            val sg2 = extractFrom(f.g)
            val (s, g2) = (sg2._1, sg2._2)
            pair(s, Prod(Terminal[sg2.A].castB(ev1) andThen f1, g2).castB[B])
          case (_, Left(ev2)) =>
            val sg1 = extractFrom(f.f)
            val (s, g1) = (sg1._1, sg1._2)
            pair(s, Prod(g1, Terminal[sg1.A].castB(ev2) andThen f2).castB[B])
          case (Right(p1), Right(p2)) =>
            p1.toShuffle match {
              case Right(s1) =>
                val qg2 = Projection.extractFrom(s1.value.invert.toFreeCCC[:->:, T, H] andThen p2.toFreeCCC)
                val (q2, g2) = (qg2._1, qg2._2)
                q2.ignoresFst[pf1.A, s1.A] match {
                  case Some(q2) =>
                    val tg1 = extractFrom(f1)
                    val tg2 = extractFrom(q2 prependTo g2 andThen f2)
                    pair(s1.value andThen Shuffle.par(tg1._1, tg2._1), FreeCCC.parallel(tg1._2, tg2._2).castB[B])
                  case None => noShuffle
                }
              case Left(_) => noShuffle
            }
        }
      }
    })
  }


  def shuffleResultI[:->:[_,_], **[_,_], T, H[_,_], A, B, C](
      f: FreeCCC[:->:, **, T, H, A, B]
  )(  s: Shuffle[**, B, C]
  ): Improvement[FreeCCC[:->:, **, T, H, A, C]] =
    shuffleResult(f)(s) match {
      case Some(f) => improved(f)
      case None    => unchanged(f andThen s.toFreeCCC[:->:, T, H])
    }

  def shuffleResult[:->:[_,_], **[_,_], T, H[_,_], A, B, C](
      f: FreeCCC[:->:, **, T, H, A, B]
  )(  s: Shuffle[**, B, C]
  ): Option[FreeCCC[:->:, **, T, H, A, C]] = {
    f.visit(new f.Visitor[Option[FreeCCC[:->:, **, T, H, A, C]]] {
      def apply      (f:     Lift[A, B]   )                              = None
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = s.isId match {
        case Some(_) => None
        case None    => Some(s.toFreeCCC[:->:, T, H].castA)
      }
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = None
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = None
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = None
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = None // TODO
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = None // TODO
      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = None // TODO

      def apply      (f: Sequence[A, B]   )                              =
        f.fs.tail match {
          case ev @ ANil() => shuffleResult(f.fs.head.castB(ev.leibniz))(s)
          case ACons(th, tt) =>
            (shuffleResultI(FreeCCC.Sequence(th +: tt))(s) flatMap { t =>
              val rt1 = extractFrom(t)
              val (r, t1) = (rt1._1, rt1._2)
              shuffleResultI(f.fs.head)(r) map (_ andThen t1)
            }).getImproved
        }

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        s.visit(new s.Visitor[Option[A :=>: C]] {
          def apply(s: Id[B])(implicit ev: B === C) = None
          def apply[B1, C1, B2, C2](s: Par[B1, C1, B2, C2])(implicit ev1: B === (B1 ** B2), ev2: (C1 ** C2) === C) =
            (for {
              f1 <- shuffleResultI(f.f.castB((ev andThen ev1).fst))(s.a)
              f2 <- shuffleResultI(f.g.castB((ev andThen ev1).snd))(s.b)
            } yield Prod(f1, f2).castB[C]).getImproved
          def apply[P, Q](s: Swap[P, Q])(implicit ev1: B === (P ** Q), ev2: (Q ** P) === C) =
            Some(Prod(f.g, f.f).castB((ev andThen ev1).swap andThen ev2))
          def apply[P, Q, R](s: AssocLR[P, Q, R])(implicit ev1: B === ((P ** Q) ** R), ev2: (P ** (Q ** R)) === C) =
            f.f.visit(new f.f.OptVisitor[A :=>: C] {
              override def apply[U, V](f1: Prod[A, U, V])(implicit ev3: (U ** V) === X) = {
                implicit val up: U === P = (ev3 andThen (ev andThen ev1).fst).fst
                implicit val vq: V === Q = (ev3 andThen (ev andThen ev1).fst).snd
                implicit val yr: Y === R =              (ev andThen ev1).snd
                Some(Prod(f1.f.castB[P], Prod(f1.g.castB[Q], f.g.castB[R])).castB[C])
              }
            })
          def apply[P, Q, R](s: AssocRL[P, Q, R])(implicit ev1: B === (P ** (Q ** R)), ev2: ((P ** Q) ** R) === C) =
            f.g.visit(new f.g.OptVisitor[A :=>: C] {
              override def apply[U, V](f2: Prod[A, U, V])(implicit ev3: (U ** V) === Y) = {
                implicit val xp: X === P =              (ev andThen ev1).fst
                implicit val uq: U === Q = (ev3 andThen (ev andThen ev1).snd).fst
                implicit val vr: V === R = (ev3 andThen (ev andThen ev1).snd).snd
                Some(Prod(Prod(f.f.castB[P], f2.f.castB[Q]), f2.g.castB[R]).castB[C])
              }
            })
          def apply[P](s: AndThen[B, P, C]) =
            shuffleResult(f.castB[B])(s.p) map (f => shuffleResultI(f)(s.q).value)
        })
    })
  }
  
}
