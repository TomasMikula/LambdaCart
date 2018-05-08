package lambdacart

import lambdacart.util.{~~>, Exists}
import lambdacart.util.LeibnizOps
import lambdacart.util.typealigned.{ACons, AList, AList1, ANil, APair, A2Pair, LeftAction, RightAction}
import scala.annotation.tailrec
import scalaz.{~>, Either3, Left3, Leibniz, Middle3, Right3}
import scalaz.Leibniz.===
import scalaz.std.anyVal._
import scalaz.std.option._
import scalaz.syntax.apply._

sealed abstract class FreeCCC[:->:[_, _], **[_, _], T, H[_, _], A, B] { self =>
  import FreeCCC._

  type :=>:[α, β] = FreeCCC[:->:, **, T, H, α, β]

  type Visitor[R] = FreeCCC.Visitor[:->:, **, T, H, A, B, R]
  type OptVisitor[R] = FreeCCC.OptVisitor[:->:, **, T, H, A, B, R]
  type BinTransformer = FreeCCC.BinTransformer[:->:, **, T, H, A, B]

  type RewriteRule = FreeCCC.RewriteRule[:->:, **, T, H]
  type ClosedRewriteRule = FreeCCC.ClosedRewriteRule[:->:, **, T, H]

  type Prj[X, Y] = FreeCCC.Prj[**, T, X, Y]
  type FPrj[F, G] = FreeCCC.FPrj[**, T, H, F, G]
  type Expansion[X, X1] = FreeCCC.Expansion[**, T, X, X1]
  type Shuffle[X, X1] = FreeCCC.Shuffle[**, X, X1]

  /** Workaround for Scala's broken GADT pattern matching. */
  def visit[R](v: Visitor[R]): R

  def castA[X](implicit ev: X === A): FreeCCC[:->:, **, T, H, X, B] =
    ev.flip.subst[FreeCCC[:->:, **, T, H, ?, B]](this)

  def castB[Y](implicit ev: B === Y): FreeCCC[:->:, **, T, H, A, Y] =
    ev.subst[FreeCCC[:->:, **, T, H, A, ?]](this)

  def const[Z]: FreeCCC[:->:, **, T, H, Z, H[A, B]] =
    FreeCCC.const(this)

  def constA[X]: FreeCCC[:->:, **, T, H, A, H[X, B]] =
    FreeCCC.curry(FreeCCC.Fst() andThen this)

  def prod[C](that: FreeCCC[:->:, **, T, H, A, C]): FreeCCC[:->:, **, T, H, A, B ** C] =
    FreeCCC.prod(this, that)

  def compose[Z](that: FreeCCC[:->:, **, T, H, Z, A]): FreeCCC[:->:, **, T, H, Z, B] =
    FreeCCC.compose(this, that)

  def andThen[C](that: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    that compose this

  def >>>[C](that: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    this andThen that

  def curry[X, Y](implicit ev: A === (X ** Y)): FreeCCC[:->:, **, T, H, X, H[Y, B]] =
    FreeCCC.curry(this.castA(ev.flip))

  def uncurry[X, Y](implicit ev: B === H[X, Y]): FreeCCC[:->:, **, T, H, A**X, Y] =
    FreeCCC.uncurry(this.castB(ev))

  def asSequence: AList1[FreeCCC[:->:, **, T, H, ?, ?], A, B] =
    visit(new OptVisitor[AList1[FreeCCC[:->:, **, T, H, ?, ?], A, B]] {
      override def apply(f: Sequence[A, B]) = Some(f.fs)
    }).getOrElse(AList1(this))

  // FIXME unsafe, should instead return Option[A :=>: (B with C)]
  def termEqual[C](that: A :=>: C): Option[B === C] =
    if(this == that) Some(Leibniz.force[Nothing, Any, B, C])
    else             None

  final def foldMap[->[_, _]](φ: :->: ~~> ->)(implicit ccc: CCC.Aux[->, **, T, H]): A -> B =
    visit[A -> B](new Visitor[A -> B] {
      def apply      (f:       Lift[A, B]) = φ[A, B](f.f)
      def apply      (f:   Sequence[A, B]) = f.fs.foldMap(ν[:=>: ~~> ->][α, β](_.foldMap(φ)))
      def apply      (f:            Id[A])(implicit ev:        A === B) = ev.lift[A -> ?](ccc.id[A])
      def apply[X]   (f:        Fst[B, X])(implicit ev: A === (B ** X)) = ev.flip.lift[? -> B](ccc.fst[B, X])
      def apply[X]   (f:        Snd[X, B])(implicit ev: A === (X ** B)) = ev.flip.lift[? -> B](ccc.snd[X, B])
      def apply      (f:      Terminal[A])(implicit ev:        T === B) = ev.lift[A -> ?](ccc.terminal[A])
      def apply[X, Y](f:    Prod[A, X, Y])(implicit ev: (X ** Y) === B) = ev.lift[A -> ?](ccc.prod(f.f.foldMap(φ), f.g.foldMap(φ)))
      def apply[X, Y](f:   Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = ev.lift[A -> ?](ccc.curry(f.f.foldMap(φ)))
      def apply[X, Y](f:   Const[A, X, Y])(implicit ev:  H[X, Y] === B) = ev.lift[A -> ?](ccc.const(f.f.foldMap(φ)))
      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = ev.flip.lift[? -> B](ccc.uncurry(f.f.foldMap(φ)))
    })

  final def fold(implicit ccc: CCC.Aux[:->:, **, T, H]): A :->: B =
    foldMap(~~>.identity[:->:])

  final def translate[->[_, _]](φ: :->: ~~> ->): FreeCCC[->, **, T, H, A, B] =
    foldMap(Λ[X, Y](f => lift(φ[X, Y](f))): :->: ~~> FreeCCC[->, **, T, H, ?, ?])

  final def size: Int = visit(new Visitor[Int] {
    def apply      (a:    Sequence[A, B]) = 1 + a.fs.sum(Λ[α, β](_.size): :=>: ~~> λ[(χ, υ) => Int])
    def apply[X, Y](a:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = 1 + a.f.size
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = 1 + a.f.size
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = 1 + a.f.size
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = 1 + a.f.size + a.g.size
    def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   A === (B**Y)) = 1
    def apply[X]   (a:      Snd[X, B])   (implicit ev:   A === (X**B)) = 1
    def apply      (a:       Id[A])      (implicit ev:        A === B) = 1
    def apply      (a: Terminal[A])      (implicit ev:        T === B) = 1
    def apply      (a:     Lift[A, B])                                 = 1
  })

  final def depth: Int = visit(new Visitor[Int] {
    def apply(a: Sequence[A, B]) = {
      type ConstInt[X] = Int
      1 + a.fs.foldLeft[ConstInt](0)(ν[RightAction[ConstInt, :=>:]][α, β]((m: ConstInt[α], f: α :=>: β) => math.max(m, f.depth)))
    }
    def apply[X, Y](a:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = 1 + a.f.depth
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = 1 + a.f.depth
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = 1 + a.f.depth
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = 1 + math.max(a.f.depth, a.g.depth)
    def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   A === (B**Y)) = 1
    def apply[X]   (a:      Snd[X, B])   (implicit ev:   A === (X**B)) = 1
    def apply      (a:       Id[A])      (implicit ev:        A === B) = 1
    def apply      (a: Terminal[A])      (implicit ev:        T === B) = 1
    def apply      (a:     Lift[A, B])                                 = 1
  })

  /** Returns `true` iff this `FreeCCC` instance doesn't contain any instances of `:->:`. */
  final def isPure: Boolean = visit(new Visitor[Boolean] {
    def apply      (a:    Sequence[A, B]) = a.fs.all(Λ[α, β](_.isPure): :=>: ~~> λ[(χ, υ) => Boolean])
    def apply[X, Y](a:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = a.f.isPure
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = a.f.isPure
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = a.f.isPure
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = a.f.isPure && a.g.isPure
    def apply[Y]   (a:         Fst[B, Y])(implicit ev:   A === (B**Y)) = true
    def apply[X]   (a:         Snd[X, B])(implicit ev:   A === (X**B)) = true
    def apply      (a:             Id[A])(implicit ev:        A === B) = true
    def apply      (a:       Terminal[A])(implicit ev:        T === B) = true
    def apply      (a:        Lift[A, B])                              = false
  })

  private[FreeCCC] implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
    def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
    def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
    def swap: (X2 ** X1) === (Y2 ** Y1) = snd lift2[**] fst
  }

  private def optimize(rules: RewriteRule): FreeCCC[:->:, **, T, H, A, B] = {
    val rr = ν[ClosedRewriteRule].rewrite[X, Y](self =
      new Function1[X :=>: Y, Option[X :=>: Y]] {
        @tailrec def apply(f: X :=>: Y) = f match {
          case Optimized(_) | Id() | Lift(_)  => Some(f)
          case _: Terminal[:->:, **, T, H, X] => Some(f) // case Terminal() not accepted by scalac
          case _: Fst[:->:, **, T, H, x, y]   => Some(f) // case Fst() not accepted by scalac
          case _: Snd[:->:, **, T, H, x, y]   => Some(f) // case Snd() not accepted by scalac
          case f =>
            val g = f.transformChildren(self)
            rules.rewriteRec(g)(self) match {
              case Some(h) => this.apply(h)
              case None    => Some(Optimized(g))
            }
        }
      }
    )

    rr.rewrite(this).getOrElse(this)
  }

  private[lambdacart] def optim: FreeCCC[:->:, **, T, H, A, B] =
    optimize(genericRules)

  private[lambdacart] def optim0: FreeCCC[:->:, **, T, H, A, B] =
    optim.rmTags

  private[FreeCCC] def rmTags: FreeCCC[:->:, **, T, H, A, B] =
    rebuild(~~>.identity[:=>:])

  private[FreeCCC] def rebuild(φ: :=>: ~~> :=>:): A :=>: B =
    φ.apply(transformChildren(ν[:=>: ~~> :=>:][α, β](_.rebuild(φ))))

  private[FreeCCC] def transformChildren(φ: :=>: ~~> :=>:): A :=>: B =
    visit(new Visitor[A :=>: B] {
      def apply   (f:     Lift[A, B])                              = f
      def apply   (f:       Id[A]   )(implicit ev:        A === B) = f.castB[B]
      def apply[X](f:      Fst[B, X])(implicit ev: A === (B ** X)) = f.castA[A]
      def apply[X](f:      Snd[X, B])(implicit ev: A === (X ** B)) = f.castA[A]
      def apply   (f: Terminal[A]   )(implicit ev:        T === B) = f.castB[B]

      def apply(f: Sequence[A, B]) =
        Sequence(f.fs.map(φ))

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        Prod(φ.apply(f.f), φ.apply(f.g)).castB[B]

      def apply[X, Y](f: Curry[A, X, Y])(implicit ev:  H[X, Y] === B) =
        Curry(φ.apply(f.f)).castB[B]

      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) =
        Uncurry(φ.apply(f.f)).castA[A]

      def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) =
        Const(φ.apply(f.f)).castB[B]
    })

  private[FreeCCC] def ignoresFst[A1, A2](implicit ev: A === (A1 ** A2)): Option[A2 :=>: B] =
    visit(new OptVisitor[A2 :=>: B] {

      override def apply[X](f: Snd[X, B])(implicit ev1: A === (X ** B)) =
        Some(Id[B].castA((ev.flip andThen ev1).snd))

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        Some(Terminal[A2].castB)

      override def apply[X, Y](p: Prod[A, X, Y])(implicit ev1: (X ** Y) === B) =
        (p.f.ignoresFst[A1, A2] |@| p.g.ignoresFst[A1, A2])(Prod(_, _).castB)

      override def apply(f: Sequence[A, B]) =
        f.fs.head.ignoresFst[A1, A2] map { h => Sequence(h +: f.fs.tail) }
    })

  private[FreeCCC] def ignoresSnd[A1, A2](implicit ev: A === (A1 ** A2)): Option[A1 :=>: B] =
    visit(new OptVisitor[A1 :=>: B] {

      override def apply[Y](f: Fst[B, Y])(implicit ev1: A === (B ** Y)) =
        Some(Id[B].castA((ev.flip andThen ev1).fst))

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        Some(Terminal[A1].castB)

      override def apply[X, Y](p: Prod[A, X, Y])(implicit ev1: (X ** Y) === B) =
        (p.f.ignoresSnd[A1, A2] |@| p.g.ignoresSnd[A1, A2])(Prod(_, _).castB)

      override def apply(f: Sequence[A, B]) =
        f.fs.head.ignoresSnd[A1, A2] map { h => Sequence(h +: f.fs.tail) }
    })

  def isId: Option[A === B] =
    visit(new OptVisitor[A === B] {
      override def apply(f: Id[A])(implicit ev: A === B) = Some(ev)
    })

  def isTerminal: Option[T === B] =
    visit(new OptVisitor[T === B] {
      override def apply(f: Terminal[A])(implicit ev: T === B) = Some(ev)
    })

  def isFst: Option[Exists[λ[x => A === (B ** x)]]] =
    visit(new OptVisitor[Exists[λ[x => A === (B ** x)]]] {
      override def apply[X](f: Fst[B, X])(implicit ev: A === (B ** X)) =
        Some(Exists[λ[x => A === (B ** x)], X](ev))
    })

  def isSnd: Option[Exists[λ[x => A === (x ** B)]]] =
    visit(new OptVisitor[Exists[λ[x => A === (x ** B)]]] {
      override def apply[X](f: Snd[X, B])(implicit ev: A === (X ** B)) =
        Some(Exists[λ[x => A === (x ** B)], X](ev))
    })

  private[lambdacart] def stripLeadingProjection: APair[Prj[A, ?], ? :=>: B] = {
    visit(new Visitor[APair[Prj[A, ?], ? :=>: B]] {
      def pair[X](p: Prj[A, X], f: X :=>: B): APair[Prj[A, ?], ? :=>: B] =
        APair[Prj[A, ?], ? :=>: B, X](p, f)

      override def apply(f: Lift[A, B]) =
        pair(Prj.Id(), f)

      override def apply(f: Id[A])(implicit ev: A === B) =
        pair(Prj.Id(), f.castB)

      override def apply[X](f: Fst[B, X])(implicit ev: A === (B ** X)) =
        pair(Prj.Fst[**, T, B, X].castA[A], Id[B])

      override def apply[X](f: Snd[X, B])(implicit ev: A === (X ** B)) =
        pair(Prj.Snd[**, T, X, B].castA[A], Id[B])

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        pair(Prj.Unit(), Id[T].castB)

      override def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        val pf1 = f.f.stripLeadingProjection
        val pf2 = f.g.stripLeadingProjection
        val (p1, f1) = (pf1._1, pf1._2)
        val (p2, f2) = (pf2._1, pf2._2)
        val gcd = p1 gcd p2
        val (r, (r1, r2)) = (gcd._1, gcd._2)
        pair(r, (f1.afterPrj(r1) prod f2.afterPrj(r2)).castB)
      }

      override def apply(f: Sequence[A, B]) = {
        val qt = FreeCCC.sequence(f.fs.tail).stripLeadingProjection
        val (q, t) = (qt._1, qt._2)
        f.fs.head.restrictResultTo(q) match {
          case Some(h0) =>
            val ph = h0.stripLeadingProjection
            val (p, h) = (ph._1, ph._2)
            pair(p, h andThen t)
          case None =>
            val ph = f.fs.head.stripLeadingProjection
            val (p, h) = (ph._1, ph._2)
            h.isId match {
              case None => pair(p, Sequence(h +: f.fs.tail))
              case Some(ev) => pair(p.castB(ev) andThen q, t)
            }
        }
      }

      override def apply[X, Y](f: Curry[A, X, Y])(implicit ev: H[X, Y] === B) = {
        // TODO
        pair(Prj.Id(), FreeCCC.this)
      }
      override def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        val pg = f.f.stripLeadingProjection
        val (p, g) = (pg._1, pg._2)
        p.switchTerminal match {
          case Left(ev1) => pair(Prj.Snd[**, T, X, Y].castA[A], Prod(Terminal[Y].castB(ev1), Id[Y]) andThen Uncurry(g))
          case Right(p) => pair(Prj.par[**, T, X, Y, pg.A, Y](p, Prj.Id()).castA[A], Uncurry(g))
        }
      //  )
      }

      override def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) =
        pair(Prj.Unit(), Const(f.f).castB)
    })
  }

  private[FreeCCC] def stripTrailingProjection: APair[A :=>: ?, FPrj[?, B]] =
    visit(new Visitor[APair[A :=>: ?, FPrj[?, B]]] {
      def pair[X](f: A :=>: X, p: FPrj[X, B]): APair[A :=>: ?, FPrj[?, B]] = APair.of[A :=>: ?, FPrj[?, B]](f, p)

      def apply      (f:     Lift[A, B]   )                              = pair(FreeCCC.this, FPrj.Id())
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = pair(FreeCCC.this, FPrj.Id())
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = pair(FreeCCC.this, FPrj.Id())
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = pair(FreeCCC.this, FPrj.Id())
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = pair(FreeCCC.this, FPrj.Id())
      def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        val fp1 = f.f.stripTrailingProjection
        val (f1, p1) = (fp1._1, fp1._2)
        val fp2 = f.g.stripTrailingProjection
        val (f2, p2) = (fp2._1, fp2._2)
        pair(Prod(f1, f2), FPrj.Par(p1, p2).castB[B])
      }
      def apply      (f: Sequence[A, B]   )                              = f.fs.unsnoc match {
        case Left(f) => f.stripTrailingProjection
        case Right(p) =>
          val (init, last) = (p._1, p._2)
          val gr = last.stripTrailingProjection
          val (g, r) = (gr._1, gr._2)
          g.isId match {
            case Some(ev) =>
              val fq = Sequence(init).stripTrailingProjection
              val (f, q) = (fq._1, fq._2)
              pair(f, q.castB(ev) andThen r)
            case None =>
              pair(Sequence(init :+ g), r)
          }
      }
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = {
        val pg = f.f.stripLeadingProjection
        val (p, g) = (pg._1, pg._2)
        val hq = g.stripTrailingProjection
        val (h, q) = (hq._1, hq._2)
        p.switchTerminal match {
          case Left(ev1) => pair(Terminal[A].castB(ev1) andThen h, q.andThen(FPrj.ExtraArg[**, T, H, Y, X]()).castB)
          case Right(p) => p.split[A, X] match {
            case Left3(p1) =>
              pair(h afterPrj p1, q.andThen(FPrj.ExtraArg[**, T, H, Y, X]()).castB[B])
            case Middle3(p12) =>
              val ((p1, p2), ev1) = (p12._1, p12._2)
              pair(
                Curry(h afterPrj (Prj.Par[**, T, A, p12.B, p12.A, p12.B](p1, Prj.Id()).castB(ev1))),
                q.asWeakerRes[X].after(FPrj.StrongerArg(FPrj.ArgPrj(p2))).castB[B]
              )
            case Right3(p2) =>
              pair(
                h.const[A],
                q.asWeakerRes[X].after(FPrj.StrongerArg(FPrj.ArgPrj(p2))).castB[B]
              )
          }
        }
      }
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        val gq = f.f.stripTrailingProjection
        val (g, q) = (gq._1, gq._2)
        val q012 = q.splitIO[Y, B]
        val (q0, (q1, q2)) = (q012._1, q012._2)
        pair(Uncurry(g.andThenFPrj(q0.andThen(q1.asStrongerArg[q012.B]))).castA[A], q2)
      }
      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = {
        val pg = f.f.stripLeadingProjection
        val (p, g) = (pg._1, pg._2)
        val hq = g.stripTrailingProjection
        val (h, q) = (hq._1, hq._2)
        pair(Const(h), q.asWeakerRes[X].after(FPrj.StrongerArg(FPrj.ArgPrj(p))).castB[B])
      }
    })

  private[FreeCCC] def stripTrailingExpansion: APair[A :=>: ?, Expansion[?, B]] =
    visit(new Visitor[APair[A :=>: ?, Expansion[?, B]]] {
      def pair[X](f: A :=>: X, p: Expansion[X, B]): APair[A :=>: ?, Expansion[?, B]] =
        APair.of[A :=>: ?, Expansion[?, B]](f, p)

      def apply      (f:     Lift[A, B]   )                              = pair(FreeCCC.this, Expansion.Id())
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = pair(FreeCCC.this, Expansion.Id())
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = pair(FreeCCC.this, Expansion.Id())
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = pair(FreeCCC.this, Expansion.Id())
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = pair(FreeCCC.this, Expansion.Id())
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = pair(FreeCCC.this, Expansion.Id())
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = pair(FreeCCC.this, Expansion.Id())
      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = pair(FreeCCC.this, Expansion.Id())

      def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        (f.f.isId, f.g.isId) match {
          case (Some(ev1), Some(ev2)) => pair(Id(), Expansion.Diag().castB(ev1 lift2[**] ev2).castB[B])
          case _ => f.f.isTerminal match {
            case Some(ev1) =>
              val fi2 = f.g.stripTrailingExpansion
              val (f2, i2) = (fi2._1, fi2._2)
              pair(f2, i2 andThen Expansion.UnitL[**, T, Y]().castB(ev1.lift[? ** Y] andThen ev))
            case _ => f.g.isTerminal match {
              case Some(ev2) =>
                val fi1 = f.f.stripTrailingExpansion
                val (f1, i1) = (fi1._1, fi1._2)
                pair(f1, i1 andThen Expansion.UnitR[**, T, X]().castB(ev2.lift[X ** ?] andThen ev))
              case _ =>
                val fi1 = f.f.stripTrailingExpansion
                val (f1, i1) = (fi1._1, fi1._2)
                val fi2 = f.g.stripTrailingExpansion
                val (f2, i2) = (fi2._1, fi2._2)
                pair(Prod(f1, f2), Expansion.par(i1, i2).castB[B])
            }
          }
        }

      def apply(f: Sequence[A, B]) = f.fs.unsnoc match {
        case Left(f) => f.stripTrailingExpansion
        case Right(p) =>
          val (init, last) = (p._1, p._2)
          val gj = last.stripTrailingExpansion
          val (g, j) = (gj._1, gj._2)
          g.isId match {
            case Some(ev) =>
              val fi = Sequence(init).stripTrailingExpansion
              val (f, i) = (fi._1, fi._2)
              pair(f, i.castB(ev) andThen j)
            case None =>
              pair(Sequence(init :+ g), j)
          }
      }
    })

  private[lambdacart] def extractLeadingShuffle: APair[Shuffle[A, ?], ? :=>: B] = {
    visit(new Visitor[APair[Shuffle[A, ?], ? :=>: B]] {
      def pair[X](p: Shuffle[A, X], f: X :=>: B): APair[Shuffle[A, ?], ? :=>: B] =
        APair.of[Shuffle[A, ?], ? :=>: B](p, f)

      def noShuffle = pair(Shuffle.Id(), FreeCCC.this)

      def apply      (f:     Lift[A, B]   )                              = noShuffle
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = noShuffle
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = noShuffle
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = noShuffle
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = noShuffle
      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = noShuffle
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = noShuffle // TODO
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = noShuffle // TODO
      def apply      (f: Sequence[A, B]   )                              = {
        val qt = sequence(f.fs.tail).extractLeadingShuffle
        val (q, t) = (qt._1, qt._2)
        f.fs.head.shuffleResult(q) match {
          case Some(h0) =>
            val ph = h0.extractLeadingShuffle
            val (p, h) = (ph._1, ph._2)
            pair(p, h andThen t)
          case None =>
            val ph = f.fs.head.extractLeadingShuffle
            val (p, h) = (ph._1, ph._2)
            pair(p, Sequence(h +: f.fs.tail))
        }
      }
      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        val pf1 = f.f.stripLeadingProjection
        val (p1, f1) = (pf1._1, pf1._2)
        val pf2 = f.g.stripLeadingProjection
        val (p2, f2) = (pf2._1, pf2._2)
        (p1.switchTerminal, p2.switchTerminal) match {
          case (Left(ev1), _) =>
            val sg2 = f.g.extractLeadingShuffle
            val (s, g2) = (sg2._1, sg2._2)
            pair(s, Prod(Terminal[sg2.A].castB(ev1) andThen f1, g2).castB[B])
          case (_, Left(ev2)) =>
            val sg1 = f.f.extractLeadingShuffle
            val (s, g1) = (sg1._1, sg1._2)
            pair(s, Prod(g1, Terminal[sg1.A].castB(ev2) andThen f2).castB[B])
          case (Right(p1), Right(p2)) =>
            p1.toShuffle match {
              case Right(s1) =>
                val qg2 = (s1.value.invert.toFreeCCC[:->:, T, H] andThenPrj p2).stripLeadingProjection
                val (q2, g2) = (qg2._1, qg2._2)
                q2.ignoresFst[pf1.A, s1.A] match {
                  case Some(q2) =>
                    val tg1 = f1.extractLeadingShuffle
                    val tg2 = (g2 andThen f2 afterPrj q2).extractLeadingShuffle
                    pair(s1.value andThen Shuffle.par(tg1._1, tg2._1), parallel(tg1._2, tg2._2).castB[B])
                  case None => noShuffle
                }
              case Left(_) => noShuffle
            }
        }
      }
    })
  }

  private[FreeCCC] def restrictResultToI[B0](p: Prj[B, B0]): Improvement[A :=>: B0] =
    restrictResultTo(p) match {
      case Some(f) => improved(f)
      case None    => unchanged(this andThenPrj p)
    }

  private[lambdacart] def restrictResultTo[B0](p: Prj[B, B0]): Option[A :=>: B0] =
    visit(new Visitor[Option[A :=>: B0]] { v =>
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
        t <- FreeCCC.sequence(f.fs.tail).restrictResultToI(p)
        tpf = t.stripLeadingProjection
        (tp, tf) = (tpf._1, tpf._2)
        h <- f.fs.head.restrictResultToI(tp)
      } yield (h andThen tf)).getImproved

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = {
        p.switchTerminal match {
          case Left(ev1) => Some(Terminal[A].castB(ev1))
          case Right(p) => p.isId match {
            case Some(_) => None
            case None    => p.split[X, Y](ev.flip) match {
              case Left3(p1) => Some(f.f.restrictResultToI(p1).value)
              case Right3(p2) => Some(f.g.restrictResultToI(p2).value)
              case Middle3(p12) =>
                val ((p1, p2), ev1) = (p12._1, p12._2)
                val f1 = f.f.restrictResultToI(p1).value
                val f2 = f.g.restrictResultToI(p2).value
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
          f.f.restrictResultToI(Prj.Id()).flatMap[A :=>: B] { g =>
            val qh = g.stripLeadingProjection
            val (q, h) = (qh._1, qh._2)
            q.switchTerminal match {
              case Left(ev1) => improved(Terminal[A].andThen(h.castA(ev1).constA[X]).castB[B])
              case Right(q) => q.split[A, X] match {
                case Left3(q1) =>
                  q1.isId match {
                    case Some(_) => unchanged(g.curry[A, X].castB[B])
                    case None => improved(h.constA[X].afterPrj(q1).castB[B])
                  }
                case Middle3(q12) =>
                  val ((q1, q2), ev1) = (q12._1, q12._2)
                  q1.isId match {
                    case Some(_) => unchanged(g.curry[A, X].castB[B])
                    case None =>
                      val p1 = Prj.par[**, T, q12.A, X, q12.A, q12.B](Prj.Id[**, T, q12.A](), q2)
                      improved((p1.castB(ev1).toFreeCCC andThen h).curry[q12.A, X].afterPrj(q1).castB[B])
                  }
                case Right3(q2) =>
                  improved(Terminal() andThen Const(h.afterPrj(q2)).castB[B])
              }
            }
          }.getImproved.map(_ andThenPrj p)
      }

      def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) =
        p.isUnit map { ev1 => Terminal[A].castB(ev1.flip) }

      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        (f.f.restrictResultToI(Prj.Id()) flatMap[A :=>: B] { g =>
          val qh = g.stripLeadingProjection
          val (q, h) = (qh._1, qh._2)
          q.isId match {
            case Some(_) => unchanged(Uncurry(g).castA[A])
            case None => q.switchTerminal match {
              case Right(q) => improved(Uncurry(h).afterPrj(Prj.par(q, Prj.Id())).castA[A])
              case Left(ev1) => improved(
                Prod(
                  Terminal[Y].castB(ev1) andThen h,
                  Id[Y]
                ).andThen(FreeCCC.eval).afterPrj(Prj.Snd[**, T, X, Y].castA[A])
              )
            }
          }
        }).getImproved.map(_.andThenPrj(p))
      }
    })

  private[FreeCCC] def strengthenInputI[A1](p: FPrj[A1, A]): Improvement[A1 :=>: B] =
    strengthenInput(p) match {
      case Some(f) => improved(f)
      case None    => unchanged(this.afterFPrj(p))
    }

  /** Returns Some if simplification was achieved. */
  private[FreeCCC] def strengthenInput[A1](p: FPrj[A1, A]): Option[A1 :=>: B] =
    visit(new Visitor[Option[A1 :=>: B]] {
      def apply      (f:     Lift[A, B]   )                              = None
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = None

      def apply      (f:       Id[A]      )(implicit ev:        A === B) =
        p.visit(new p.OptVisitor[A1 :=>: B] {
          override def apply[Z](p: ExtraArg[A1, Z])(implicit ev1: H[Z, A1] === A) =
            Some(FreeCCC.constA.castB[A].castB[B])
        })

      def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = {
        val p012 = p.rsplit[B, X](ev.flip)
        val (ev1, (p1, p2)) = (p012._1, p012._2)
        Id[B].strengthenInput(p1) map {
          g => Fst[p012.A, p012.B].castA(ev1) andThen g
        }
      }

      def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = {
        val p012 = p.rsplit[X, B](ev.flip)
        val (ev1, (p1, p2)) = (p012._1, p012._2)
        Id[B].strengthenInput(p2) map {
          g => Snd[p012.A, p012.B].castA(ev1) andThen g
        }
      }

      def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        (for {
          f1 <- f.f.strengthenInputI(p)
          f2 <- f.g.strengthenInputI(p)
        } yield Prod(f1, f2).castB[B]).getImproved

      def apply      (f: Sequence[A, B]   )                              =
        (for {
          h <- f.fs.head.strengthenInputI(p)
          h1q = h.stripTrailingProjection
          (h1, q) = (h1q._1, h1q._2)
          t <- FreeCCC.sequence(f.fs.tail).strengthenInputI(q)
        } yield (h1 andThen t)).getImproved

      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = None // TODO

      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        val p12 = p.rsplit[X, Y](ev.flip)
        val (ev1, (p1, p2)) = (p12._1, p12._2)

        f.f.strengthenInputI(p1)                          .flatMap[A1 :=>: B] { g1 =>
        g1.strengthenOutputsArgI[Y, B, p12.B](p2)         .flatMap[A1 :=>: B] { g2 =>
        val hq = g2.stripTrailingProjection
        val (h, q) = (hq._1, hq._2)
        val q0io = q.splitIO
        val (q0, (qi, qo)) = (q0io._1, q0io._2)
        qo.isId match {
          case Some(_) => unchanged(Uncurry(g2).castA(ev1))
          case None => improved(Uncurry(h andThenFPrj q0.andThen(qi.asStrongerArg[q0io.B])).castA(ev1).andThenFPrj(qo))
        }
        }}.getImproved
      }

      def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = None
    })

  private[FreeCCC] def strengthenOutputsArgI[B1, B2, B0](p: FPrj[B0, B1])(implicit ev: H[B1, B2] === B): Improvement[A :=>: H[B0, B2]] =
    strengthenOutputsArg(p) match {
      case Some(f) => improved(f)
      case None    => unchanged(this andThenFPrj p.asStrongerArg[B2].castA[B](ev.flip))
    }

  private[FreeCCC] def strengthenOutputsArg[B1, B2, B0](p: FPrj[B0, B1])(implicit ev: H[B1, B2] === B): Option[A :=>: H[B0, B2]] = {
    // TODO
    None
  }

  private[FreeCCC] def deferExpansionI[A0](i: Expansion[A0, A]): Improvement[A0 :=>: B] =
    deferExpansion(i) match {
      case Some(f) => improved(f)
      case None    => unchanged(this.afterExpansion(i))
    }

  private[FreeCCC] def deferExpansion[A0](i: Expansion[A0, A]): Option[A0 :=>: B] =
    visit(new Visitor[Option[A0 :=>: B]] { v =>
      def apply(f: Lift[A, B])                       = None
      def apply(f:   Id[A]   )(implicit ev: A === B) = None

      def apply[C](f: Fst[B, C])(implicit ev: A === (B ** C)) =
        i.visit(new i.Visitor[Option[A0 :=>: B]] {
          def apply(i: Diag[A0])(implicit ev1: (A0 ** A0) === A) = Some(v.Id[A0].castB(ev1.andThen(ev).fst))
          def apply(i: UnitR[A0])(implicit ev1: (A0 ** T) === A) = Some(v.Id[A0].castB(ev1.andThen(ev).fst))
          def apply(i: UnitL[A0])(implicit ev1: (T ** A0) === A) = Some(v.Terminal[A0].castB(ev1.andThen(ev).fst))
          def apply(i: Id[A0])(implicit ev1: A0 === A) = None

          def apply[Q](i: AndThen[A0, Q, A]) = (for {
            f1 <- deferExpansionI(i.j)
            f2 <- f1.deferExpansionI(i.i)
          } yield f2).getImproved

          def apply[X, X1, Y, Y1](i: Par[X, X1, Y, Y1])(implicit ev1: A0 === (X ** Y), ev2: (X1 ** Y1) === A) =
            Some((v.Fst[X, Y] andThen i.i1.toFreeCCC).castA[A0].castB(ev2.andThen(ev).fst))
        })

      def apply[C](f: Snd[C, B])(implicit ev: A === (C ** B)) =
        i.visit(new i.Visitor[Option[A0 :=>: B]] {
          def apply(i: Diag[A0])(implicit ev1: (A0 ** A0) === A) = Some(v.Id[A0].castB(ev1.andThen(ev).snd))
          def apply(i: UnitL[A0])(implicit ev1: (T ** A0) === A) = Some(v.Id[A0].castB(ev1.andThen(ev).snd))
          def apply(i: UnitR[A0])(implicit ev1: (A0 ** T) === A) = Some(v.Terminal[A0].castB(ev1.andThen(ev).snd))
          def apply(i: Id[A0])(implicit ev1: A0 === A) = None

          def apply[Q](i: AndThen[A0, Q, A]) = (for {
            f1 <- deferExpansionI(i.j)
            f2 <- f1.deferExpansionI(i.i)
          } yield f2).getImproved

          def apply[X, X1, Y, Y1](i: Par[X, X1, Y, Y1])(implicit ev1: A0 === (X ** Y), ev2: (X1 ** Y1) === A) =
            Some((v.Snd[X, Y] andThen i.i2.toFreeCCC).castA[A0].castB(ev2.andThen(ev).snd))
        })

      def apply(f: Terminal[A])(implicit ev: T === B) = i.isId match {
        case None => Some(Terminal[A0].castB)
        case _    => None
      }

      def apply[X, Y](f: Const[A, X, Y])(implicit ev: H[X, Y] === B) = i.isId match {
        case None => Some(Const[A0, X, Y](f.f).castB)
        case _    => None
      }

      def apply(f: Sequence[A, B]) = (
        for {
          h1 <- f.fs.head.deferExpansionI(i)
          h2j = h1.stripTrailingExpansion
          (h2, j) = (h2j._1, h2j._2)
          t1 <- sequence(f.fs.tail).deferExpansionI(j)
        } yield (h2 andThen t1)
      ).getImproved

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) = (for {
        f1 <- f.f.deferExpansionI(i)
        f2 <- f.g.deferExpansionI(i)
      } yield Prod(f1, f2).castB[B]).getImproved

      def apply[X, Y](f: Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = None // TODO

      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
        val i012 = i.rsplit[X, Y](ev.flip)
        val (i0, (i1, i2)) = (i012._1, i012._2)
        f.f.deferExpansion(i1) map {
          (g: i012.A :=>: H[Y, B]) => Uncurry(g) afterExpansion i0.andThen(Expansion.par(Expansion.Id(), i2))
        }
      }
    })

  private[FreeCCC] def shuffleResultI[C](s: Shuffle[B, C]): Improvement[A :=>: C] =
    shuffleResult(s) match {
      case Some(f) => improved(f)
      case None    => unchanged(this andThen s.toFreeCCC[:->:, T, H])
    }

  private[lambdacart] def shuffleResult[C](s: Shuffle[B, C]): Option[A :=>: C] = {
    //println(s"$this   .shuffleResult   $s")
    visit(new Visitor[Option[A :=>: C]] {
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
          case ev @ ANil() => f.fs.head.castB(ev.leibniz).shuffleResult(s)
          case ACons(th, tt) =>
            (Sequence(th +: tt).shuffleResultI(s) flatMap { t =>
              val rt1 = t.extractLeadingShuffle
              val (r, t1) = (rt1._1, rt1._2)
              //println(s"Extracted shuffle from tail: $r")
              f.fs.head.shuffleResultI(r) map (_ andThen t1)
            }).getImproved
        }

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        s.visit(new s.Visitor[Option[A :=>: C]] {
          def apply(s: Id[B])(implicit ev: B === C) = None
          def apply[B1, C1, B2, C2](s: Par[B1, C1, B2, C2])(implicit ev1: B === (B1 ** B2), ev2: (C1 ** C2) === C) =
            (for {
              f1 <- f.f.castB((ev andThen ev1).fst).shuffleResultI(s.a)
              f2 <- f.g.castB((ev andThen ev1).snd).shuffleResultI(s.b)
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
            FreeCCC.this.shuffleResult(s.p) map (f => f.shuffleResultI(s.q).value)
        })
    })
  }

  private[FreeCCC] def andThenPrj[B0](p: Prj[B, B0]): A :=>: B0 =
    andThen(p.toFreeCCC)

  private[FreeCCC] def afterPrj[A0](p: Prj[A0, A]): A0 :=>: B =
    compose(p.toFreeCCC)

  private[FreeCCC] def andThenFPrj[B0](p: FPrj[B, B0]): A :=>: B0 =
    andThen(p.toFreeCCC)

  private[FreeCCC] def afterFPrj[A0](p: FPrj[A0, A]): A0 :=>: B =
    compose(p.toFreeCCC)

  private[FreeCCC] def afterExpansion[A0](i: Expansion[A0, A]): A0 :=>: B =
    compose(i.toFreeCCC)
}

object FreeCCC {
  case class Lift[:->:[_, _], **[_, _], T, H[_, _], A, B](f: A :->: B) extends FreeCCC[:->:, **, T, H, A, B] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Id[:->:[_, _], **[_, _], T, H[_, _], A]() extends FreeCCC[:->:, **, T, H, A, A] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Sequence[:->:[_, _], **[_, _], T, H[_, _], A, B](fs: AList1[FreeCCC[:->:, **, T, H, ?, ?], A, B]) extends FreeCCC[:->:, **, T, H, A, B] {
    def visit[R](v: Visitor[R]): R = v(this)

    override def toString: String = fs.mkString("Sequence(", ", ", ")")(_.toString)
  }

  case class Fst[:->:[_, _], **[_, _], T, H[_, _], A, B]() extends FreeCCC[:->:, **, T, H, A ** B, A] {
    def visit[R](v: Visitor[R]): R = v(this)

    def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): A === X =
      Leibniz.force[Nothing, Any, A, X]
  }

  case class Snd[:->:[_, _], **[_, _], T, H[_, _], A, B]() extends FreeCCC[:->:, **, T, H, A ** B, B] {
    def visit[R](v: Visitor[R]): R = v(this)

    def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): B === Y =
      Leibniz.force[Nothing, Any, B, Y]
  }

  case class Prod[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, B], g: FreeCCC[:->:, **, T, H, A, C]) extends FreeCCC[:->:, **, T, H, A, B ** C] {
    def visit[R](v: Visitor[R]): R = v(this)

    def cast[Y, Z](implicit ev: (B ** C) === (Y ** Z)): Prod[:->:, **, T, H, A, Y, Z] =
      this.asInstanceOf[Prod[:->:, **, T, H, A, Y, Z]]
  }

  case class Terminal[:->:[_, _], **[_, _], T, H[_, _], A]() extends FreeCCC[:->:, **, T, H, A, T] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Curry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A ** B, C]) extends FreeCCC[:->:, **, T, H, A, H[B, C]] {
    def visit[R](v: Visitor[R]): R = v(this)

    def cast[Y, Z](implicit ev: H[B, C] === H[Y, Z]): Curry[:->:, **, T, H, A, Y, Z] =
      this.asInstanceOf[Curry[:->:, **, T, H, A, Y, Z]]
  }

  case class Uncurry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, H[B, C]]) extends FreeCCC[:->:, **, T, H, A ** B, C] {
    def visit[R](v: Visitor[R]): R = v(this)

    def cast[X, Y](implicit ev: (A ** B) === (X ** Y)): Uncurry[:->:, **, T, H, X, Y, C] =
      this.asInstanceOf[Uncurry[:->:, **, T, H, X, Y, C]]
  }

  // Can be expressed as Curry(Snd() andThen f),
  // but we know that Const always starts at T (the terminal object).
  case class Const[:->:[_, _], **[_, _], T, H[_, _], Z, A, B](f: FreeCCC[:->:, **, T, H, A, B]) extends FreeCCC[:->:, **, T, H, Z, H[A, B]] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  /** Marker that the tree below this node is optimized,
    * and thus optimization will not try to rewrite it.
    */
  private[FreeCCC]
  case class Optimized[:->:[_, _], **[_, _], T, H[_, _], A, B](f: FreeCCC[:->:, **, T, H, A, B]) extends FreeCCC[:->:, **, T, H, A, B] {
    def visit[R](v: Visitor[R]): R = f.visit(v)
    override def toString = f.toString
  }


  trait Visitor[:->:[_, _], **[_, _], T, H[_, _], A, B, R] {
    type :=>:[X, Y] = FreeCCC[:->:, **, T, H, X, Y]

    type Lift[X, Y]       = FreeCCC.Lift    [:->:, **, T, H, X, Y]
    type Sequence[X, Y]   = FreeCCC.Sequence[:->:, **, T, H, X, Y]
    type Id[X]            = FreeCCC.Id      [:->:, **, T, H, X]
    type Prod[X, Y, Z]    = FreeCCC.Prod    [:->:, **, T, H, X, Y, Z]
    type Terminal[X]      = FreeCCC.Terminal[:->:, **, T, H, X]
    type Fst[X, Y]        = FreeCCC.Fst     [:->:, **, T, H, X, Y]
    type Snd[X, Y]        = FreeCCC.Snd     [:->:, **, T, H, X, Y]
    type Curry[X, Y, Z]   = FreeCCC.Curry   [:->:, **, T, H, X, Y, Z]
    type Uncurry[X, Y, Z] = FreeCCC.Uncurry [:->:, **, T, H, X, Y, Z]
    type Const[X, Y, Z]   = FreeCCC.Const   [:->:, **, T, H, X, Y, Z]

    def Lift[X, Y](f: X :->: Y)                 : Lift[X, Y]       = FreeCCC.Lift(f)
    def Id[X]()                                 : Id[X]            = FreeCCC.Id()
    def Prod[X, Y, Z](f: X :=>: Y, g: X :=>: Z) : Prod[X, Y, Z]    = FreeCCC.Prod(f, g)
    def Terminal[X]()                           : Terminal[X]      = FreeCCC.Terminal()
    def Fst[X, Y]()                             : Fst[X, Y]        = FreeCCC.Fst()
    def Snd[X, Y]()                             : Snd[X, Y]        = FreeCCC.Snd()
    def Curry[X, Y, Z](f: (X ** Y) :=>: Z)      : Curry[X, Y, Z]   = FreeCCC.Curry(f)
    def Uncurry[X, Y, Z](f: X :=>: H[Y, Z])     : Uncurry[X, Y, Z] = FreeCCC.Uncurry(f)
    def Const[X, Y, Z](f: Y :=>: Z)             : Const[X, Y, Z]   = FreeCCC.Const(f)

    def apply      (f:     Lift[A, B]   )                              : R
    def apply      (f: Sequence[A, B]   )                              : R
    def apply      (f:       Id[A]      )(implicit ev:        A === B) : R
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) : R
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) : R
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) : R
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) : R
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) : R
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) : R
    def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) : R
  }

  trait OptVisitor[:->:[_, _], **[_, _], T, H[_, _], A, B, R]
  extends Visitor[:->:, **, T, H, A, B, Option[R]] {
    def apply      (f:     Lift[A, B]   )                              = Option.empty[R]
    def apply      (f: Sequence[A, B]   )                              = Option.empty[R]
    def apply      (f:       Id[A]      )(implicit ev:        A === B) = Option.empty[R]
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = Option.empty[R]
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = Option.empty[R]
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = Option.empty[R]
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) = Option.empty[R]
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = Option.empty[R]
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = Option.empty[R]
    def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = Option.empty[R]
  }

  trait BinTransformer[:->:[_, _], **[_, _], T, H[_, _], A, B]
  extends OptVisitor[:->:, **, T, H, A, B, FreeCCC[:->:, **, T, H, A, B]] { self =>
    def apply[X, Y, Z](f: X :=>: Y, g: Y :=>: Z): Option[X :=>: Z] = None

    final override def apply(f: Sequence[A, B]): Option[A :=>: B] = {
      type G[α] = AList1[:=>:, α, B]
      f.fs.foldRight1[G](λ[(? :=>: B) ~> G](AList1(_)))(ν[LeftAction[G, :=>:]][α, β]((f, acc) => self(f, acc.head) match {
        case Some(f) => f +: acc.tail
        case None    => f :: acc
      })).uncons match {
        case Left(f)   => Some(f)
        case Right(ht) =>
          val fs = ht._1 :: ht._2
          if(fs.size < f.fs.size) Some(Sequence(fs)) else None
      }
    }
  }

  trait RewriteRule[:->:[_, _], **[_, _], T, H[_, _]] {
    type :=>:[A, B] = FreeCCC[:->:, **, T, H, A, B]

    def rewriteRec[A, B]: (A :=>: B) => ClosedRewriteRule[:->:, **, T, H] => Option[A :=>: B]
  }

  trait ClosedRewriteRule[:->:[_, _], **[_, _], T, H[_, _]]
  extends RewriteRule[:->:, **, T, H]
     with (FreeCCC[:->:, **, T, H, ?, ?] ~~> FreeCCC[:->:, **, T, H, ?, ?]) {

    def rewrite[A, B]: (A :=>: B) => Option[A :=>: B]

    def apply[A, B]: (A :=>: B) => (A :=>: B) =
      f => rewrite[A, B](f).getOrElse(f)

    def rewriteRec[A, B]: (A :=>: B) => ClosedRewriteRule[:->:, **, T, H] => Option[A :=>: B] =
      f => _ => rewrite(f)
  }

  object RewriteRule {
    def noop[:->:[_, _], **[_, _], T, H[_, _]]: RewriteRule[:->:, **, T, H] =
      ν[RewriteRule[:->:, **, T, H]].rewriteRec[A, B](f => rec => None)

    def sequence[:->:[_, _], **[_, _], T, H[_, _]](rules: RewriteRule[:->:, **, T, H]*): RewriteRule[:->:, **, T, H] =
      sequence(rules.toList)

    def sequence[:->:[_, _], **[_, _], T, H[_, _]](rules: List[RewriteRule[:->:, **, T, H]]): RewriteRule[:->:, **, T, H] =
      rules match {
        case Nil      => noop
        case r :: Nil => r
        case r :: rs =>
          val r2 = sequence(rs)
          ν[RewriteRule[:->:, **, T, H]].rewriteRec[A, B](f => rec =>
            r.rewriteRec(f)(rec) orElse r2.rewriteRec(f)(rec)
          )
      }
  }

  /** `H` can handle `A`, producing `R`. */
  type Handler[H, A, R] = (H, A) => R

  /**
   * For all `A`, `B` and `R`,
   * `H[A, B, R]` handles `F[A, B]`, producing `R`.
   */
  trait UniversalHandler[H[_,_,_], F[_,_]] {
    def apply[A, B, R]: Handler[H[A, B, R], F[A, B], R]
  }

  implicit def visitorUniversalHandler[:->:[_,_], **[_,_], T, H[_,_]]: UniversalHandler[Visitor[:->:, **, T, H, ?, ?, ?], FreeCCC[:->:, **, T, H, ?, ?]] =
    new UniversalHandler[Visitor[:->:, **, T, H, ?, ?, ?], FreeCCC[:->:, **, T, H, ?, ?]] {
      def apply[A, B, R] = (visitor, f) => f.visit(visitor)
    }

  trait CCCTermHandler[F[_,_], :->:[_,_], **[_,_], T, H[_,_], A, B, R] {
    def caseOpaque        (f: A :->: B           )                               : R
    def caseSequence      (f: AList1[F, A, B]    )                               : R
    def caseId                                     (implicit ev:        A === B) : R
    def caseFst[X]                                 (implicit ev: A === (B ** X)) : R
    def caseSnd[X]                                 (implicit ev: A === (X ** B)) : R
    def caseProd[X, Y]    (f: F[A, X], g: F[A, Y]) (implicit ev: (X ** Y) === B) : R
    def caseTerminal                               (implicit ev:        T === B) : R
    def caseCurry[X, Y]   (f: F[A ** X, Y])        (implicit ev:  H[X, Y] === B) : R
    def caseUncurry[X, Y] (f: F[X, H[Y, B]])       (implicit ev: A === (X ** Y)) : R
    def caseConst[X, Y]   (f: F[X, Y])             (implicit ev:  H[X, Y] === B) : R
  }

  def termHandlerToVisitor[:->:[_,_], **[_,_], T, H[_,_], A, B, R](
    h: CCCTermHandler[FreeCCC[:->:, **, T, H, ?, ?], :->:, **, T, H, A, B, R]
  ): Visitor[:->:, **, T, H, A, B, R] = new Visitor[:->:, **, T, H, A, B, R] {
    def apply      (f:     Lift[A, B]   )                              = h.caseOpaque(f.f)
    def apply      (f: Sequence[A, B]   )                              = h.caseSequence(f.fs)
    def apply      (f:       Id[A]      )(implicit ev:        A === B) = h.caseId
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: A === (B ** X)) = h.caseFst
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: A === (X ** B)) = h.caseSnd
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = h.caseProd(f.f, f.g)
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) = h.caseTerminal
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = h.caseCurry(f.f)
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = h.caseUncurry(f.f)
    def apply[X, Y](f:    Const[A, X, Y])(implicit ev:  H[X, Y] === B) = h.caseConst(f.f)
  }

  def termHandlerUniversality[:->:[_,_], **[_,_], T, H[_,_]]: UniversalHandler[
    CCCTermHandler[FreeCCC[:->:, **, T, H, ?, ?], :->:, **, T, H, ?, ?, ?],
    FreeCCC[:->:, **, T, H, ?, ?]
  ] =
    new UniversalHandler[
      CCCTermHandler[FreeCCC[:->:, **, T, H, ?, ?], :->:, **, T, H, ?, ?, ?],
      FreeCCC[:->:, **, T, H, ?, ?]
    ] {
      def apply[A, B, R] = (handler, f) => f.visit(termHandlerToVisitor(handler))
    }

  /**
   * Represents projection from a data type,
   * namely forgetting some part of the data.
   *
   * During program optimization pushed to the front, i.e. as early
   * as possible. (Don't carry around something only to ignore it later;
   * ignore as soon as possible.)
   */
  sealed trait Prj[**[_,_], T, A, B] {
    type Visitor[R] = Prj.Visitor[**, T, A, B, R]
    type OptVisitor[R] = Prj.OptVisitor[**, T, A, B, R]

    def visit[R](v: Visitor[R]): R

    def castA[C](implicit ev: C === A): Prj[**, T, C, B] = ev.flip.subst[Prj[**, T, ?, B]](this)
    def castB[C](implicit ev: B === C): Prj[**, T, A, C] = ev.subst[Prj[**, T, A, ?]](this)

    def unital(implicit ev: A === T): B === T

    def andThen[C](that: Prj[**, T, B, C]): Prj[**, T, A, C] =
      this.switchTerminal match {
        case Left(ev) => Prj.Unit().castB(that.unital(ev.flip).flip)
        case Right(thiz) =>
          that.switchTerminal match {
            case Left(ev) => Prj.Unit[**, T, A].castB(ev)
            case Right(that) => thiz andThenNT that
          }
      }

    def after[Z](that: Prj[**, T, Z, A]): Prj[**, T, Z, B] =
      that andThen this

    def isUnit: Option[B === T] = None
    def isId: Option[A === B] = None
    def isFst[X, Y](implicit ev: A === (X ** Y)): Option[X === B] = None
    def isSnd[X, Y](implicit ev: A === (X ** Y)): Option[Y === B] = None

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
    final def gcd[C](that: Prj[**, T, A, C]): APair[Prj[**, T, A, ?], λ[a => (Prj[**, T, a, B], Prj[**, T, a, C])]] =
      (this.switchTerminal, that.switchTerminal) match {
        case (Left(ev1), Left(ev2)) => gcdRet(Prj.Unit(), Prj.Id().castB(ev1), Prj.Id().castB(ev2))
        case (Left(ev1), Right(p2)) => gcdRet(p2, Prj.Unit().castB(ev1), Prj.Id())
        case (Right(p1), Left(ev2)) => gcdRet(p1, Prj.Id(), Prj.Unit().castB(ev2))
        case (Right(p1), Right(p2)) =>
          val r = p1 gcdNT p2
          gcdRet(r._1, r._2._1, r._2._2)
      }

    def ignoresSnd[X, Y](implicit ev: (X ** Y) === A): Option[Prj[**, T, X, B]] = {
      val gcd = this.castA(ev) gcd Prj.Fst[**, T, X, Y]
      val (common, (rest, _)) = (gcd._1, gcd._2)
      common.isFst[X, Y] map (ev1 => rest.castA(ev1))
    }

    def ignoresFst[X, Y](implicit ev: (X ** Y) === A): Option[Prj[**, T, Y, B]] = {
      val gcd = this.castA(ev) gcd Prj.Snd[**, T, X, Y]
      val (common, (rest, _)) = (gcd._1, gcd._2)
      common.isSnd[X, Y] map (ev1 => rest.castA(ev1))
    }

    private def gcdRet[X, C](p: Prj[**, T, A, X], q: Prj[**, T, X, B], r: Prj[**, T, X, C]) =
      APair[Prj[**, T, A, ?], λ[a => (Prj[**, T, a, B], Prj[**, T, a, C])], X](p, (q, r))

    private[Prj] implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
      def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
      def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
    }

    def switchTerminal: (T === B) Either Prj.NonTerminal[**, T, A, B]
  }

  object Prj {

    sealed trait NonTerminal[**[_,_], T, A, B] extends Prj[**, T, A, B] {
      def andThenNT[C](that: NonTerminal[**, T, B, C]): NonTerminal[**, T, A, C] =
        (this.isId map {
          ev => that.castA(ev)
        }) orElse (that.isId map {
          ev => this.castB(ev)
        }) orElse this.visit(new this.OptVisitor[NonTerminal[**, T, A, C]] {
          // TODO handle anything ending in product type, not just Par
          override def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit
              ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B) =
            (that.isFst[B1, B2](ev2.flip) map {
              ev => (Fst[A1, A2] andThenNT p.p1).castA(ev1).castB(ev)
            }) orElse (that.isSnd[B1, B2](ev2.flip) map {
              ev => (Snd[A1, A2] andThenNT p.p2).castA(ev1).castB(ev)
            })
        }) getOrElse (
          Prj.AndThen(this, that)
        )

      final def gcdNT[C](that: NonTerminal[**, T, A, C]): APair[NonTerminal[**, T, A, ?], λ[a => (NonTerminal[**, T, a, B], NonTerminal[**, T, a, C])]] = {
        type τ[X, Y] = NonTerminal[**, T, X, Y]

        def ret[X, P, Y, Z](p: τ[X, P], q1: τ[P, Y], q2: τ[P, Z]) =
          APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])], P](p, (q1, q2))

        def flipRet[X, Y, Z](r: APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]]): APair[τ[X, ?], λ[a => (τ[a, Z], τ[a, Y])]] =
          APair.of[τ[X, ?], λ[a => (τ[a, Z], τ[a, Y])]](r._1, (r._2._2, r._2._1))

        def seq[X, Y](ps: AList[τ, X, Y]): τ[X, Y] = ps match {
          case ev @ ANil() => Prj.Id[**, T, X].castB(ev.leibniz)
          case ACons(h, t) => h andThenNT seq(t)
        }

        def go[X, Y, Z](ps: AList[τ, X, Y], qs: AList[τ, X, Z]): APair[τ[X, ?], λ[a => (τ[a, Y], τ[a, Z])]] =
          ps match {
            case ev @ ANil() => ret(Prj.Id[**, T, X], Prj.Id[**, T, X].castB(ev.leibniz), seq(qs))
            case ps @ ACons(ph, pt) => qs match {
              case ev @ ANil() => ret(Prj.Id[**, T, X], seq(ps), Prj.Id[**, T, X].castB(ev.leibniz))
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
                        ret[X, Y ** Z, Y, Z](Prj.par(seq(pt), seq(qt)).castA[X], Fst[Y, Z], Snd[Y, Z])
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
                        ret[X, Z ** Y, Y, Z](Prj.par(seq(qt), seq(pt)).castA[X], Snd[Z, Y], Fst[Z, Y])
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
                            ret(Prj.par(r1, p2).castA(ev1), Prj.par(r1p, Id[pt12.B]).castB(ev3), Fst[r1pq.A, pt12.B] andThenNT r1q)
                          }
                          def apply[U](q: Snd[U, qs.Joint])(implicit ev: X === (U ** qs.Joint)) = {
                            val r2pq = p2 gcdNT seq(qt).castA[A2](ev1.flip.andThen(ev).snd)
                            val (r2, (r2p, r2q)) = (r2pq._1, r2pq._2)
                            ret(Prj.par(p1, r2).castA(ev1), Prj.par(Id[pt12.A], r2p).castB(ev3), Snd[pt12.A, r2pq.A] andThenNT r2q)
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
                                ret(Prj.par(r1, r2).castA(ev1), Prj.par(r1p, r2p).castB(ev3), Prj.par(r1q, r2q).castB(ev6))
                            }
                        })
                    }
                })
            }
          }
        go[A, B, C](AList(this), AList(that))
      }

      /** Helper to create return value for [[#gcd]]. */
      private[Prj] def gcdRet[X, C](p: NonTerminal[**, T, A, X], q: NonTerminal[**, T, X, B], r: NonTerminal[**, T, X, C]) =
        APair[NonTerminal[**, T, A, ?], λ[a => (NonTerminal[**, T, a, B], NonTerminal[**, T, a, C])], X](p, (q, r))

      /** Helper to create return value for [[#gcd]] that represents no (non-trivial) common prefix. */
      private[Prj] def noGcd[C](that: NonTerminal[**, T, A, C]): APair[NonTerminal[**, T, A, ?], λ[a => (NonTerminal[**, T, a, B], NonTerminal[**, T, a, C])]] =
        gcdRet(Prj.Id[**, T, A], this, that)

      private[Prj] def gcdFlip[C](that: NonTerminal[**, T, A, C]): APair[NonTerminal[**, T, A, ?], λ[a => (NonTerminal[**, T, a, C], NonTerminal[**, T, a, B])]] = {
        val x = gcdNT(that)
        that.gcdRet(x._1, x._2._2, x._2._1)
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
      def split[A1, A2](implicit ev: A === (A1 ** A2)): Either3[
        NonTerminal[**, T, A1, B],
        A2Pair[
          λ[(b1, b2) => (NonTerminal[**, T, A1, b1], NonTerminal[**, T, A2, b2])],
          λ[(b1, b2) => (b1 ** b2) === B]
        ],
        NonTerminal[**, T, A2, B]
      ]

      /** Helper to create return value for [[#split]]. */
      private[Prj] def splitRet[A1, A2, B1, B2](p1: NonTerminal[**, T, A1, B1], p2: NonTerminal[**, T, A2, B2])(implicit ev: (B1 ** B2) === B) =
        A2Pair[
          λ[(b1, b2) => (NonTerminal[**, T, A1, b1], NonTerminal[**, T, A2, b2])],
          λ[(b1, b2) => (b1 ** b2) === B],
          B1, B2
        ]((p1, p2), ev)

      /**
       * Permutes input `A` into parts `B ** Y`, for some `Y`.
       * If this projection is an identity projection, returns evidence that `A` = `B`.
       */
      def toShuffle: Either[A === B, Exists[λ[y => Shuffle[**, A, B ** y]]]]

      protected def shuffle[Y](s: Shuffle[**, A, B ** Y]): Exists[λ[y => Shuffle[**, A, B ** y]]] =
        Exists[λ[y => Shuffle[**, A, B ** y]], Y](s)
    }

    case class Fst[**[_,_], T, A, B]() extends NonTerminal[**, T, A ** B, A] {
      def visit[R](v: Visitor[R]): R = v(this)

      def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): A === X =
        Leibniz.force[Nothing, Any, A, X]

      def unital(implicit ev: (A ** B) === T): A === T =
        sys.error("impossible")

      override def isFst[X, Y](implicit ev: (A ** B) === (X ** Y)): Option[X === A] =
        Some(ev.fst.flip)

      def split[A1, A2](implicit ev: (A ** B) === (A1 ** A2)) =
        Left3(Id().castB(ev.fst.flip))

      def toShuffle: Either[(A ** B) === A, Exists[λ[y => Shuffle[**, A ** B, A ** y]]]] =
        Right(shuffle(Shuffle.Id[**, A ** B]()))
    }

    case class Snd[**[_,_], T, A, B]() extends NonTerminal[**, T, A ** B, B] {
      def visit[R](v: Visitor[R]): R = v(this)

      def deriveLeibniz[X, Y](implicit ev: (A ** B) === (X ** Y)): B === Y =
        Leibniz.force[Nothing, Any, B, Y]

      def unital(implicit ev: (A ** B) === T): B === T =
        sys.error("impossible")

      override def isSnd[X, Y](implicit ev: (A ** B) === (X ** Y)): Option[Y === B] =
        Some(ev.snd.flip)

      def split[A1, A2](implicit ev: (A ** B) === (A1 ** A2)) =
        Right3(Id().castB(ev.snd.flip))

      def toShuffle: Either[(A ** B) === B, Exists[λ[y => Shuffle[**, A ** B, B ** y]]]] =
        Right(shuffle(Shuffle.Swap[**, A, B]()))
    }

    case class Par[**[_,_], T, A1, A2, B1, B2](p1: NonTerminal[**, T, A1, B1], p2: NonTerminal[**, T, A2, B2]) extends NonTerminal[**, T, A1 ** A2, B1 ** B2] {
      def visit[R](v: Visitor[R]): R = v(this)

      def unital(implicit ev: (A1 ** A2) === T): (B1 ** B2) === T =
        sys.error("impossible")

      def split[X1, X2](implicit ev: (A1 ** A2) === (X1 ** X2)) =
        Middle3(splitRet(p1.castA(ev.fst.flip), p2.castA(ev.snd.flip)))

      def toShuffle: Either[(A1 ** A2) === (B1 ** B2), Exists[λ[y => Shuffle[**, A1 ** A2, (B1 ** B2) ** y]]]] =
        (p1.toShuffle, p2.toShuffle) match {
          case (Left(ev1), Left(ev2)) =>
            Left(ev1 lift2[**] ev2)
          case (Left(ev1), Right(s2)) =>
            Right(shuffle[s2.A](Shuffle.par(Shuffle.Id[**, A1]().castB(ev1), s2.value) andThen Shuffle.AssocRL()))
          case (Right(s1), Left(ev2)) =>
            Right(shuffle[s1.A](
              Shuffle.par(s1.value, Shuffle.Id[**, A2]().castB(ev2)) andThen
              Shuffle.AssocLR() andThen
              Shuffle.par(Shuffle.Id(), Shuffle.Swap()) andThen
              Shuffle.AssocRL()
            ))
          case (Right(s1), Right(s2)) =>
            Right(shuffle[s1.A ** s2.A](
              Shuffle.par(s1.value, s2.value) andThen
              Shuffle.AssocLR() andThen
              Shuffle.par(
                Shuffle.Id(),
                Shuffle.AssocRL() andThen Shuffle.par(Shuffle.Swap[**, s1.A, B2](), Shuffle.Id[**, s2.A]()) andThen Shuffle.AssocLR()
              ) andThen
              Shuffle.AssocRL()
            ))
        }
    }

    case class Unit[**[_,_], T, A]() extends Prj[**, T, A, T] {
      def visit[R](v: Visitor[R]): R = v(this)

      def unital(implicit ev: A === T): T === T =
        implicitly

      override def isUnit: Option[T === T] = Some(implicitly)
      def switchTerminal: (T === T) Either NonTerminal[**, T, A, T] = Left(implicitly)
    }

    case class Id[**[_,_], T, A]() extends NonTerminal[**, T, A, A] {
      def visit[R](v: Visitor[R]): R = v(this)

      def unital(implicit ev: A === T): A === T =
        ev

      override def isId: Option[A === A] = Some(implicitly)

      def split[A1, A2](implicit ev: A === (A1 ** A2)) =
        Middle3(splitRet(Id[**, T, A1](), Id[**, T, A2]())(ev.flip))

      def toShuffle: Either[A === A, Exists[λ[y => Shuffle[**, A, A ** y]]]] =
        Left(implicitly)
    }

    case class AndThen[**[_,_], T, A, B, C](p: NonTerminal[**, T, A, B], q: NonTerminal[**, T, B, C]) extends NonTerminal[**, T, A, C] {
      def visit[R](v: Visitor[R]): R = v(this)

      def unital(implicit ev: A === T): C === T =
        q.unital(p.unital)

      def split[A1, A2](implicit ev: A === (A1 ** A2)) =
        p.split[A1, A2] match {
          case Left3(p) => Left3(AndThen(p, q))
          case Right3(p) => Right3(AndThen(p, q))
          case Middle3(p12) =>
            val ((p1, p2), ev) = (p12._1, p12._2)
            q.castA(ev).split[p12.A, p12.B] match {
              case Left3(q) => Left3(AndThen(p1, q))
              case Right3(q) => Right3(AndThen(p2, q))
              case Middle3(q12) => Middle3(splitRet(AndThen(p1, q12._1._1), AndThen(p2, q12._1._2))(q12._2))
            }
        }

      def toShuffle: Either[A === C, Exists[λ[y => Shuffle[**, A, C ** y]]]] =
        p.toShuffle match {
          case Left(ev) => q.castA(ev).toShuffle
          case Right(s) => q.toShuffle match {
            case Left(ev) => Right(ev.subst[λ[α => Exists[λ[y => Shuffle[**, A, α ** y]]]]](s))
            case Right(t) => Right(shuffle[t.A ** s.A](s.value andThen Shuffle.par(t.value, Shuffle.Id()) andThen Shuffle.AssocLR()))
          }
        }
    }

    trait Visitor[**[_,_], T, A, B, R] {
      type π[X, Y] = Prj[**, T, X, Y]
      type Π[X, Y] = Prj.NonTerminal[**, T, X, Y]

      type Fst[X, Y] = Prj.Fst[**, T, X, Y]
      type Snd[X, Y] = Prj.Snd[**, T, X, Y]
      type Par[X1, X2, Y1, Y2] = Prj.Par[**, T, X1, X2, Y1, Y2]
      type Unit[X] = Prj.Unit[**, T, X]
      type Id[X] = Prj.Id[**, T, X]
      type AndThen[X, Y, Z] = Prj.AndThen[**, T, X, Y, Z]

      def Fst[X, Y]                                         : Fst[X, Y]           = Prj.Fst()
      def Snd[X, Y]                                         : Snd[X, Y]           = Prj.Snd()
      def Par[X1, X2, Y1, Y2](p1: Π[X1, Y1], p2: Π[X2, Y2]) : Par[X1, X2, Y1, Y2] = Prj.Par(p1, p2)
      def Unit[X]                                           : Unit[X]             = Prj.Unit()
      def Id[X]                                             : Id[X]               = Prj.Id()
      def AndThen[X, Y, Z](p: Π[X, Y], q: Π[Y, Z])          : AndThen[X, Y, Z]    = Prj.AndThen(p, q)

      def apply[Y](p: Fst[B, Y])(implicit ev: A === (B ** Y)): R
      def apply[X](p: Snd[X, B])(implicit ev: A === (X ** B)): R
      def apply[A1, A2, B1, B2](p: Par[A1, A2, B1, B2])(implicit ev1: A === (A1 ** A2), ev2: (B1 ** B2) === B): R
      def apply(p: Unit[A])(implicit ev: T === B): R
      def apply(p: Id[A])(implicit ev: A === B): R
      def apply[X](p: AndThen[A, X, B]): R
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
  }

  /**
   * Represents projection of an arrow type.
   * The result of such projection is an arrow that takes more/bigger
   * inputs than it needs or, if its output is again an arrow type,
   * artificially weakens the produced arrow (again by a projection)
   * before returning.
   *
   * During optimization propagated forward i.e. deferred as much as possible.
   * (If we keep stronger functions, we need to feed them fewer arguments
   * and thus possibly save by not having to produce those arguments.)
   */
  sealed trait FPrj[**[_,_], T, ->[_,_], F, G] {
    type π[X, Y] = FPrj[**, T, ->, X, Y]
    type ArgPrj[X, Y] = FPrj.ArgPrj[**, T, ->, X, Y]
    type Visitor[R] = FPrj.Visitor[**, T, ->, F, G, R]
    type OptVisitor[R] = FPrj.OptVisitor[**, T, ->, F, G, R]

    def visit[R](v: Visitor[R]): R

    def castA[E](implicit ev: E === F): π[E, G] = ev.flip.subst[π[?, G]](this)
    def castB[H](implicit ev: G === H): π[F, H] = ev.subst[π[F, ?]](this)

    def andThen[H](that: π[G, H]): π[F, H] =
      (this.isId map {
        ev => that.castA(ev)
      }) orElse (that.isId map {
        ev => this.castB(ev)
      }) getOrElse (
        FPrj.AndThen(this, that)
      )

    def after[E](that: π[E, F]): π[E, G] =
      that andThen this

    def isId: Option[F === G] = visit(new OptVisitor[F === G] {
      override def apply(p: Id[F])(implicit ev: F === G) = Some(ev)
    })

    def asStrongerArg[H]: FPrj[**, T, ->, G -> H, F -> H] =
      FPrj.StrongerArg(FPrj.ArgPrj(this))

    def asWeakerRes[A]: FPrj[**, T, ->, A -> F, A -> G] =
      FPrj.WeakerRes(this)

    def rsplit[X, Y](implicit ev: (X ** Y) === G): A2Pair[
                                                     λ[(x, y) => F === (x ** y)],
                                                     λ[(x, y) => (π[x, X], π[y, Y])]]

    protected def rsplitRet[X, Y, G1, G2](ev: F === (X ** Y), p1: π[X, G1], p2: π[Y, G2]) =
      A2Pair[λ[(x, y) => F === (x ** y)], λ[(x, y) => (π[x, G1], π[y, G2])], X, Y](ev, (p1, p2))

    protected def rsplitRet[X, Y, G1, G2](p1: π[X, G1], p2: π[Y, G2]) =
      A2Pair[λ[(x, y) => (X ** Y) === (x ** y)], λ[(x, y) => (π[x, G1], π[y, G2])], X, Y](implicitly, (p1, p2))

    def splitIO[X, Y](implicit ev: (X -> Y) === G): A2Pair[
                                                      λ[(x, y) => π[F, x -> y]],
                                                      λ[(x, y) => (ArgPrj[X, x], π[y, Y])] ]

    protected def splitIORet[X, Y, X0, Y0](p: π[F, X0 -> Y0], p1: ArgPrj[X, X0], p2: π[Y0, Y]) =
      A2Pair[λ[(x, y) => π[F, x -> y]], λ[(x, y) => (ArgPrj[X, x], π[y, Y])], X0, Y0](p, (p1, p2))

    def takesExtraArg[X, Y](implicit ev: (X -> Y) === G): Option[π[F, Y]]

    def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, F, G] =
      visit(new Visitor[FreeCCC[:=>:, **, T, ->, F, G]] {
        def apply[X](p: AndThen[F, X, G]) = FreeCCC.andThen(p.p.toFreeCCC, p.q.toFreeCCC)
        def apply(p: Id[F])(implicit ev: F === G) = FreeCCC.id.castB
        def apply[F1, F2, G1, G2](p: Par[F1, F2, G1, G2])(implicit ev1: F === (F1 ** F2), ev2: (G1 ** G2) === G) =
          FreeCCC.parallel(p.p1.toFreeCCC[:=>:], p.p2.toFreeCCC[:=>:]).castA[F].castB[G]
        def apply[Z](p: ExtraArg[F, Z])(implicit ev: (Z -> F) === G) = FreeCCC.constA.castB
        def apply[X, Y, X1](p: StrongerArg[X, Y, X1])(implicit ev1: F === (X -> Y), ev2: (X1 -> Y) === G) = {
          val f0 = p.p.toFreeCCC[:=>:]
          curry(parallel(id[:=>:, **, T, ->, X -> Y], f0) andThen eval).castA[F].castB[G]
        }
        def apply[X, Y, Y0](p: WeakerRes[X, Y, Y0])(implicit ev1: F === (X -> Y), ev2: (X -> Y0) === G) = {
          val f0 = p.p.toFreeCCC[:=>:]
          curry(eval[:=>:, **, T, ->, X, Y] andThen f0).castA[F].castB[G]
        }
      })

    private[FPrj] implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
      def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
      def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
    }

    private[FPrj] implicit class ArrowLeibnizOps[X1, X2, Y1, Y2](ev: (X1 -> X2) === (Y1 -> Y2)) {
      def in: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
      def out: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
    }
  }

  object FPrj {
    case class AndThen[**[_,_], T, ->[_,_], F, G, H](p: FPrj[**, T, ->, F, G], q: FPrj[**, T, ->, G, H]) extends FPrj[**, T, ->, F, H] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === H) = {
        val q012 = q.rsplit[X, Y]
        val (ev1, (q1, q2)) = (q012._1, q012._2)
        val p012 = p.castB(ev1).rsplit[q012.A, q012.B]
        val (ev2, (p1, p2)) = (p012._1, p012._2)
        rsplitRet(ev2, p1 andThen q1, p2 andThen q2)
      }

      def splitIO[X, Y](implicit ev: (X -> Y) === H) = {
        val q012 = q.splitIO[X, Y]
        val (q0, (q1, q2)) = (q012._1, q012._2)
        q0.isId match {
          case Some(ev1) =>
            val p012 = p.castB(ev1).splitIO[q012.A, q012.B]
            val (p0, (p1, p2)) = (p012._1, p012._2)
            splitIORet(p0, q1 andThen p1, p2 andThen q2)
          case None =>
            splitIORet(p andThen q0, q1, q2)
        }
      }

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === H) =
        (q.takesExtraArg[X, Y] map {
          q0 => AndThen(p, q0)
        }) orElse {
          val q012 = q.splitIO[X, Y]
          val (q0, (q1, q2)) = (q012._1, q012._2)
          q0.isId flatMap {
            ev1 => p.castB(ev1).takesExtraArg[q012.A, q012.B] map {
              p0 => p0 andThen q2
            }
          }
        }
    }
    case class Id[**[_,_], T, ->[_,_], F]() extends FPrj[**, T, ->, F, F] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === F) =
        rsplitRet(ev.flip, Id(), Id())

      def splitIO[X, Y](implicit ev: (X -> Y) === F) =
        splitIORet(Id[**, T, ->, F].castB(ev.flip), ArgId(), Id())

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === F) =
        None
    }
    case class Par[**[_,_], T, ->[_,_], F1, G1, F, G](p1: FPrj[**, T, ->, F1, F], p2: FPrj[**, T, ->, G1, G]) extends FPrj[**, T, ->, F1 ** G1, F ** G] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === (F ** G)) =
        rsplitRet(p1.castB(ev.flip.fst), p2.castB(ev.flip.snd))

      def splitIO[X, Y](implicit ev: (X -> Y) === (F ** G)) =
        sys.error("Impossible")

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === (F ** G)) =
        sys.error("Impossible")
    }
    case class ExtraArg[**[_,_], T, ->[_,_], A, Z]() extends FPrj[**, T, ->, A, Z -> A] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === (Z -> A)) =
        sys.error("Impossible")

      def splitIO[X, Y](implicit ev: (X -> Y) === (Z -> A)) =
        splitIORet(ExtraArg[**, T, ->, A, Z].castB(ev.flip), ArgId(), Id())

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === (Z -> A)) =
        Some(Id[**, T, ->, Y]().castA(ev.out.flip))
    }
    case class StrongerArg[**[_,_], T, ->[_,_], A, B, A1](p: FPrj.ArgPrj[**, T, ->, A1, A]) extends FPrj[**, T, ->, A -> B, A1 -> B] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === (A1 -> B)) =
        sys.error("Impossible")

      def splitIO[X, Y](implicit ev: (X -> Y) === (A1 -> B)) =
        splitIORet(Id[**, T, ->, A -> B], p.castA(ev.in), Id().castB(ev.flip.out))

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === (A1 -> B)) =
        None
    }
    case class WeakerRes[**[_,_], T, ->[_,_], A, F, F0](p: FPrj[**, T, ->, F, F0]) extends FPrj[**, T, ->, A -> F, A -> F0] {
      def visit[R](v: Visitor[R]): R = v(this)

      def rsplit[X, Y](implicit ev: (X ** Y) === (A -> F0)) =
        sys.error("Impossible")

      def splitIO[X, Y](implicit ev: (X -> Y) === (A -> F0)) =
        splitIORet(Id[**, T, ->, A -> F], ArgId().castB(ev.in), p.castB(ev.flip.out))

      def takesExtraArg[X, Y](implicit ev: (X -> Y) === (A -> F0)) =
        None
    }

    sealed trait ArgPrj[**[_,_], T, ->[_,_], A1, A] {
      def andThen[B](that: ArgPrj[**, T, ->, A, B]): ArgPrj[**, T, ->, A1, B] =
        ArgAndThen(this, that) // TODO check for identities

      def castA[A0](implicit ev: A0 === A1): ArgPrj[**, T, ->, A0, A] =
        ev.flip.subst[ArgPrj[**, T, ->, ?, A]](this)

      def castB[B0](implicit ev: A === B0): ArgPrj[**, T, ->, A1, B0] =
        ev.subst[ArgPrj[**, T, ->, A1, ?]](this)

      def asStrongerArg[B]: FPrj[**, T, ->, A -> B, A1 -> B] =
        FPrj.StrongerArg(this)

      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, A1, A]
    }
    case class WrapPrj[**[_,_], T, ->[_,_], A1, A](p: Prj[**, T, A1, A]) extends ArgPrj[**, T, ->, A1, A] {
      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, A1, A] = p.toFreeCCC[:=>:, ->]
    }
    case class WrapFPrj[**[_,_], T, ->[_,_], A1, A](p: FPrj[**, T, ->, A1, A]) extends ArgPrj[**, T, ->, A1, A] {
      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, A1, A] = p.toFreeCCC[:=>:]
    }
    case class ArgAndThen[**[_,_], T, ->[_,_], F, G, H](p: ArgPrj[**, T, ->, F, G], q: ArgPrj[**, T, ->, G, H]) extends ArgPrj[**, T, ->, F, H] {
      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, F, H] = FreeCCC.andThen(p.toFreeCCC[:=>:], q.toFreeCCC[:=>:])
    }
    case class ArgId[**[_,_], T, ->[_,_], F]() extends ArgPrj[**, T, ->, F, F] {
      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, F, F] = FreeCCC.id
    }
    case class ArgPar[**[_,_], T, ->[_,_], F1, G1, F, G](p1: ArgPrj[**, T, ->, F1, F], p2: ArgPrj[**, T, ->, G1, G]) extends ArgPrj[**, T, ->, F1 ** G1, F ** G] {
      def toFreeCCC[:=>:[_,_]]: FreeCCC[:=>:, **, T, ->, F1 ** G1, F ** G] =
        FreeCCC.parallel(p1.toFreeCCC[:=>:], p2.toFreeCCC[:=>:])
    }

    object ArgPrj {
      def apply[**[_,_], T, ->[_,_], A1, A](p: Prj[**, T, A1, A]): ArgPrj[**, T, ->, A1, A] = WrapPrj(p)
      def apply[**[_,_], T, ->[_,_], A1, A](p: FPrj[**, T, ->, A1, A]): ArgPrj[**, T, ->, A1, A] = WrapFPrj(p)
    }

    trait Visitor[**[_,_], T, ->[_,_], F, G, R] {
      type AndThen[X, Y, Z]      = FPrj.AndThen    [**, T, ->, X, Y, Z]
      type Id[X]                 = FPrj.Id         [**, T, ->, X]
      type Par[X, Y, x, y]       = FPrj.Par        [**, T, ->, X, Y, x, y]
      type ExtraArg[X, Z]        = FPrj.ExtraArg   [**, T, ->, X, Z]
      type StrongerArg[X, Y, X1] = FPrj.StrongerArg[**, T, ->, X, Y, X1]
      type WeakerRes[X, Y, Y0]   = FPrj.WeakerRes  [**, T, ->, X, Y, Y0]

      def apply[X](p: AndThen[F, X, G]): R
      def apply(p: Id[F])(implicit ev: F === G): R
      def apply[F1, F2, G1, G2](p: Par[F1, F2, G1, G2])(implicit ev1: F === (F1 ** F2), ev2: (G1 ** G2) === G): R
      def apply[Z](p: ExtraArg[F, Z])(implicit ev: (Z -> F) === G): R
      def apply[X, Y, X1](p: StrongerArg[X, Y, X1])(implicit ev1: F === (X -> Y), ev2: (X1 -> Y) === G): R
      def apply[X, Y, Y0](p: WeakerRes[X, Y, Y0])(implicit ev1: F === (X -> Y), ev2: (X -> Y0) === G): R
    }

    trait OptVisitor[**[_,_], T, ->[_,_], F, G, R] extends Visitor[**, T, ->, F, G, Option[R]] {
      def apply[X](p: AndThen[F, X, G])                                                                        = Option.empty[R]
      def apply(p: Id[F])(implicit ev: F === G)                                                                = Option.empty[R]
      def apply[F1, F2, G1, G2](p: Par[F1, F2, G1, G2])(implicit ev1: F === (F1 ** F2), ev2: (G1 ** G2) === G) = Option.empty[R]
      def apply[Z](p: ExtraArg[F, Z])(implicit ev: (Z -> F) === G)                                             = Option.empty[R]
      def apply[X, Y, X1](p: StrongerArg[X, Y, X1])(implicit ev1: F === (X -> Y), ev2: (X1 -> Y) === G)        = Option.empty[R]
      def apply[X, Y, Y0](p: WeakerRes[X, Y, Y0])(implicit ev1: F === (X -> Y), ev2: (X -> Y0) === G)          = Option.empty[R]
    }
  }

  sealed trait Expansion[**[_,_], U, A, A1] {
    type Exp[X, X1] = Expansion[**, U, X, X1]
    type Visitor[R] = Expansion.Visitor[**, U, A, A1, R]

    def visit[R](v: Visitor[R]): R
    def toFreeCCC[:=>:[_,_], :->:[_,_]]: FreeCCC[:=>:, **, U, :->:, A, A1]
    def isId: Option[A === A1] = None

    def rsplit[X, Y](implicit ev: (X ** Y) === A1): A2Pair[
                                                      λ[(x, y) => Exp[A, x ** y]],
                                                      λ[(x, y) => (Exp[x, X], Exp[y, Y])]]

    protected def rsplitRet[x, y, X, Y](i0: Exp[A, x ** y], i1: Exp[x, X], i2: Exp[y, Y]) =
      A2Pair[λ[(α, β) => Exp[A, α ** β]], λ[(α, β) => (Exp[α, X], Exp[β, Y])], x, y](i0, (i1, i2))

    def castA[A0](implicit ev: A0 === A): Expansion[**, U, A0, A1] = ev.flip.subst[Expansion[**, U, ?, A1]](this)
    def castB[A2](implicit ev: A1 === A2): Expansion[**, U, A, A2] = ev.subst[Expansion[**, U, A, ?]](this)
    def andThen[A2](that: Expansion[**, U, A1, A2]): Expansion[**, U, A, A2] = Expansion.andThen(this, that)

    protected implicit class ProductLeibnizOps[X1, X2, Y1, Y2](ev: (X1 ** X2) === (Y1 ** Y2)) {
      def fst: X1 === Y1 = Leibniz.force[Nothing, Any, X1, Y1]
      def snd: X2 === Y2 = Leibniz.force[Nothing, Any, X2, Y2]
    }
  }
  object Expansion {
    case class Diag[**[_,_], U, A]() extends Expansion[**, U, A, A ** A] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.diag
      override def rsplit[X, Y](implicit ev: (X ** Y) === (A ** A)) =
        rsplitRet(this, Id().castB(ev.fst.flip), Id().castB(ev.snd.flip))
    }

    case class UnitL[**[_,_], U, A]() extends Expansion[**, U, A, U ** A] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.Prod(FreeCCC.Terminal(), FreeCCC.Id())
      override def rsplit[X, Y](implicit ev: (X ** Y) === (U ** A)) =
        rsplitRet(this, Id().castB(ev.fst.flip), Id().castB(ev.snd.flip))
    }

    case class UnitR[**[_,_], U, A]() extends Expansion[**, U, A, A ** U] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.Prod(FreeCCC.Id(), FreeCCC.Terminal())
      override def rsplit[X, Y](implicit ev: (X ** Y) === (A ** U)) =
        rsplitRet(this, Id().castB(ev.fst.flip), Id().castB(ev.snd.flip))
    }

    case class Id[**[_,_], U, A]() extends Expansion[**, U, A, A] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def isId = Some(Leibniz.refl)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.Id()
      override def rsplit[X, Y](implicit ev: (X ** Y) === A) =
        rsplitRet(this.castB(ev.flip), Id(), Id())
    }

    case class AndThen[**[_,_], U, A, B, C](i: Expansion[**, U, A, B], j: Expansion[**, U, B, C]) extends Expansion[**, U, A, C] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.andThen(i.toFreeCCC, j.toFreeCCC)
      override def rsplit[X, Y](implicit ev: (X ** Y) === C) = {
        val j012 = j.rsplit[X, Y]
        val (j0, (j1, j2)) = (j012._1, j012._2)
        j0.isId match {
          case Some(ev1) =>
            val i012 = i.rsplit(ev1.flip)
            val (i0, (i1, i2)) = (i012._1, i012._2)
            rsplitRet(i0, i1 andThen j1, i2 andThen j2)
          case None =>
            rsplitRet(i andThen j0, j1, j2)
        }
      }
    }

    case class Par[**[_,_], U, A, A1, B, B1](i1: Expansion[**, U, A, A1], i2: Expansion[**, U, B, B1]) extends Expansion[**, U, A ** B, A1 ** B1] {
      override def visit[R](v: Visitor[R]) = v(this)
      override def toFreeCCC[:=>:[_,_], :->:[_,_]] = FreeCCC.parallel(i1.toFreeCCC, i2.toFreeCCC)
      override def rsplit[X, Y](implicit ev: (X ** Y) === (A1 ** B1)) =
        rsplitRet(Id[**, U, A ** B](), i1.castB(ev.fst.flip), i2.castB(ev.snd.flip))
    }

    trait Visitor[**[_,_], U, A, A1, R] {
      type Diag[X]           = Expansion.Diag[**, U, X]
      type UnitL[X]          = Expansion.UnitL[**, U, X]
      type UnitR[X]          = Expansion.UnitR[**, U, X]
      type Id[X]             = Expansion.Id[**, U, X]
      type AndThen[X, Y, Z]  = Expansion.AndThen[**, U, X, Y, Z]
      type Par[X, X1, Y, Y1] = Expansion.Par[**, U, X, X1, Y, Y1]

      def apply(i: Diag[A])(implicit ev: (A ** A) === A1): R
      def apply(i: UnitL[A])(implicit ev: (U ** A) === A1): R
      def apply(i: UnitR[A])(implicit ev: (A ** U) === A1): R
      def apply(i: Id[A])(implicit ev: A === A1): R
      def apply[X](i: AndThen[A, X, A1]): R
      def apply[X, X1, Y, Y1](i: Par[X, X1, Y, Y1])(implicit ev1: A === (X ** Y), ev2: (X1 ** Y1) === A1): R
    }

    def par[**[_,_], U, A, A1, B, B1](i1: Expansion[**, U, A, A1], i2: Expansion[**, U, B, B1]): Expansion[**, U, A ** B, A1 ** B1] =
      (i1.isId, i2.isId) match {
        case (Some(ev1), Some(ev2)) => Id[**, U, A ** B]().castB(ev1 lift2 ev2)
        case _ => Par(i1, i2)
      }

    def andThen[**[_,_], U, A, B, C](i: Expansion[**, U, A, B], j: Expansion[**, U, B, C]): Expansion[**, U, A, C] =
      (i.isId map { ev => j.castA(ev) }) orElse
      (j.isId map { ev => i.castB(ev) }) getOrElse
      AndThen(i, j)
  }

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
  }

  import scalaz.Writer
  import scalaz.@@
  import scalaz.Tags.Disjunction
  type Improvement[A] = Writer[Boolean @@ Disjunction, A]
  def improved[A](a: A) = Writer(Disjunction(true), a)
  def unchanged[A](a: A) = Writer(Disjunction(false), a)
  implicit class ImprovementOps[A](i: Improvement[A]) {
    def getImproved: Option[A] = if(Disjunction.unwrap(i.run._1)) Some(i.run._2) else None
  }

  implicit def cccInstance[:->:[_, _], &[_, _], T, H[_, _]]: CCC.Aux[FreeCCC[:->:, &, T, H, ?, ?], &, T, H] =
    new CCC[FreeCCC[:->:, &, T, H, ?, ?]] {
      type **[A, B] = A & B
      type Unit = T
      type Hom[A, B] = H[A, B]

      type ->[A, B] = FreeCCC[:->:, &, T, H, A, B]

      def id[A]: A -> A = FreeCCC.id
      def compose[A, B, C](f: B -> C, g: A -> B): A -> C = FreeCCC.compose(f, g)
      def fst[A, B]: (A & B) -> A = FreeCCC.fst
      def snd[A, B]: (A & B) -> B = FreeCCC.snd
      def prod[A, B, C](f: A -> B, g: A -> C): A -> (B & C) = FreeCCC.prod(f, g)
      def terminal[A]: A -> T = FreeCCC.terminal
      def curry[A, B, C](f: (A & B) -> C): A -> H[B, C] = FreeCCC.curry(f)
      def uncurry[A, B, C](f: A -> H[B, C]): (A & B) -> C = FreeCCC.uncurry(f)
    }

  /* Smart constructors */

  def lift[:->:[_, _], **[_, _], T, H[_, _], A, B](f: A :->: B): FreeCCC[:->:, **, T, H, A, B] = Lift(f)

  // Cartesian closed operations
  def id[:->:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:->:, **, T, H, A, A] = Id()
  def compose[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, B, C], g: FreeCCC[:->:, **, T, H, A, B]): FreeCCC[:->:, **, T, H, A, C] = sequence(g :: AList(f))
  def fst[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, (A**B), A] = Fst()
  def snd[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, (A**B), B] = Snd()
  def prod[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, B], g: FreeCCC[:->:, **, T, H, A, C]): FreeCCC[:->:, **, T, H, A, (B**C)] =
    (f.isFst, g.isSnd) match {
      case (Some(ev1), Some(ev2)) => id[:->:, **, T, H, A].castB(Leibniz.force[Nothing, Any, A, B ** C])
      case _ => Prod(f, g)
    }
  def terminal[:->:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:->:, **, T, H, A, T] = Terminal()
  def curry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, (A**B), C]): FreeCCC[:->:, **, T, H, A, H[B, C]] = Curry(f)
  def uncurry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, H[B, C]]): FreeCCC[:->:, **, T, H, (A**B), C] = Uncurry(f)
  def const[:->:[_, _], **[_, _], T, H[_, _], Z, A, B](f: FreeCCC[:->:, **, T, H, A, B]): FreeCCC[:->:, **, T, H, Z, H[A, B]] = Const(f)


  // derived Cartesian closed operations

  def diag[:->:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:->:, **, T, H, A, (A ** A)] =
    prod(id, id)

  def parallel[:->:[_, _], **[_, _], T, H[_, _], A1, A2, B1, B2](
      f: FreeCCC[:->:, **, T, H, A1, B1],
      g: FreeCCC[:->:, **, T, H, A2, B2]
  ): FreeCCC[:->:, **, T, H, (A1**A2), (B1**B2)] =
    prod(compose(f, fst), compose(g, snd))

  def constA[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, A, H[B, A]] =
    curry(fst[:->:, **, T, H, A, B])

  def getConst[:->:[_, _], **[_, _], T, H[_, _], A, B](f: FreeCCC[:->:, **, T, H, T, H[A, B]]): FreeCCC[:->:, **, T, H, A, B] =
    compose(uncurry(f), prod(terminal[:->:, **, T, H, A], id[:->:, **, T, H, A]))

  def andThen[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, B], g: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    compose(g, f)

  def sequence[:->:[_, _], **[_, _], T, H[_, _], A, B](fs: AList[FreeCCC[:->:, **, T, H, ?, ?], A, B]): FreeCCC[:->:, **, T, H, A, B] = {
    // TODO: might also flatten Sequences
    fs.filterNot(ν[FreeCCC[:->:, **, T, H, ?, ?] ~~> λ[(a, b) => Option[a === b]]].apply[a, b](_.isId)) match {
      case ev @ ANil()   => id[:->:, **, T, H, A].castB(ev.leibniz)
      case ACons(f1, fs1) => fs1 match {
        case ev @ ANil() => f1.castB(ev.leibniz)
        case ACons(f2, fs2) => Sequence(f1 +: (f2 :: fs2))
      }
    }
  }

  def swap[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, A ** B, B ** A] =
    prod(snd, fst)

  def flipArg[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, (A**B), C]): FreeCCC[:->:, **, T, H, (B**A), C] =
    compose(f, prod(snd[:->:, **, T, H, B, A], fst[:->:, **, T, H, B, A]))

  def swapArgs[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, H[B, C]]): FreeCCC[:->:, **, T, H, B, H[A, C]] =
    curry(flipArg(uncurry(f)))

  def eval[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, H[A, B] ** A, B] =
    uncurry(id[:->:, **, T, H, H[A, B]])

  def assocR[:->:[_, _], **[_, _], T, H[_, _], A, B, C]: FreeCCC[:->:, **, T, H, ((A**B)**C), (A**(B**C))] = {
    val pa = compose(fst[:->:, **, T, H, A, B], fst[:->:, **, T, H, A**B, C])
    val pb = compose(snd[:->:, **, T, H, A, B], fst[:->:, **, T, H, A**B, C])
    val pc = snd[:->:, **, T, H, A**B, C]
    prod(pa, prod(pb, pc))
  }

  def assocL[:->:[_, _], **[_, _], T, H[_, _], A, B, C]: FreeCCC[:->:, **, T, H, (A**(B**C)), ((A**B)**C)] = {
    val pa = fst[:->:, **, T, H, A, B**C]
    val pb = compose(fst[:->:, **, T, H, B, C], snd[:->:, **, T, H, A, B**C])
    val pc = compose(snd[:->:, **, T, H, B, C], snd[:->:, **, T, H, A, B**C])
    prod(prod(pa, pb), pc)
  }

  private[FreeCCC] def genericRules[:->:[_, _], **[_, _], T, H[_, _]]: RewriteRule[:->:, **, T, H] = {
    type       RewriteRule = FreeCCC.      RewriteRule[:->:, **, T, H]
    type ClosedRewriteRule = FreeCCC.ClosedRewriteRule[:->:, **, T, H]

    RewriteRule.sequence[:->:, **, T, H](

      // Perform projections as soon as possible.
      // That is, don't carry along something that will not be used.
      // Forget it as soon as possible.
      ν[ClosedRewriteRule].rewrite[A, B](_.restrictResultTo(Prj.Id())),

      ν[ClosedRewriteRule].rewrite[A, B](_.deferExpansion(Expansion.Id())),

      ν[ClosedRewriteRule].rewrite[A, B](_.strengthenInput(FPrj.Id())),

      ν[ClosedRewriteRule].rewrite[A, B](_.shuffleResult(Shuffle.Id())),

      ν[ClosedRewriteRule].rewrite[A, B](f => f.visit(new BinTransformer[:->:, **, T, H, A, B] {
        override def apply   (f:     Lift[A, B])                              = None
        override def apply   (f:       Id[A]   )(implicit ev:        A === B) = None
        override def apply[X](f:      Fst[B, X])(implicit ev: A === (B ** X)) = None
        override def apply[X](f:      Snd[X, B])(implicit ev: A === (X ** B)) = None
        override def apply   (f: Terminal[A]   )(implicit ev:        T === B) = None

        override def apply[X, Y, Z](f: X :=>: Y, g: Y :=>: Z) = g.visit(new g.OptVisitor[X :=>: Z] {

          // flatten compositions
          override def apply(g: Sequence[Y, Z]) = Some(Sequence(f :: g.fs))

          // reduce `id . f` to `f`
          override def apply(g: Id[Y])(implicit ev: Y === Z) = Some(f.castB(ev))

          // reduce `terminal . f` to `terminal`
          override def apply(g: Terminal[Y])(implicit ev: T === Z) = Some((Terminal(): Terminal[X]).castB[Z])

          // reduce `f >>> const(g)` to `const(g)`
          override def apply[Z1, Z2](g: Const[Y, Z1, Z2])(implicit ev: H[Z1, Z2] === Z) = Some(Const(g.f).castB[Z])

          override def apply[P, Q](g: Prod[Y, P, Q])(implicit ev: (P ** Q) === Z) = {
            val g1s = g.f.asSequence
            val g2s = g.g.asSequence
            val (g1h, g1t) = (g1s.head, g1s.tail)
            val (g2h, g2t) = (g2s.head, g2s.tail)

            // rewrite `f >>> prod(curry(snd >>> h) >>> i, g2)`
            // to      `prod(curry(snd >>> h) >>> i, f >>> g2)`
            g1h.visit(new g1h.OptVisitor[X :=>: Z] {
              override def apply[R, S](g1h: Curry[Y, R, S])(implicit ev1: H[R, S] === g1s.A1) = {
                val g1hs = g1h.f.asSequence
                val (g1hh, g1ht) = (g1hs.head, g1hs.tail)

                g1hh.visit(new g1hh.OptVisitor[X :=>: Z] {
                  override def apply[U](g1hh: Snd[U, g1hs.A1])(implicit ev2: (Y ** R) === (U ** g1hs.A1)) = {
                    import g1hh.ProductLeibnizOps
                    val ev3: R === g1hs.A1 = ev2.snd
                    Some(Prod(andThen(Curry(andThen(Snd[X, R](), sequence(g1ht).castA(ev3))), sequence(g1t).castA(ev1)), f >>> g.g).castB[Z])
                  }
                })
              }
            }) orElse {
            // rewrite `f >>> prod(g1, curry(snd >>> h) >>> i)`
            // to      `prod(f >>> g1, curry(snd >>> h) >>> i)`
            g2h.visit(new g2h.OptVisitor[X :=>: Z] {
              override def apply[R, S](g2h: Curry[Y, R, S])(implicit ev1: H[R, S] === g2s.A1) = {
                val g2hs = g2h.f.asSequence
                val (g2hh, g2ht) = (g2hs.head, g2hs.tail)

                g2hh.visit(new g2hh.OptVisitor[X :=>: Z] {
                  override def apply[U](g2hh: Snd[U, g2hs.A1])(implicit ev2: (Y ** R) === (U ** g2hs.A1)) = {
                    import g2hh.ProductLeibnizOps
                    val ev3: R === g2hs.A1 = ev2.snd
                    Some(Prod(f >>> g.f, andThen(Curry(andThen(Snd[X, R](), sequence(g2ht).castA(ev3))), sequence(g2t).castA(ev1))).castB[Z])
                  }
                })
              }
            })
            }
          }

        }).orElse(                                   f.visit(new f.OptVisitor[X :=>: Z] {
          // flatten compositions
          override def apply(f: Sequence[X, Y]) = Some(Sequence(f.fs :+ g))

          // reduce `g . id` to `g`
          override def apply(f: Id[X])(implicit ev: X === Y) = Some(g.castA)

          override def apply[P, Q](p: Prod[X, P, Q])(implicit ev: (P ** Q) === Y) =
            g.ignoresFst[P, Q](ev.flip).map(h => h compose p.g) orElse
            g.ignoresSnd[P, Q](ev.flip).map(h => h compose p.f) orElse
            g.visit(new g.OptVisitor[X :=>: Z] {

              override def apply[R, S](rs: Prod[Y, R, S])(implicit ev1: (R ** S) === Z) = {
                (rs.f.ignoresSnd[P, Q](ev.flip) |@| rs.g.ignoresFst[P, Q](ev.flip))(
                  (pr, qs) => Prod(pr compose p.f, qs compose p.g).castB
                ) orElse
                (rs.f.ignoresFst[P, Q](ev.flip) |@| rs.g.ignoresSnd[P, Q](ev.flip))(
                  (qr, ps) => Prod(qr compose p.g, ps compose p.f).castB
                )
              }

              // rewrite `prod(e >>> curry(f), g) >>> uncurry(id)` to `prod(e, g) >>> f`
              override def apply[R, S](g: Uncurry[R, S, Z])(implicit ev1: Y === (R ** S)) = {
                val g0: Uncurry[P, Q, Z] = g.cast(ev.andThen(ev1).flip)
                g0.f.visit(new g0.f.OptVisitor[X :=>: Z] {
                  override def apply(gf: Id[P])(implicit ev2: P === H[Q, Z]) = {
                    val p1 = p.f.asSequence.unsnoc1
                    val (p1init, p1last) = (p1._1, p1._2)
                    val e = sequence(p1init)
                    p1last.visit(new p1last.OptVisitor[X :=>: Z] {
                      override def apply[V, W](cf: Curry[p1.A, V, W])(implicit ev3: H[V, W] === P) =
                        Some(andThen(Prod(e, p.g), cf.cast(ev2 compose ev3).f))
                    })
                  }
                })
              }
            })
        })).orElse({
          // rewrite `assocL >>> assocR` and `assocR >>> assocL` to `id`
          val assocL = Prod(Prod(Fst[Any, Any**Any](), andThen(Snd[Any, Any**Any](), Fst[Any, Any]())), andThen(Snd[Any, Any**Any](), Snd[Any, Any]()))
          val assocR = Prod(andThen(Fst[Any**Any, Any](), Fst[Any, Any]()), Prod(andThen(Fst[Any**Any, Any](), Snd[Any, Any]()), Snd[Any**Any, Any]()))

          val (f1, g1) = (f.rmTags, g.rmTags)
          if((f1.rmTags == assocL && g1.rmTags == assocR) || (f1.rmTags == assocR && g1.rmTags == assocL))
            Some(Id().asInstanceOf[X :=>: Z]) // XXX should avoid asInstanceOf, but it's a pain
          else
            None
        })

        override def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
          // reduce `prod(fst, snd)` to identity
          f.f.visit(new f.f.OptVisitor[A :=>: B] {
            override def apply[P](fst: Fst[X, P])(implicit ev1: A === (X ** P)) =
              f.g.visit(new f.g.OptVisitor[A :=>: B] {
                override def apply[Q](snd: Snd[Q, Y])(implicit ev2: A === (Q ** Y)) = {
                  import snd.ProductLeibnizOps
                  Some(id[:->:, **, T, H, A].castB(ev compose (ev1.flip andThen ev2).snd.lift[X ** ?].subst[A === ?](ev1)))
                }
              })
          }).orElse({
            val fs = f.f.asSequence
            val gs = f.g.asSequence
            val (fh, ft) = (fs.head, fs.tail)
            val (gh, gt) = (gs.head, gs.tail)

            // reduce `prod(fh >>> ft, fh >>> gt)` to `fh >>> prod(ft, gt)`
            (fh termEqual gh) flatMap { (ev1: fs.A1 === gs.A1) => fh match {
              case Id() => None // prevent expanding `prod(id, id)` to `id >>> prod(id, id)`
              case _    => Some(andThen(fh, Prod(sequence(ft), sequence(gt).castA(ev1))).castB[B])
            }} orElse
            None
//            //
//            gh.visit(new gh.OptVisitor[A :=>: B] {
//              override def apply[P, Q](gh: Prod[A, P, Q])(implicit ev1: (P ** Q) === gs.A1) = {
//                val (g1, g2) = (gh.f, gh.g)
//                val g1s = g1.asSequence
//                val g2s = g2.asSequence
//                val (g1h, g1t) = (g1s.head, g1s.tail)
//                val (g2h, g2t) = (g2s.head, g2s.tail)
//
//                // Rewrite `prod(fh >>> ft, prod(fh >>> g1t, g2) >>> gt)`
//                // to      `prod(fh >>> prod(ft, g1t), g2) >>> prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`,
//                // factoring out `fh`.
//                (g1h termEqual fh) flatMap { (ev2: g1s.A1 === fs.A1) =>
//                  if(fh == Fst() && sequence(ft) == Fst() && sequence(g1t) == Snd() && g2 == Snd())
//                    // prevent expanding                        `prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`
//                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`
//                    None
//                  else
//                    Some(andThen(Prod(andThen(fh, Prod(sequence(ft), sequence(g1t).castA(ev2))), g2), Prod(Fst[X ** P, Q]() >>> Fst[X, P](), Prod(Fst[X ** P, Q]() >>> Snd[X, P](), Snd[X ** P, Q]()).castB(ev1) >>> sequence(gt)).castB(ev)))
//                } orElse {
//                // Rewrite `prod(fh >>> ft, prod(g1, fh >>> g2t) >>> gt)`
//                // to      `prod(fh >>> prod(ft, g2t), g1) >>> prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`,
//                // factoring out `fh`.
//                (g2h termEqual fh) flatMap { (ev2: g2s.A1 === fs.A1) =>
//                  if(fh == Fst() && sequence(ft) == Fst() && g1 == Snd() && sequence(g2t) == Snd())
//                    // prevent expanding                        `prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`
//                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`
//                    None
//                  else
//                    Some(andThen(Prod(andThen(fh, Prod(sequence(ft), sequence(g2t).castA(ev2))), g1), Prod(Fst[X ** Q, P]() >>> Fst[X, Q](), Prod(Snd[X ** Q, P](), Fst[X ** Q, P]() >>> Snd[X, Q]()).castB(ev1) >>> sequence(gt)).castB(ev)))
//                }
//                }
//              }
//            }) orElse
//            //
//            fh.visit(new fh.OptVisitor[A :=>: B] {
//              override def apply[P, Q](fh: Prod[A, P, Q])(implicit ev1: (P ** Q) === fs.A1) = {
//                val (f1, f2) = (fh.f, fh.g)
//                val f1s = f1.asSequence
//                val f2s = f2.asSequence
//                val (f1h, f1t) = (f1s.head, f1s.tail)
//                val (f2h, f2t) = (f2s.head, f2s.tail)
//
//                // Rewrite `prod(prod(gh >>> f1t, f2) >>> ft, gh >>> gt)`
//                // to      `prod(gh >>> prod(f1t, gt), f2) >>> prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`,
//                // factoring out `gh`.
//                (f1h termEqual gh) flatMap { (ev2: f1s.A1 === gs.A1) =>
//                  if(gh == Fst() || sequence(f1t) == Fst() || f2 == Snd() || sequence(gt) == Snd())
//                    // prevent expanding                        `prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`
//                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`
//                    None
//                  else
//                    Some(andThen(Prod(andThen(gh, Prod(sequence(f1t).castA(ev2), sequence(gt))), f2), Prod(Prod(Fst[P ** Y, Q]() >>> Fst[P, Y](), Snd[P ** Y, Q]()).castB(ev1) >>> sequence(ft), Fst[P ** Y, Q]() >>> Snd[P, Y]()).castB(ev)))
//                } orElse {
//
//                // Rewrite `prod(prod(f1, gh >>> f2t) >>> ft, gh >>> gt)`
//                // to      `prod(f1, gh >>> prod(f2t, gt)) >>> prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`,
//                // factoring out `gh`.
//                (f2h termEqual gh) flatMap { (ev2: f2s.A1 === gs.A1) =>
//                  if(f1 == Fst() && gh == Snd() && sequence(f2t) == Fst() && sequence(gt) == Snd())
//                    // prevent expanding                        `prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`
//                    // to `prod(fst, snd >>> prod(fst, snd)) >>> prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`
//                    None
//                  else
//                    Some(andThen(Prod(f1, andThen(gh, Prod(sequence(f2t).castA(ev2), sequence(gt)))), Prod(Prod(Fst[P, Q ** Y](), Snd[P, Q ** Y]() >>> Fst[Q, Y]()).castB(ev1) >>> sequence(ft), Snd[P, Q ** Y]() >>> Snd[Q, Y]()).castB(ev)))
//                }
//                }
//              }
//            })
          })

        override def apply[Y, Z](f: Curry[A, Y, Z])(implicit ev: H[Y, Z] === B) =
          f.f.visit(new f.f.OptVisitor[A :=>: B] {
            // reduce curry(uncurry(f)) to f
            override def apply[P, Q](g: Uncurry[P, Q, Z])(implicit ev1: (A ** Y) === (P ** Q)) =
              Some(g.cast(ev1.flip).f.castB[B])
          })

        override def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = {
          // reduce uncurry(g >>> curry(h)) to parallel(g, id) >>> h
          val gh = f.f.asSequence.unsnoc1
          val (g, h) = (sequence(gh._1), gh._2)
          h.visit(new h.OptVisitor[A :=>: B] {
            override def apply[Y1, Z](h: Curry[gh.A, Y1, Z])(implicit ev1: H[Y1, Z] === H[Y, B]) =
              Some((parallel(g, Id[Y]) andThen h.cast(ev1).f).castA[A])
          })
        }
          /* orElse (f.f match {
            case Id() => None

            // rewrite `uncurry(h)` to `prod(fst >>> h, snd) >>> eval`
            case f0   => Some(andThen(Prod(andThen(Fst[X, Y](), f0), Snd[X, Y]()), Uncurry(Id[H[Y, B]]())).castA[A])
          }) */
      })),
    )
  }
}
