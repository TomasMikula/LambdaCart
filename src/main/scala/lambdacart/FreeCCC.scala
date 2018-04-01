package lambdacart

import lambdacart.util.~~>
import lambdacart.util.LeibnizOps
import lambdacart.util.typealigned.{ACons, AList, AList1, ANil, APair, LeftAction}
import scala.annotation.tailrec
import scalaz.{~>, Leibniz}
import scalaz.Leibniz.===
import scalaz.std.anyVal._
import scalaz.std.option._
import scalaz.syntax.apply._

sealed abstract class FreeCCC[:->:[_, _], **[_, _], T, H[_, _], A, B] {
  import FreeCCC._

  type :=>:[α, β] = FreeCCC[:->:, **, T, H, α, β]

  type Visitor[R] = FreeCCC.Visitor[:->:, **, T, H, A, B, R]
  type OptVisitor[R] = FreeCCC.OptVisitor[:->:, **, T, H, A, B, R]
  type BinTransformer = FreeCCC.BinTransformer[:->:, **, T, H, A, B]

  type RewriteRule = FreeCCC.RewriteRule[:->:, **, T, H]
  type ClosedRewriteRule = FreeCCC.ClosedRewriteRule[:->:, **, T, H]

  /** Workaround for Scala's broken GADT pattern matching. */
  def visit[R](v: Visitor[R]): R

  def castA[X](implicit ev: A === X): FreeCCC[:->:, **, T, H, X, B] =
    ev.subst[FreeCCC[:->:, **, T, H, ?, B]](this)

  def castB[Y](implicit ev: B === Y): FreeCCC[:->:, **, T, H, A, Y] =
    ev.subst[FreeCCC[:->:, **, T, H, A, ?]](this)

  def const[Z]: FreeCCC[:->:, **, T, H, Z, H[A, B]] =
    (this compose snd[:->:, **, T, H, Z, A]).curry

  def prod[C](that: FreeCCC[:->:, **, T, H, A, C]): FreeCCC[:->:, **, T, H, A, B ** C] =
    FreeCCC.prod(this, that)

  def compose[Z](that: FreeCCC[:->:, **, T, H, Z, A]): FreeCCC[:->:, **, T, H, Z, B] =
    FreeCCC.compose(this, that)

  def andThen[C](that: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    that compose this

  def >>>[C](that: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    this andThen that

  def curry[X, Y](implicit ev: A === (X ** Y)): FreeCCC[:->:, **, T, H, X, H[Y, B]] =
    FreeCCC.curry(this.castA(ev))

  def uncurry[X, Y](implicit ev: B === H[X, Y]): FreeCCC[:->:, **, T, H, A**X, Y] =
    FreeCCC.uncurry(this.castB(ev))

  def asSequence: Sequence[:->:, **, T, H, A, B] =
    visit(new OptVisitor[Sequence[:->:, **, T, H, A, B]] {
      override def apply(f: Sequence[A, B]) = Some(f)
    }).getOrElse(Sequence(AList1(this)))

  // FIXME unsafe, should instead return Option[A :=>: (B with C)]
  def termEqual[C](that: A :=>: C): Option[B === C] =
    if(this == that) Some(Leibniz.force[Nothing, Any, B, C])
    else             None

  final def foldMap[->[_, _]](φ: :->: ~~> ->)(implicit ccc: CCC.Aux[->, **, T, H]): A -> B =
    visit[A -> B](new Visitor[A -> B] {
      def apply      (f:     Lift[A, B]   ) = φ[A, B](f.f)
      def apply      (f: Sequence[A, B]   ) = f.fs.foldMap(ν[:=>: ~~> ->][α, β](_.foldMap(φ)))
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = ev.lift[A -> ?](ccc.id[A])
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: (B ** X) === A) = ev.lift[? -> B](ccc.fst[B, X])
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: (X ** B) === A) = ev.lift[? -> B](ccc.snd[X, B])
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = ev.lift[A -> ?](ccc.terminal[A])
      def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = ev.lift[A -> ?](ccc.prod(f.f.foldMap(φ), f.g.foldMap(φ)))
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = ev.lift[A -> ?](ccc.curry(f.f.foldMap(φ)))
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = ev.lift[? -> B](ccc.uncurry(f.f.foldMap(φ)))
    })

  final def fold(implicit ccc: CCC.Aux[:->:, **, T, H]): A :->: B =
    foldMap(~~>.identity[:->:])

  final def translate[->[_, _]](φ: :->: ~~> ->): FreeCCC[->, **, T, H, A, B] =
    foldMap(Λ[X, Y](f => lift(φ[X, Y](f))): :->: ~~> FreeCCC[->, **, T, H, ?, ?])

  final def size: Int = visit(new Visitor[Int] {
    def apply      (a: Sequence[A, B]   ) = 1 + a.fs.sum(Λ[α, β](_.size): :=>: ~~> λ[(χ, υ) => Int])
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = 1 + a.f.size
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = 1 + a.f.size
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = 1 + a.f.size + a.g.size
    def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = 1
    def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = 1
    def apply      (a:       Id[A])      (implicit ev:        A === B) = 1
    def apply      (a: Terminal[A])      (implicit ev:        T === B) = 1
    def apply      (a:     Lift[A, B])                                 = 1
  })

  /** Returns `true` iff this `FreeCCC` instance doesn't contain any instances of `:->:`. */
  final def isPure: Boolean = visit(new Visitor[Boolean] {
    def apply      (a: Sequence[A, B]   ) = a.fs.all(Λ[α, β](_.isPure): :=>: ~~> λ[(χ, υ) => Boolean])
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = a.f.isPure
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = a.f.isPure
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = a.f.isPure && a.g.isPure
    def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = true
    def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = true
    def apply      (a:       Id[A])      (implicit ev:        A === B) = true
    def apply      (a: Terminal[A])      (implicit ev:        T === B) = true
    def apply      (a:     Lift[A, B])                                 = false
  })

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

  private[FreeCCC] def optim: FreeCCC[:->:, **, T, H, A, B] =
    optimize(genericRules)

  private[FreeCCC] def rmTags: FreeCCC[:->:, **, T, H, A, B] =
    rebuild(~~>.identity[:=>:])

  private[FreeCCC] def rebuild(φ: :=>: ~~> :=>:): A :=>: B =
    φ.apply(transformChildren(ν[:=>: ~~> :=>:][α, β](_.rebuild(φ))))

  private[FreeCCC] def transformChildren(φ: :=>: ~~> :=>:): A :=>: B =
    visit(new Visitor[A :=>: B] {
      def apply   (f:     Lift[A, B])                              = f
      def apply   (f:       Id[A]   )(implicit ev:        A === B) = f.castB[B]
      def apply[X](f:      Fst[B, X])(implicit ev: (B ** X) === A) = f.castA[A]
      def apply[X](f:      Snd[X, B])(implicit ev: (X ** B) === A) = f.castA[A]
      def apply   (f: Terminal[A]   )(implicit ev:        T === B) = f.castB[B]

      def apply(f: Sequence[A, B]) =
        Sequence(f.fs.map(φ))

      def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        Prod(φ.apply(f.f), φ.apply(f.g)).castB[B]

      def apply[X, Y](f: Curry[A, X, Y])(implicit ev:  H[X, Y] === B) =
        Curry(φ.apply(f.f)).castB[B]

      def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) =
        Uncurry(φ.apply(f.f)).castA[A]
    })

  private[FreeCCC] def split: Option[APair[A :=>: ?, ? :=>: B]] = visit(new OptVisitor[APair[A :=>: ?, ? :=>: B]] {
    override def apply(f: Sequence[A, B]) = f.fs.unsnoc match {
      case Left(f)  => f.split
      case Right(p) =>
        val (fs, f) = (p._1, p._2)
        if(f.isCandidateForInlining) Some(APair.of[A :=>: ?, ? :=>: B](Sequence(fs), f))
        else f.split match {
          case None    => None
          case Some(p) =>
            val (f, g) = (p._1, p._2)
            Some(APair.of[A :=>: ?, ? :=>: B](Sequence(fs :+ f), g))
        }
    }
    override def apply[X, Y](p: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
      if      (p.f.isCandidateForInlining)
        Some(APair.of[A :=>: ?, ? :=>: B](Prod(Id(), p.g), Prod[A ** Y, X, Y](sequence(Fst(), p.f), Snd()).castB[B]))
      else if (p.g.isCandidateForInlining)
        Some(APair.of[A :=>: ?, ? :=>: B](Prod(p.f, Id()), Prod[X ** A, X, Y](Fst(), sequence(Snd(), p.g)).castB[B]))
      else (p.f.split, p.g.split) match {
        case (Some(f), _) =>
          Some(APair.of[A :=>: ?, ? :=>: B](Prod(f._1, p.g), Prod[f.A ** Y, X, Y](sequence(Fst(), f._2), Snd()).castB[B]))
        case (_, Some(g)) =>
          Some(APair.of[A :=>: ?, ? :=>: B](Prod(p.f, g._1), Prod[X ** g.A, X, Y](Fst(), sequence(Snd(), g._2)).castB[B]))
        case (None, None) =>
          None
      }
  })

  private[FreeCCC] def isCandidateForInlining: Boolean = {
    visit(new OptVisitor[Boolean] {
      override def apply[X, Y](p: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        if (p.f.isPure && p.g.isPure) Some(true)
        else Some(false)
    }).getOrElse(false)
  }

  private[FreeCCC] def inline[Z](g: Z :=>: A)(reduce: ClosedRewriteRule): Option[Z :=>: B] =
    visit(new OptVisitor[Z :=>: B] {

      override def apply(f: Sequence[A, B]) =
        f.fs.head.inline(g)(reduce) map { f1 => Sequence(f1 +: f.fs.tail) }

      override def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
        (f.f.inline(g)(reduce), f.g.inline(g)(reduce)) match {
          case (Some(f1), Some(f2)) => Some(Prod(f1, f2).castB[B])
          case (Some(f1), None    ) => Some(Prod(f1, sequence(g, f.g)).castB[B])
          case (None    , Some(f2)) => Some(Prod(sequence(g, f.f), f2).castB[B])
          case _                    => None
        }

      override def apply[X, Y](f: Curry[A, X, Y])(implicit ev: H[X, Y] === B) =
        for {
          f <- reduce.rewrite[Z ** X, Y](sequence(Prod(sequence(Fst(), g), Snd()), f.f))
        } yield Curry(f).castB[B]
    })

  private[FreeCCC] def ignoresFst[A1, A2](implicit ev: A === (A1 ** A2)): Option[A2 :=>: B] =
    visit(new OptVisitor[A2 :=>: B] {

      override def apply[X](f: Snd[X, B])(implicit ev1: (X ** B) === A) =
        Some(Id[B].castA(f.deriveLeibniz(ev1 andThen ev)))

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        Some(Terminal[A2].castB)

      override def apply[X, Y](p: Prod[A, X, Y])(implicit ev1: (X ** Y) === B) =
        (p.f.ignoresFst[A1, A2] |@| p.g.ignoresFst[A1, A2])(Prod(_, _).castB)

      override def apply(f: Sequence[A, B]) =
        f.fs.head.ignoresFst[A1, A2] map { h => Sequence(h +: f.fs.tail) }
    })

  private[FreeCCC] def ignoresSnd[A1, A2](implicit ev: A === (A1 ** A2)): Option[A1 :=>: B] =
    visit(new OptVisitor[A1 :=>: B] {

      override def apply[Y](f: Fst[B, Y])(implicit ev1: (B ** Y) === A) =
        Some(Id[B].castA(f.deriveLeibniz(ev1 andThen ev)))

      override def apply(f: Terminal[A])(implicit ev: T === B) =
        Some(Terminal[A1].castB)

      override def apply[X, Y](p: Prod[A, X, Y])(implicit ev1: (X ** Y) === B) =
        (p.f.ignoresSnd[A1, A2] |@| p.g.ignoresSnd[A1, A2])(Prod(_, _).castB)

      override def apply(f: Sequence[A, B]) =
        f.fs.head.ignoresSnd[A1, A2] map { h => Sequence(h +: f.fs.tail) }
    })
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

    def Lift[X, Y](f: X :->: Y)                 : Lift[X, Y]       = FreeCCC.Lift(f)
    def Id[X]()                                 : Id[X]            = FreeCCC.Id()
    def Prod[X, Y, Z](f: X :=>: Y, g: X :=>: Z) : Prod[X, Y, Z]    = FreeCCC.Prod(f, g)
    def Terminal[X]()                           : Terminal[X]      = FreeCCC.Terminal()
    def Fst[X, Y]()                             : Fst[X, Y]        = FreeCCC.Fst()
    def Snd[X, Y]()                             : Snd[X, Y]        = FreeCCC.Snd()
    def Curry[X, Y, Z](f: (X ** Y) :=>: Z)      : Curry[X, Y, Z]   = FreeCCC.Curry(f)
    def Uncurry[X, Y, Z](f: X :=>: H[Y, Z])     : Uncurry[X, Y, Z] = FreeCCC.Uncurry(f)

    def apply      (f:     Lift[A, B]   )                              : R
    def apply      (f: Sequence[A, B]   )                              : R
    def apply      (f:       Id[A]      )(implicit ev:        A === B) : R
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: (B ** X) === A) : R
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: (X ** B) === A) : R
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) : R
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) : R
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) : R
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit e1: (X ** Y) === A) : R
  }

  trait OptVisitor[:->:[_, _], **[_, _], T, H[_, _], A, B, R]
  extends Visitor[:->:, **, T, H, A, B, Option[R]] {
    def apply      (f:     Lift[A, B]   )                              = Option.empty[R]
    def apply      (f: Sequence[A, B]   )                              = Option.empty[R]
    def apply      (f:       Id[A]      )(implicit ev:        A === B) = Option.empty[R]
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: (B ** X) === A) = Option.empty[R]
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: (X ** B) === A) = Option.empty[R]
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = Option.empty[R]
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) = Option.empty[R]
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = Option.empty[R]
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = Option.empty[R]
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
     with (FreeCCC[:->:, **, T, H, ?, ?] ~~> λ[(α, β) => FreeCCC[:->:, **, T, H, α, β]]) {

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
  def compose[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, B, C], g: FreeCCC[:->:, **, T, H, A, B]): FreeCCC[:->:, **, T, H, A, C] = Sequence(g :: AList1(f)).optim
  def fst[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, (A**B), A] = Fst()
  def snd[:->:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:->:, **, T, H, (A**B), B] = Snd()
  def prod[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, B], g: FreeCCC[:->:, **, T, H, A, C]): FreeCCC[:->:, **, T, H, A, (B**C)] = Prod(f, g).optim
  def terminal[:->:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:->:, **, T, H, A, T] = Terminal()
  def curry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, (A**B), C]): FreeCCC[:->:, **, T, H, A, H[B, C]] = Curry(f).optim
  def uncurry[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, H[B, C]]): FreeCCC[:->:, **, T, H, (A**B), C] = Uncurry(f).optim


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

  /** Like [[#andThen]], but not eagerly optimizing. */
  private[FreeCCC] def sequence[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, B], g: FreeCCC[:->:, **, T, H, B, C]): FreeCCC[:->:, **, T, H, A, C] =
    Sequence(f :: AList1(g))

  private[FreeCCC] def sequence[:->:[_, _], **[_, _], T, H[_, _], A, B](fs: AList[FreeCCC[:->:, **, T, H, ?, ?], A, B]): FreeCCC[:->:, **, T, H, A, B] =
    fs match {
      case ev @ ANil()   => id[:->:, **, T, H, A].castB(ev.leibniz)
      case ACons(f1, fs1) => fs1 match {
        case ev @ ANil() => f1.castB(ev.leibniz)
        case ACons(f2, fs2) => Sequence(f1 +: (f2 :: fs2))
      }
    }

  def flip[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, (A**B), C]): FreeCCC[:->:, **, T, H, (B**A), C] =
    compose(f, prod(snd[:->:, **, T, H, B, A], fst[:->:, **, T, H, B, A]))

  def swap[:->:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:->:, **, T, H, A, H[B, C]]): FreeCCC[:->:, **, T, H, B, H[A, C]] =
    curry(flip(uncurry(f)))

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
      ν[ClosedRewriteRule].rewrite[A, B](f => f.visit(new BinTransformer[:->:, **, T, H, A, B] {
        override def apply   (f:     Lift[A, B])                              = None
        override def apply   (f:       Id[A]   )(implicit ev:        A === B) = None
        override def apply[X](f:      Fst[B, X])(implicit ev: (B ** X) === A) = None
        override def apply[X](f:      Snd[X, B])(implicit ev: (X ** B) === A) = None
        override def apply   (f: Terminal[A]   )(implicit ev:        T === B) = None

        override def apply[X, Y, Z](f: X :=>: Y, g: Y :=>: Z) = g.visit(new g.OptVisitor[X :=>: Z] {

          // flatten compositions
          override def apply(g: Sequence[Y, Z]) = Some(Sequence(f :: g.fs))

          // reduce `id . f` to `f`
          override def apply(g: Id[Y])(implicit ev: Y === Z) = Some(f.castB(ev))

          // reduce `terminal . f` to `terminal`
          override def apply(g: Terminal[Y])(implicit ev: T === Z) = Some((Terminal(): Terminal[X]).castB[Z])

          // Rewrite `f >>> curry(g)` to `curry(parallel(f, id) >>> g)`
          // Increases size, but pushes `curry` on the outside.
          override def apply[V, W](g: Curry[Y, V, W])(implicit ev: H[V, W] === Z) =
            Some(curry(sequence(parallel(f, id[:->:, **, T, H, V]), g.f)).castB[Z])

          override def apply[P, Q](g: Prod[Y, P, Q])(implicit ev: (P ** Q) === Z) = {
            val g1s = g.f.asSequence.fs
            val g2s = g.g.asSequence.fs
            val (g1h, g1t) = (g1s.head, g1s.tail)
            val (g2h, g2t) = (g2s.head, g2s.tail)

            // rewrite `f >>> prod(curry(snd >>> h) >>> i, g2)`
            // to      `prod(curry(snd >>> h) >>> i, f >>> g2)`
            g1h.visit(new g1h.OptVisitor[X :=>: Z] {
              override def apply[R, S](g1h: Curry[Y, R, S])(implicit ev1: H[R, S] === g1s.A1) = {
                val g1hs = g1h.f.asSequence.fs
                val (g1hh, g1ht) = (g1hs.head, g1hs.tail)

                g1hh.visit(new g1hh.OptVisitor[X :=>: Z] {
                  override def apply[U](g1hh: Snd[U, g1hs.A1])(implicit ev2: (U ** g1hs.A1) === (Y ** R)) = {
                    val ev3: g1hs.A1 === R = g1hh.deriveLeibniz(ev2)
                    Some(Prod(sequence(Curry(sequence(Snd[X, R](), sequence(g1ht).castA(ev3))), sequence(g1t).castA(ev1.flip)), f >>> g.g).castB[Z])
                  }
                })
              }
            }) orElse {
            // rewrite `f >>> prod(g1, curry(snd >>> h) >>> i)`
            // to      `prod(f >>> g1, curry(snd >>> h) >>> i)`
            g2h.visit(new g2h.OptVisitor[X :=>: Z] {
              override def apply[R, S](g2h: Curry[Y, R, S])(implicit ev1: H[R, S] === g2s.A1) = {
                val g2hs = g2h.f.asSequence.fs
                val (g2hh, g2ht) = (g2hs.head, g2hs.tail)

                g2hh.visit(new g2hh.OptVisitor[X :=>: Z] {
                  override def apply[U](g2hh: Snd[U, g2hs.A1])(implicit ev2: (U ** g2hs.A1) === (Y ** R)) = {
                    val ev3: g2hs.A1 === R = g2hh.deriveLeibniz(ev2)
                    Some(Prod(f >>> g.f, sequence(Curry(sequence(Snd[X, R](), sequence(g2ht).castA(ev3))), sequence(g2t).castA(ev1.flip))).castB[Z])
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
          override def apply(f: Id[X])(implicit ev: X === Y) = Some(g.castA(ev.flip))

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

              // rewrite `prod(curry(f), g) >>> uncurry(id)` to `prod(id, g) >>> f`
              override def apply[R, S](g: Uncurry[R, S, Z])(implicit ev1: (R ** S) === Y) = {
                val g0: Uncurry[P, Q, Z] = g.cast(ev.flip compose ev1)
                g0.f.visit(new g0.f.OptVisitor[X :=>: Z] {
                  override def apply(gf: Id[P])(implicit ev2: P === H[Q, Z]) = {
                    p.f.visit(new p.f.OptVisitor[X :=>: Z] {
                      override def apply[V, W](p1: Curry[X, V, W])(implicit ev3: H[V, W] === P) =
                        Some(sequence(Prod(Id[X](), p.g), p1.cast(ev2 compose ev3).f))
                    })
                  }
                })
              }
            })
        })).orElse({
          // rewrite `assocL >>> assocR` and `assocR >>> assocL` to `id`
          val assocL = Prod(Prod(Fst[Any, Any**Any](), sequence(Snd[Any, Any**Any](), Fst[Any, Any]())), sequence(Snd[Any, Any**Any](), Snd[Any, Any]()))
          val assocR = Prod(sequence(Fst[Any**Any, Any](), Fst[Any, Any]()), Prod(sequence(Fst[Any**Any, Any](), Snd[Any, Any]()), Snd[Any**Any, Any]()))

          val (f1, g1) = (f.rmTags, g.rmTags)
          if((f1.rmTags == assocL && g1.rmTags == assocR) || (f1.rmTags == assocR && g1.rmTags == assocL))
            Some(Id().asInstanceOf[X :=>: Z]) // XXX should avoid asInstanceOf, but it's a pain
          else
            None
        })

        override def apply[X, Y](f: Prod[A, X, Y])(implicit ev: (X ** Y) === B) =
          // reduce `prod(fst, snd)` to identity
          f.f.visit(new f.f.OptVisitor[A :=>: B] {
            override def apply[P](fst: Fst[X, P])(implicit ev1: (X ** P) === A) =
              f.g.visit(new f.g.OptVisitor[A :=>: B] {
                override def apply[Q](snd: Snd[Q, Y])(implicit ev2: (Q ** Y) === A) =
                  Some(id[:->:, **, T, H, A].castB(ev compose snd.deriveLeibniz(ev1.flip.compose(ev2)).flip.lift[X ** ?].subst[? === A](ev1).flip))
              })
          }).orElse({
            val fs = f.f.asSequence.fs
            val gs = f.g.asSequence.fs
            val (fh, ft) = (fs.head, fs.tail)
            val (gh, gt) = (gs.head, gs.tail)

            // reduce `prod(fh >>> ft, fh >>> gt)` to `fh >>> prod(ft, gt)`
            (fh termEqual gh) flatMap { (ev1: fs.A1 === gs.A1) => fh match {
              case Id() => None // prevent expanding `prod(id, id)` to `id >>> prod(id, id)`
              case _    => Some(sequence(fh, Prod(sequence(ft), sequence(gt).castA(ev1.flip))).castB[B])
            }} orElse
            //
            gh.visit(new gh.OptVisitor[A :=>: B] {
              override def apply[P, Q](gh: Prod[A, P, Q])(implicit ev1: (P ** Q) === gs.A1) = {
                val (g1, g2) = (gh.f, gh.g)
                val g1s = g1.asSequence.fs
                val g2s = g2.asSequence.fs
                val (g1h, g1t) = (g1s.head, g1s.tail)
                val (g2h, g2t) = (g2s.head, g2s.tail)

                // Rewrite `prod(fh >>> ft, prod(fh >>> g1t, g2) >>> gt)`
                // to      `prod(fh >>> prod(ft, g1t), g2) >>> prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`,
                // factoring out `fh`.
                (g1h termEqual fh) flatMap { (ev2: g1s.A1 === fs.A1) =>
                  if(fh == Fst() && sequence(ft) == Fst() && sequence(g1t) == Snd() && g2 == Snd())
                    // prevent expanding                        `prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`
                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(fst >>> fst, prod(fst >>> snd, snd) >>> gt)`
                    None
                  else
                    Some(sequence(Prod(sequence(fh, Prod(sequence(ft), sequence(g1t).castA(ev2))), g2), Prod(Fst[X ** P, Q]() >>> Fst[X, P](), Prod(Fst[X ** P, Q]() >>> Snd[X, P](), Snd[X ** P, Q]()).castB(ev1) >>> sequence(gt)).castB(ev)))
                } orElse {
                // Rewrite `prod(fh >>> ft, prod(g1, fh >>> g2t) >>> gt)`
                // to      `prod(fh >>> prod(ft, g2t), g1) >>> prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`,
                // factoring out `fh`.
                (g2h termEqual fh) flatMap { (ev2: g2s.A1 === fs.A1) =>
                  if(fh == Fst() && sequence(ft) == Fst() && g1 == Snd() && sequence(g2t) == Snd())
                    // prevent expanding                        `prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`
                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(fst >>> fst, prod(snd, fst >>> snd) >>> gt)`
                    None
                  else
                    Some(sequence(Prod(sequence(fh, Prod(sequence(ft), sequence(g2t).castA(ev2))), g1), Prod(Fst[X ** Q, P]() >>> Fst[X, Q](), Prod(Snd[X ** Q, P](), Fst[X ** Q, P]() >>> Snd[X, Q]()).castB(ev1) >>> sequence(gt)).castB(ev)))
                }
                }
              }
            }) orElse
            //
            fh.visit(new fh.OptVisitor[A :=>: B] {
              override def apply[P, Q](fh: Prod[A, P, Q])(implicit ev1: (P ** Q) === fs.A1) = {
                val (f1, f2) = (fh.f, fh.g)
                val f1s = f1.asSequence.fs
                val f2s = f2.asSequence.fs
                val (f1h, f1t) = (f1s.head, f1s.tail)
                val (f2h, f2t) = (f2s.head, f2s.tail)

                // Rewrite `prod(prod(gh >>> f1t, f2) >>> ft, gh >>> gt)`
                // to      `prod(gh >>> prod(f1t, gt), f2) >>> prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`,
                // factoring out `gh`.
                (f1h termEqual gh) flatMap { (ev2: f1s.A1 === gs.A1) =>
                  if(gh == Fst() || sequence(f1t) == Fst() || f2 == Snd() || sequence(gt) == Snd())
                    // prevent expanding                        `prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`
                    // to `prod(fst >>> prod(fst, snd), snd) >>> prod(prod(fst >>> fst, snd) >>> ft, fst >>> snd)`
                    None
                  else
                    Some(sequence(Prod(sequence(gh, Prod(sequence(f1t).castA(ev2), sequence(gt))), f2), Prod(Prod(Fst[P ** Y, Q]() >>> Fst[P, Y](), Snd[P ** Y, Q]()).castB(ev1) >>> sequence(ft), Fst[P ** Y, Q]() >>> Snd[P, Y]()).castB(ev)))
                } orElse {

                // Rewrite `prod(prod(f1, gh >>> f2t) >>> ft, gh >>> gt)`
                // to      `prod(f1, gh >>> prod(f2t, gt)) >>> prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`,
                // factoring out `gh`.
                (f2h termEqual gh) flatMap { (ev2: f2s.A1 === gs.A1) =>
                  if(f1 == Fst() && gh == Snd() && sequence(f2t) == Fst() && sequence(gt) == Snd())
                    // prevent expanding                        `prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`
                    // to `prod(fst, snd >>> prod(fst, snd)) >>> prod(prod(fst, snd >>> fst) >>> ft, snd >>> snd)`
                    None
                  else
                    Some(sequence(Prod(f1, sequence(gh, Prod(sequence(f2t).castA(ev2), sequence(gt)))), Prod(Prod(Fst[P, Q ** Y](), Snd[P, Q ** Y]() >>> Fst[Q, Y]()).castB(ev1) >>> sequence(ft), Snd[P, Q ** Y]() >>> Snd[Q, Y]()).castB(ev)))
                }
                }
              }
            })
          })

        override def apply[Y, Z](f: Curry[A, Y, Z])(implicit ev: H[Y, Z] === B) =
          f.f.visit(new f.f.OptVisitor[A :=>: B] {
            // reduce curry(uncurry(f)) to f
            override def apply[P, Q](g: Uncurry[P, Q, Z])(implicit ev1: (P ** Q) === (A ** Y)) =
              Some(g.cast(ev1).f.castB[B])
          })

        // rewrite `uncurry(h)` to `prod(fst >>> h, snd) >>> eval`
        override def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) =
          f.f match {
            case Id() => None
            case f0   => Some(sequence(Prod(sequence(Fst[X, Y](), f0), Snd[X, Y]()), Uncurry(Id[H[Y, B]]())).castA[A])
          }
      })),

      ν[RewriteRule].rewriteRec[A, B](f => rec => f.visit(new BinTransformer[:->:, **, T, H, A, B] {
        override def apply[X, Y, Z](f: X :=>: Y, g: Y :=>: Z) =
          (
            if (f.isCandidateForInlining) g.inline(f)(rec)
            else None
          ) orElse (
            f.split flatMap { p =>
              val (f1, f2) = (p._1, p._2)
              assert( f2.isCandidateForInlining , s"not a candidate for inlining: $f2" )
              g.inline(f2)(rec) map (g1 => sequence(f1, g1))
            }
          )
      }))
    )
  }
}
