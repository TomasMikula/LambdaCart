package lambdacart

import lambdacart.util.~~>
import lambdacart.util.LeibnizOps
import scalaz.Leibniz.===

sealed abstract class FreeCCC[:=>:[_, _], **[_, _], T, H[_, _], A, B] {
  import FreeCCC._

  type Visitor[R] = FreeCCC.Visitor[:=>:, **, T, H, A, B, R]

  /** Workaround for Scala's broken GADT pattern matching. */
  def visit[R](v: Visitor[R]): R

  final def foldMap[->[_, _]](φ: :=>: ~~> ->)(implicit ccc: CCC.Aux[->, **, T, H]): A -> B =
    visit[A -> B](new Visitor[A -> B] {
      def apply(f: Wrap[:=>:, **, T, H, A, B]) = φ[A, B](f.f)
      def apply(f: Id[:=>:, **, T, H, A])(implicit ev: A === B) = ev.lift[A -> ?](ccc.id[A])
      def apply[X](f: Compose[:=>:, **, T, H, A, X, B]) = ccc.compose(f.f.foldMap(φ), f.g.foldMap(φ))
      def apply[X](f: Fst[:=>:, **, T, H, B, X])(implicit ev: (B ** X) === A) = ev.lift[? -> B](ccc.fst[B, X])
      def apply[X](f: Snd[:=>:, **, T, H, X, B])(implicit ev: (X ** B) === A) = ev.lift[? -> B](ccc.snd[X, B])
      def apply[X, Y](f: Prod[:=>:, **, T, H, A, X, Y])(implicit ev: (X ** Y) === B) = ev.lift[A -> ?](ccc.prod(f.f.foldMap(φ), f.g.foldMap(φ)))
      def apply(f: Terminal[:=>:, **, T, H, A])(implicit ev: T === B) = ev.lift[A -> ?](ccc.terminal[A])
      def apply[X, Y](f: Curry[:=>:, **, T, H, A, X, Y])(implicit ev: H[X, Y] === B) = ev.lift[A -> ?](ccc.curry(f.f.foldMap(φ)))
      def apply[X, Y](f: Uncurry[:=>:, **, T, H, X, Y, B])(implicit ev: (X ** Y) === A) = ev.lift[? -> B](ccc.uncurry(f.f.foldMap(φ)))
    })

  final def fold(implicit ccc: CCC.Aux[:=>:, **, T, H]): A :=>: B =
    foldMap(~~>.identity[:=>:])

  final def translate[->[_, _]](φ: :=>: ~~> ->): FreeCCC[->, **, T, H, A, B] =
    foldMap(Λ[X, Y](f => Wrap(φ[X, Y](f))): :=>: ~~> FreeCCC[->, **, T, H, ?, ?])
}

object FreeCCC {
  case class Wrap[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B) extends FreeCCC[:=>:, **, T, H, A, B] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Id[:=>:[_, _], **[_, _], T, H[_, _], A]() extends FreeCCC[:=>:, **, T, H, A, A] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, B, C], g: FreeCCC[:=>:, **, T, H, A, B]) extends FreeCCC[:=>:, **, T, H, A, C] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends FreeCCC[:=>:, **, T, H, A ** B, A] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends FreeCCC[:=>:, **, T, H, A ** B, B] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, B], g: FreeCCC[:=>:, **, T, H, A, C]) extends FreeCCC[:=>:, **, T, H, A, B ** C] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Terminal[:=>:[_, _], **[_, _], T, H[_, _], A]() extends FreeCCC[:=>:, **, T, H, A, T] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A ** B, C]) extends FreeCCC[:=>:, **, T, H, A, H[B, C]] {
    def visit[R](v: Visitor[R]): R = v(this)
  }

  case class Uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, H[B, C]]) extends FreeCCC[:=>:, **, T, H, A ** B, C] {
    def visit[R](v: Visitor[R]): R = v(this)
  }


  trait Visitor[:=>:[_, _], **[_, _], T, H[_, _], A, B, R] {
    def apply(f: Wrap[:=>:, **, T, H, A, B]): R
    def apply(f: Id[:=>:, **, T, H, A])(implicit ev: A === B): R
    def apply[X](f: Compose[:=>:, **, T, H, A, X, B]): R
    def apply[X](f: Fst[:=>:, **, T, H, B, X])(implicit ev: (B ** X) === A): R
    def apply[X](f: Snd[:=>:, **, T, H, X, B])(implicit ev: (X ** B) === A): R
    def apply[X, Y](f: Prod[:=>:, **, T, H, A, X, Y])(implicit ev: (X ** Y) === B): R
    def apply(f: Terminal[:=>:, **, T, H, A])(implicit ev: T === B): R
    def apply[X, Y](f: Curry[:=>:, **, T, H, A, X, Y])(implicit ev: H[X, Y] === B): R
    def apply[X, Y](f: Uncurry[:=>:, **, T, H, X, Y, B])(implicit ev: (X ** Y) === A): R
  }

  implicit def cccInstance[:=>:[_, _], &[_, _], T, H[_, _]]: CCC.Aux[FreeCCC[:=>:, &, T, H, ?, ?], &, T, H] =
    new CCC[FreeCCC[:=>:, &, T, H, ?, ?]] {
      type **[A, B] = A & B
      type Unit = T
      type Hom[A, B] = H[A, B]

      type ->[A, B] = FreeCCC[:=>:, &, T, H, A, B]

      def id[A]: A -> A = Id()
      def compose[A, B, C](f: B -> C, g: A -> B): A -> C = Compose(f, g)
      def fst[A, B]: (A & B) -> A = Fst()
      def snd[A, B]: (A & B) -> B = Snd()
      def prod[A, B, C](f: A -> B, g: A -> C): A -> (B & C) = Prod(f, g)
      def terminal[A]: A -> T = Terminal()
      def curry[A, B, C](f: (A & B) -> C): A -> H[B, C] = Curry[:=>:, &, T, H, A, B, C](f)
      def uncurry[A, B, C](f: A -> H[B, C]): (A & B) -> C = Uncurry(f)
    }
}
