package lambdacart

import lambdacart.util.~~>
import lambdacart.util.LeibnizOps
import scalaz.Leibniz.===

sealed abstract class FreeCCC[:=>:[_, _], **[_, _], T, H[_, _], A, B] {
  import FreeCCC._

  type Visitor[R] = FreeCCC.Visitor[:=>:, **, T, H, A, B, R]

  /** Workaround for Scala's broken GADT pattern matching. */
  def visit[R](v: Visitor[R]): R

  def castA[X](implicit ev: A === X): FreeCCC[:=>:, **, T, H, X, B] =
    ev.subst[FreeCCC[:=>:, **, T, H, ?, B]](this)

  def castB[Y](implicit ev: B === Y): FreeCCC[:=>:, **, T, H, A, Y] =
    ev.subst[FreeCCC[:=>:, **, T, H, A, ?]](this)

  def const[Z]: FreeCCC[:=>:, **, T, H, Z, H[A, B]] =
    (this compose snd[:=>:, **, T, H, Z, A]).curry

  def prod[C](that: FreeCCC[:=>:, **, T, H, A, C]): FreeCCC[:=>:, **, T, H, A, B ** C] =
    FreeCCC.prod(this, that)

  def compose[Z](that: FreeCCC[:=>:, **, T, H, Z, A]): FreeCCC[:=>:, **, T, H, Z, B] =
    FreeCCC.compose(this, that)

  def curry[X, Y](implicit ev: A === (X ** Y)): FreeCCC[:=>:, **, T, H, X, H[Y, B]] =
    FreeCCC.curry(this.castA(ev))

  def uncurry[X, Y](implicit ev: B === H[X, Y]): FreeCCC[:=>:, **, T, H, A**X, Y] =
    FreeCCC.uncurry(this.castB(ev))

  final def foldMap[->[_, _]](φ: :=>: ~~> ->)(implicit ccc: CCC.Aux[->, **, T, H]): A -> B =
    visit[A -> B](new Visitor[A -> B] {
      def apply      (f:     Lift[A, B]   ) = φ[A, B](f.f)
      def apply[X]   (f:  Compose[A, X, B]) = ccc.compose(f.f.foldMap(φ), f.g.foldMap(φ))
      def apply      (f:       Id[A]      )(implicit ev:        A === B) = ev.lift[A -> ?](ccc.id[A])
      def apply[X]   (f:      Fst[B, X]   )(implicit ev: (B ** X) === A) = ev.lift[? -> B](ccc.fst[B, X])
      def apply[X]   (f:      Snd[X, B]   )(implicit ev: (X ** B) === A) = ev.lift[? -> B](ccc.snd[X, B])
      def apply      (f: Terminal[A]      )(implicit ev:        T === B) = ev.lift[A -> ?](ccc.terminal[A])
      def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) = ev.lift[A -> ?](ccc.prod(f.f.foldMap(φ), f.g.foldMap(φ)))
      def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) = ev.lift[A -> ?](ccc.curry(f.f.foldMap(φ)))
      def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = ev.lift[? -> B](ccc.uncurry(f.f.foldMap(φ)))
    })

  final def fold(implicit ccc: CCC.Aux[:=>:, **, T, H]): A :=>: B =
    foldMap(~~>.identity[:=>:])

  final def translate[->[_, _]](φ: :=>: ~~> ->): FreeCCC[->, **, T, H, A, B] =
    foldMap(Λ[X, Y](f => lift(φ[X, Y](f))): :=>: ~~> FreeCCC[->, **, T, H, ?, ?])

  final def size: Int = visit(new Visitor[Int] {
    def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = 1 + a.f.size
    def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = 1 + a.f.size
    def apply[Y]   (a:  Compose[A, Y, B])                              = 1 + a.f.size + a.g.size
    def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = 1 + a.f.size + a.g.size
    def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = 1
    def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = 1
    def apply      (a:       Id[A])      (implicit ev:        A === B) = 1
    def apply      (a: Terminal[A])      (implicit ev:        T === B) = 1
    def apply      (a:     Lift[A, B])                                 = 1
  })
}

object FreeCCC {
  case class Lift[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B) extends FreeCCC[:=>:, **, T, H, A, B] {
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
    type Lift[X, Y]       = FreeCCC.Lift    [:=>:, **, T, H, X, Y]
    type Compose[X, Y, Z] = FreeCCC.Compose [:=>:, **, T, H, X, Y, Z]
    type Id[X]            = FreeCCC.Id      [:=>:, **, T, H, X]
    type Prod[X, Y, Z]    = FreeCCC.Prod    [:=>:, **, T, H, X, Y, Z]
    type Terminal[X]      = FreeCCC.Terminal[:=>:, **, T, H, X]
    type Fst[X, Y]        = FreeCCC.Fst     [:=>:, **, T, H, X, Y]
    type Snd[X, Y]        = FreeCCC.Snd     [:=>:, **, T, H, X, Y]
    type Curry[X, Y, Z]   = FreeCCC.Curry   [:=>:, **, T, H, X, Y, Z]
    type Uncurry[X, Y, Z] = FreeCCC.Uncurry [:=>:, **, T, H, X, Y, Z]

    def apply      (f:     Lift[A, B]   )                              : R
    def apply[X]   (f:  Compose[A, X, B])                              : R
    def apply      (f:       Id[A]      )(implicit ev:        A === B) : R
    def apply[X]   (f:      Fst[B, X]   )(implicit ev: (B ** X) === A) : R
    def apply[X]   (f:      Snd[X, B]   )(implicit ev: (X ** B) === A) : R
    def apply[X, Y](f:     Prod[A, X, Y])(implicit ev: (X ** Y) === B) : R
    def apply      (f: Terminal[A]      )(implicit ev:        T === B) : R
    def apply[X, Y](f:    Curry[A, X, Y])(implicit ev:  H[X, Y] === B) : R
    def apply[X, Y](f:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) : R
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

  /* Smart constructors */

  def lift[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B): FreeCCC[:=>:, **, T, H, A, B] = Lift(f)

  // Cartesian closed operations
  def id[:=>:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:=>:, **, T, H, A, A] = Id()
  def compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, B, C], g: FreeCCC[:=>:, **, T, H, A, B]): FreeCCC[:=>:, **, T, H, A, C] = Compose(f, g)
  def fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:=>:, **, T, H, (A**B), A] = Fst()
  def snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:=>:, **, T, H, (A**B), B] = Snd()
  def prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, B], g: FreeCCC[:=>:, **, T, H, A, C]): FreeCCC[:=>:, **, T, H, A, (B**C)] = Prod(f, g)
  def terminal[:=>:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:=>:, **, T, H, A, T] = Terminal()
  def curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, (A**B), C]): FreeCCC[:=>:, **, T, H, A, H[B, C]] = Curry(f)
  def uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, H[B, C]]): FreeCCC[:=>:, **, T, H, (A**B), C] = Uncurry(f)


  // derived Cartesian closed operations

  def diag[:=>:[_, _], **[_, _], T, H[_, _], A]: FreeCCC[:=>:, **, T, H, A, (A ** A)] =
    prod(id, id)

  def parallel[:=>:[_, _], **[_, _], T, H[_, _], A1, A2, B1, B2](
      f: FreeCCC[:=>:, **, T, H, A1, B1],
      g: FreeCCC[:=>:, **, T, H, A2, B2]
  ): FreeCCC[:=>:, **, T, H, (A1**A2), (B1**B2)] =
    prod(compose(f, fst), compose(g, snd))

  def constA[:=>:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:=>:, **, T, H, A, H[B, A]] =
    curry(fst[:=>:, **, T, H, A, B])

  def getConst[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: FreeCCC[:=>:, **, T, H, T, H[A, B]]): FreeCCC[:=>:, **, T, H, A, B] =
    compose(uncurry(f), prod(terminal[:=>:, **, T, H, A], id[:=>:, **, T, H, A]))

  def andThen[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, B], g: FreeCCC[:=>:, **, T, H, B, C]): FreeCCC[:=>:, **, T, H, A, C] =
    compose(g, f)

  def flip[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, (A**B), C]): FreeCCC[:=>:, **, T, H, (B**A), C] =
    compose(f, prod(snd[:=>:, **, T, H, B, A], fst[:=>:, **, T, H, B, A]))

  def swap[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: FreeCCC[:=>:, **, T, H, A, H[B, C]]): FreeCCC[:=>:, **, T, H, B, H[A, C]] =
    curry(flip(uncurry(f)))

  def eval[:=>:[_, _], **[_, _], T, H[_, _], A, B]: FreeCCC[:=>:, **, T, H, H[A, B] ** A, B] =
    uncurry(id[:=>:, **, T, H, H[A, B]])

  def assocR[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: FreeCCC[:=>:, **, T, H, ((A**B)**C), (A**(B**C))] = {
    val pa = compose(fst[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pb = compose(snd[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pc = snd[:=>:, **, T, H, A**B, C]
    prod(pa, prod(pb, pc))
  }

  def assocL[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: FreeCCC[:=>:, **, T, H, (A**(B**C)), ((A**B)**C)] = {
    val pa = fst[:=>:, **, T, H, A, B**C]
    val pb = compose(fst[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    val pc = compose(snd[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    prod(prod(pa, pb), pc)
  }

}
