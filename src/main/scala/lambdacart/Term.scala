package lambdacart

import scalaz.Leibniz
import scalaz.Leibniz.===

/** Hybrid representation containing both lambda terms and operations of
  * a Cartesian closed category. Used as an intermediate representation
  * in the translation from lambda expressions to Cartesian closed operations.
  */
sealed trait Term[:=>:[_, _], **[_, _], T, H[_, _], A] {
  import Term._

  type $[X]             =      DataTerm[:=>:, **, T, H, X]
  type φ[X, Y]          =      CodeTerm[:=>:, **, T, H, X, Y]

  type Id[X]            =       Term.Id[:=>:, **, T, H, X]
  type Var[X]           =      Term.Var[:=>:, **, T, H, X]
  type Obj[X]           =      Term.Obj[:=>:, **, T, H, X]
  type App[X, Y]        =      Term.App[:=>:, **, T, H, X, Y]
  type Arr[X, Y]        =      Term.Arr[:=>:, **, T, H, X, Y]
  type Fst[X, Y]        =      Term.Fst[:=>:, **, T, H, X, Y]
  type Snd[X, Y]        =      Term.Snd[:=>:, **, T, H, X, Y]
  type Prod[X, Y, Z]    =     Term.Prod[:=>:, **, T, H, X, Y, Z]
  type Terminal[X]      = Term.Terminal[:=>:, **, T, H, X]
  type Compose[X, Y, Z] =  Term.Compose[:=>:, **, T, H, X, Y, Z]
  type Curry[X, Y, Z]   =    Term.Curry[:=>:, **, T, H, X, Y, Z]
  type Uncurry[X, Y, Z] =  Term.Uncurry[:=>:, **, T, H, X, Y, Z]
  type ConstVar[X, Y]   = Term.ConstVar[:=>:, **, T, H, X, Y]
}

object Term {

  sealed trait DataTerm[:=>:[_, _], **[_, _], T, H[_, _], A] extends Term[:=>:, **, T, H, A] {
    type Visitor[R] = DataTerm.Visitor[:=>:, **, T, H, A, R]

    def visit[R](v: Visitor[R]): R

    def size: Int = visit(new Visitor[Int] {
      def apply(a: Var[A]): Int = 1
      def apply[X](a: App[X,A]): Int = 1 + a.f.size + a.a.size
      def apply(a: Obj[A]): Int = 1
    })

    def containsVar[V](v: Var[V]): Boolean = visit(new Visitor[Boolean] {
      def apply(a: Var[A]) = a == v
      def apply(a: Obj[A]) = a.f.containsVar(v)
      def apply[X](a: App[X,A]) = a.f.containsVar(v) || a.a.containsVar(v)
    })

    /** Returns `f` such that `f(x) = this` and `x` does not occur in `f`.
      */
    def unapply[V](v: Var[V]): φ[V, A] = visit(new Visitor[φ[V, A]] {
      def apply(a: Obj[A]) =
        if(a.f.containsVar(v)) compose(uncurry(a.f.unapply(v)), prod(id, terminal))
        else compose(a.f, terminal)

      def apply[X](a: App[X,A]) =
        if(!a.f.containsVar(v)) andThen(a.a.unapply(v), Term.code(a.f))
        else andThen(prod(a.f.unapply(v), a.a.unapply(v)), eval[:=>:, **, T, H, X, A])

      def apply(a: Var[A]) =
        sameVar(a, v) match {
          case Some(ev) => id[:=>:, **, T, H, A].castA[V](ev)
          case None     => constVar(a)
        }
    })

    def code: φ[T, A] =
      visit(new Visitor[φ[T, A]] {
        def apply   (a: Obj[A])   = a.f
        def apply   (a: Var[A])   = constVar(a)
        def apply[X](a: App[X, A])= compose(Term.code(a.f), a.a.code)
      })


    /* Syntax */

    // Not a usual map signagure. This is to abuse Scala's `for` syntax.
    def map[B](f: $[A] => $[B]): $[B] =
      f(this)

    // Not a usual flatMap signagure. This is to abuse Scala's `for` syntax.
    def flatMap[B](f: $[A] => $[B]): $[B] =
      f(this)

    def **[B](b: $[B]): $[A ** B] = pair(this, b)
    def **[B, C](f: φ[B, C]): $[A ** H[B, C]] = pair(this, f.data)
  }
  object DataTerm {
    trait Visitor[:=>:[_, _], **[_, _], T, H[_, _], A, R] {
      def apply[X](a: App[:=>:, **, T, H, X, A]): R
      def apply   (a: Obj[:=>:, **, T, H, A])   : R
      def apply   (a: Var[:=>:, **, T, H, A])   : R
    }
  }

  sealed trait CodeTerm[:=>:[_, _], **[_, _], T, H[_, _], A, B] extends Term[:=>:, **, T, H, A :=>: B] {
    type Visitor[R] = CodeTerm.Visitor[:=>:, **, T, H, A, B, R]

    def visit[R](v: Visitor[R]): R

    def const[Z]: φ[Z, H[A, B]] = Term.const(this)

    def data: DataTerm[:=>:, **, T, H, H[A, B]] =
      obj(this.const[T])

    def castA[X](implicit ev: A === X): CodeTerm[:=>:, **, T, H, X, B] =
      ev.subst[CodeTerm[:=>:, **, T, H, ?, B]](this)

    def castB[Y](implicit ev: B === Y): CodeTerm[:=>:, **, T, H, A, Y] =
      ev.subst[CodeTerm[:=>:, **, T, H, A, ?]](this)

    def size: Int = visit(new Visitor[Int] {
      def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = 1 + a.f.size
      def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = 1 + a.f.size
      def apply[Y]   (a:  Compose[A, Y, B])                              = 1 + a.f.size + a.g.size
      def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = 1 + a.f.size + a.g.size
      def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = 1
      def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = 1
      def apply      (a:       Id[A])      (implicit ev:        A === B) = 1
      def apply      (a: Terminal[A])      (implicit ev:        T === B) = 1
      def apply      (a:      Arr[A, B])                                 = 1
      def apply      (a: ConstVar[A, B])                                 = 2
    })

    def containsVar[V](v: Var[V]): Boolean = visit(new Visitor[Boolean] {
      def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = a.f.containsVar(v)
      def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = a.f.containsVar(v)
      def apply[Y]   (a:  Compose[A, Y, B])                              = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = false
      def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = false
      def apply      (a:       Id[A])      (implicit ev:        A === B) = false
      def apply      (a: Terminal[A])      (implicit ev:        T === B) = false
      def apply      (a:      Arr[A, B])                                 = false
      def apply      (a: ConstVar[A, B])                                 = a.a.containsVar(v)
    })

    def unapply[V](v: Var[V]): φ[V, H[A, B]] = visit(new Visitor[φ[V, H[A, B]]] {
      def apply   (a:      Arr[A, B])                            = a         .const[V]
      def apply   (a:       Id[A]   )(implicit ev:      A === B) = a.castB[B].const[V]
      def apply[Y](a:      Fst[B, Y])(implicit ev: (B**Y) === A) = a.castA[A].const[V]
      def apply[X](a:      Snd[X, B])(implicit ev: (X**B) === A) = a.castA[A].const[V]
      def apply   (a: Terminal[A]   )(implicit ev:      T === B) = a.castB[B].const[V]

      def apply[X, Y](a: Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = (
        if(a.containsVar(v)) curry(andThen(assocL[:=>:, **, T, H, V, X, Y], uncurry(uncurry(a.f.unapply(v)))))
        else a.const[V]
      ).castB(ev.lift[H[?, B]])

      def apply[Y, Z](a: Curry[A, Y, Z])(implicit ev: H[Y, Z] === B) = (
        if(a.containsVar(v)) curry(curry(andThen(assocR[:=>:, **, T, H, V, A, Y], uncurry(a.f.unapply(v)))))
        else                 a.const[V]
      ).castB(ev.lift[H[A, ?]])

      def apply[Y, Z](a: Prod[A, Y, Z])(implicit ev: (Y**Z) === B) = (
        if(a.containsVar(v)) curry(prod(uncurry(a.f.unapply(v)), uncurry(a.g.unapply(v))))
        else                 a.const[V]
      ).castB(ev.lift[H[A, ?]])

      def apply[Y](a: Compose[A, Y, B]) =
        if(a.containsVar(v)) {
          val f: φ[V**A, H[V, B]] = compose(swap(a.f.unapply(v)), uncurry(a.g.unapply(v)))
          val g: φ[(V**V)**A, B] = compose(flip(uncurry(f)), assocR[:=>:, **, T, H, V, V, A])
          val diag1: φ[V**A, (V**V)**A] = parallel(diag[:=>:, **, T, H, V], id)
          curry(compose(g, diag1))
        } else {
          a.const[V]
        }

      def apply(a: ConstVar[A, B]) =
        sameVar(a.a, v) match {
          case Some(ev) => constA[:=>:, **, T, H, B, A].castA[V](ev)
          case None     => a.const[V]
        }
    })

    final def compile(implicit C: CCC.Aux[:=>:, **, T, H]): A :=>: B = visit(new Visitor[A :=>:B] {
      def apply[Y, Z](a:    Curry[A, Y, Z])(implicit ev:  H[Y, Z] === B) = ev.lift[A :=>: ?](C.curry(a.f.compile))
      def apply[X, Y](a:  Uncurry[X, Y, B])(implicit ev: (X ** Y) === A) = ev.lift[? :=>: B](C.uncurry(a.f.compile))
      def apply[Y]   (a:  Compose[A, Y, B])                              = C.compose(a.f.compile, a.g.compile)
      def apply[Y, Z](a:     Prod[A, Y, Z])(implicit ev:   (Y**Z) === B) = ev.lift[A :=>: ?](C.prod(a.f.compile, a.g.compile))
      def apply[Y]   (a:      Fst[B, Y])   (implicit ev:   (B**Y) === A) = ev.lift[? :=>: B](C.fst[B, Y])
      def apply[X]   (a:      Snd[X, B])   (implicit ev:   (X**B) === A) = ev.lift[? :=>: B](C.snd[X, B])
      def apply      (a:       Id[A])      (implicit ev:        A === B) = ev.lift[A :=>: ?](C.id[A])
      def apply      (a: Terminal[A])      (implicit ev:        T === B) = ev.lift[A :=>: ?](C.terminal[A])
      def apply      (a:      Arr[A, B])                                 = a.f

      def apply      (a: ConstVar[A, B])                                 = sys.error("Cannot compile variable.")
    })


    /* Syntax */

    def **[C]   (c: $[C]   ): $[H[A, B] ** C]       = pair(this.data, c)
    def **[C, D](f: φ[C, D]): $[H[A, B] ** H[C, D]] = pair(this.data, f.data)
  }

  object CodeTerm {
    trait Visitor[:=>:[_, _], **[_, _], T, H[_, _], A, B, R] {
      def apply[Y, Z](a:    Curry[:=>:, **, T, H, A, Y, Z])(implicit ev:  H[Y, Z] === B) : R
      def apply[X, Y](a:  Uncurry[:=>:, **, T, H, X, Y, B])(implicit ev: (X ** Y) === A) : R
      def apply[Y]   (a:  Compose[:=>:, **, T, H, A, Y, B])                              : R
      def apply[Y, Z](a:     Prod[:=>:, **, T, H, A, Y, Z])(implicit ev:   (Y**Z) === B) : R
      def apply[Y]   (a:      Fst[:=>:, **, T, H, B, Y])   (implicit ev:   (B**Y) === A) : R
      def apply[X]   (a:      Snd[:=>:, **, T, H, X, B])   (implicit ev:   (X**B) === A) : R
      def apply      (a:       Id[:=>:, **, T, H, A])      (implicit ev:        A === B) : R
      def apply      (a: Terminal[:=>:, **, T, H, A])      (implicit ev:        T === B) : R
      def apply      (a:      Arr[:=>:, **, T, H, A, B])                                 : R
      def apply      (a: ConstVar[:=>:, **, T, H, A, B])                                 : R
    }
  }

  implicit class LeibnizOps[X, Y](ev: X === Y) {
    def lift[F[_]]: F[X] === F[Y] = ev.subst[λ[α => F[X] === F[α]]](Leibniz.refl)
  }

  // wrap primitive arrow
  def arr[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B): CodeTerm[:=>:, **, T, H, A, B] = Arr(f)

  // Cartesian operations
  def id[:=>:[_, _], **[_, _], T, H[_, _], A]: CodeTerm[:=>:, **, T, H, A, A] = Id()
  def compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, B, C], g: CodeTerm[:=>:, **, T, H, A, B]): CodeTerm[:=>:, **, T, H, A, C] = Compose(f, g)
  def fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]: CodeTerm[:=>:, **, T, H, (A**B), A] = Fst()
  def snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]: CodeTerm[:=>:, **, T, H, (A**B), B] = Snd()
  def prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, B], g: CodeTerm[:=>:, **, T, H, A, C]): CodeTerm[:=>:, **, T, H, A, (B**C)] = Prod(f, g)
  def terminal[:=>:[_, _], **[_, _], T, H[_, _], A]: CodeTerm[:=>:, **, T, H, A, T] = Terminal()
  def curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, (A**B), C]): CodeTerm[:=>:, **, T, H, A, H[B, C]] = Curry(f)
  def uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, H[B, C]]): CodeTerm[:=>:, **, T, H, (A**B), C] = Uncurry(f)

  // object A represented as an arrow from terminal object to A (eliminated during compilation)
  def obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: CodeTerm[:=>:, **, T, H, T, A]): DataTerm[:=>:, **, T, H, A] = Obj(f)

  def constVar[:=>:[_, _], **[_, _], T, H[_, _], Z, A](a: Term.Var[:=>:, **, T, H, A]): CodeTerm[:=>:, **, T, H, Z, A] = ConstVar(a)

  // Arrow application (will be eliminated during compilation)
  def app[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: CodeTerm[:=>:, **, T, H, A, B], a: DataTerm[:=>:, **, T, H, A]): DataTerm[:=>:, **, T, H, B] =
    app(f.data, a)
  def app[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]], a: DataTerm[:=>:, **, T, H, A]): DataTerm[:=>:, **, T, H, B] =
    a.visit(new DataTerm.Visitor[:=>:, **, T, H, A, DataTerm[:=>:, **, T, H, B]] {
      def apply[X](a: App[:=>:, **, T, H, X, A]) = App(compose(code(f), code(a.f)).data, a.a)
      def apply   (a: Obj[:=>:, **, T, H, A])    = obj(compose(code(f), a.f))
      def apply   (a: Var[:=>:, **, T, H, A])    = App(f, a)
    })


  // derived Cartesian closed operations

  def diag[:=>:[_, _], **[_, _], T, H[_, _], A]: CodeTerm[:=>:, **, T, H, A, (A ** A)] =
    prod(id, id)

  def parallel[:=>:[_, _], **[_, _], T, H[_, _], A1, A2, B1, B2](
      f: CodeTerm[:=>:, **, T, H, A1, B1],
      g: CodeTerm[:=>:, **, T, H, A2, B2]
  ): CodeTerm[:=>:, **, T, H, (A1**A2), (B1**B2)] =
    prod(compose(f, fst), compose(g, snd))

  def constA[:=>:[_, _], **[_, _], T, H[_, _], A, B]: CodeTerm[:=>:, **, T, H, A, H[B, A]] =
    curry(fst[:=>:, **, T, H, A, B])

  def const[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, B]): CodeTerm[:=>:, **, T, H, C, H[A, B]] =
    curry(compose(f, snd[:=>:, **, T, H, C, A]))

  def getConst[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: CodeTerm[:=>:, **, T, H, T, H[A, B]]): CodeTerm[:=>:, **, T, H, A, B] =
    compose(uncurry(f), prod(terminal[:=>:, **, T, H, A], id[:=>:, **, T, H, A]))

  def andThen[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, B], g: CodeTerm[:=>:, **, T, H, B, C]): CodeTerm[:=>:, **, T, H, A, C] =
    compose(g, f)

  def flip[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, (A**B), C]): CodeTerm[:=>:, **, T, H, (B**A), C] =
    compose(f, prod(snd[:=>:, **, T, H, B, A], fst[:=>:, **, T, H, B, A]))

  def swap[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, H[B, C]]): CodeTerm[:=>:, **, T, H, B, H[A, C]] =
    curry(flip(uncurry(f)))

  def pair[:=>:[_, _], **[_, _], T, H[_, _], A, B](a: DataTerm[:=>:, **, T, H, A], b: DataTerm[:=>:, **, T, H, B]): DataTerm[:=>:, **, T, H, A**B] =
    app(app(curry(id[:=>:, **, T, H, A**B]), a), b)

  def eval[:=>:[_, _], **[_, _], T, H[_, _], A, B]: CodeTerm[:=>:, **, T, H, H[A, B] ** A, B] =
    uncurry(id[:=>:, **, T, H, H[A, B]])

  def assocR[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: CodeTerm[:=>:, **, T, H, ((A**B)**C), (A**(B**C))] = {
    val pa = compose(fst[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pb = compose(snd[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pc = snd[:=>:, **, T, H, A**B, C]
    prod(pa, prod(pb, pc))
  }

  def assocL[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: CodeTerm[:=>:, **, T, H, (A**(B**C)), ((A**B)**C)] = {
    val pa = fst[:=>:, **, T, H, A, B**C]
    val pb = compose(fst[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    val pc = compose(snd[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    prod(prod(pa, pb), pc)
  }

  def code[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]]): CodeTerm[:=>:, **, T, H, A, B] =
    getConst(f.code)


  // implementation

  case class Arr[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B) extends CodeTerm[:=>:, **, T, H, A, B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Id[:=>:[_, _], **[_, _], T, H[_, _], A]() extends CodeTerm[:=>:, **, T, H, A, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, B, C], g: CodeTerm[:=>:, **, T, H, A, B]) extends CodeTerm[:=>:, **, T, H, A, C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends CodeTerm[:=>:, **, T, H, (A**B), A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends CodeTerm[:=>:, **, T, H, (A**B), B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, B], g: CodeTerm[:=>:, **, T, H, A, C]) extends CodeTerm[:=>:, **, T, H, A, (B**C)] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Terminal[:=>:[_, _], **[_, _], T, H[_, _], A]() extends CodeTerm[:=>:, **, T, H, A, T] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, (A**B), C]) extends CodeTerm[:=>:, **, T, H, A, H[B, C]] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: CodeTerm[:=>:, **, T, H, A, H[B, C]]) extends CodeTerm[:=>:, **, T, H, (A**B), C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class ConstVar[:=>:[_, _], **[_, _], T, H[_, _], Z, A](a: Term.Var[:=>:, **, T, H, A]) extends CodeTerm[:=>:, **, T, H, Z, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: CodeTerm[:=>:, **, T, H, T, A]) extends DataTerm[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class App[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]], a: Term.Var[:=>:, **, T, H, A]) extends DataTerm[:=>:, **, T, H, B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  class Var[:=>:[_, _], **[_, _], T, H[_, _], A] private[Term]() extends DataTerm[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  def sameVar[:=>:[_, _], **[_, _], T, H[_, _], X, Y](x: Var[:=>:, **, T, H, X], y: Var[:=>:, **, T, H, Y]): Option[X === Y] =
    if(x eq y) Some(Leibniz.force[Nothing, Any, X, Y])
    else None

  def internalize[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, A] => DataTerm[:=>:, **, T, H, B]): CodeTerm[:=>:, **, T, H, A, B] = {
    val v = new Var[:=>:, **, T, H, A]
    f(v).unapply(v)
  }

  def compile[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: CodeTerm[:=>:, **, T, H, A, B])(implicit C: CCC.Aux[:=>:, **, T, H]): A :=>: B =
    f.compile

}
