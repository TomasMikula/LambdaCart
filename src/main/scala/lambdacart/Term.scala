package lambdacart

import scalaz.Leibniz
import scalaz.Leibniz.===

/** Hybrid representation containing both lambda terms and operations of
  * a Cartesian closed category. Used as an intermediate representation
  * in the translation from lambda expressions to Cartesian closed operations.
  */
sealed trait Term[:=>:[_, _], **[_, _], T, H[_, _], A] {
  import Term._

  type τ[X]             =          Term[:=>:, **, T, H, X]

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

  type Visitor[R]       =   TermVisitor[:=>:, **, T, H, A, R]

  def visit[Z](visitor: Visitor[Z]): Z

  private[Term] def coerce[B](implicit ev: A === B): τ[B] = ev.subst[τ](this)
  private[Term] implicit class LeibnizOps[X, Y](ev: X === Y) {
    def lift[F[_]]: F[X] === F[Y] = ev.subst[λ[α => F[X] === F[α]]](Leibniz.refl)
  }
  private def const[X, Y, Z](f: τ[X :=>: Y]): τ[Z :=>: X :=>: Y] = Term.const(f)

  def size: Int = visit(new Visitor[Int] {
    def apply(a: Var[A]): Int = 1
    def apply[X](a: App[X,A]): Int = 1 + a.f.size + a.a.size
    def apply(a: Obj[A]): Int = 1
    def apply[X, Y, Z](a: Uncurry[X,Y,Z])(implicit ev: ===[:=>:[**[X,Y],Z],A]): Int = 1 + a.f.size
    def apply[X, Y, Z](a: Curry[X,Y,Z])(implicit ev: ===[:=>:[X,:=>:[Y,Z]],A]): Int = 1 + a.f.size
    def apply[X](a: Terminal[X])(implicit ev: ===[:=>:[X,T],A]): Int = 1
    def apply[X, Y, Z](a: Prod[X,Y,Z])(implicit ev: ===[:=>:[X,**[Y,Z]],A]): Int = 1 + a.f.size + a.g.size
    def apply[X, Y](a: Snd[X,Y])(implicit ev: ===[:=>:[**[X,Y],Y],A]): Int = 1
    def apply[X, Y](a: Fst[X,Y])(implicit ev: ===[:=>:[**[X,Y],X],A]): Int = 1
    def apply[X, Y, Z](a: Compose[X,Y,Z])(implicit ev: ===[:=>:[X,Z],A]): Int = 1 + a.f.size + a.g.size
    def apply[X](a: Id[X])(implicit ev: ===[:=>:[X,X],A]): Int = 1
    def apply[X, Y](a: Arr[X,Y])(implicit ev: ===[:=>:[X,Y],A]): Int = 1
  })

  /** Returns `f` such that `f(x) = this` and `x` does not occur in `f`.
    */
  private final def unapply[V](x: Var[V]): τ[V :=>: A] = visit(new Visitor[τ[V :=>: A]] {

    def apply[X, Y](a:      Arr[X,Y])(implicit ev: (X :=>: Y)      === A) = const[X,    Y, V](a).coerce(ev.lift[V :=>: ?])
    def apply[X]   (a:       Id[X])  (implicit ev: (X :=>: X)      === A) = const[X,    X, V](a).coerce(ev.lift[V :=>: ?])
    def apply[X, Y](a:      Snd[X,Y])(implicit ev: ((X**Y) :=>: Y) === A) = const[X**Y, Y, V](a).coerce(ev.lift[V :=>: ?])
    def apply[X, Y](a:      Fst[X,Y])(implicit ev: ((X**Y) :=>: X) === A) = const[X**Y, X, V](a).coerce(ev.lift[V :=>: ?])
    def apply[X   ](a: Terminal[X])  (implicit ev: (X :=>: T)      === A) = const[X,    T, V](a).coerce(ev.lift[V :=>: ?])

    def apply(a: Var[A]) =
      sameVar(a, x) match {
        case Some(ev) => ev.subst[λ[χ => τ[χ :=>: A]]](id[:=>:, **, T, H, A])
        case None     => app(constA[:=>:, **, T, H, A, V], a)
      }

    def apply[X, Y, Z](a: Uncurry[X,Y,Z])(implicit ev: :=>:[**[X,Y],Z] === A) = (
      if(a.containsVarOrApp(x)) curry(andThen(assocL[:=>:, **, T, H, V, X, Y], uncurry(uncurry(a.f.unapply(x)))))
      else const[X**Y, Z, V](a)
    ).coerce(ev.lift[V :=>: ?])

    def apply[X, Y, Z](a: Curry[X,Y,Z])(implicit ev: (X :=>: Y :=>: Z) === A) = (
      if(a.containsVarOrApp(x)) curry(curry(andThen(assocR[:=>:, **, T, H, V, X, Y], uncurry(a.f.unapply(x)))))
      else const[X, Y :=>: Z, V](a)
    ).coerce(ev.lift[V :=>: ?])

    def apply[X, Y, Z](a: Prod[X,Y,Z])(implicit ev: :=>:[X,**[Y,Z]] === A) = (
      if(a.containsVarOrApp(x)) curry(prod(uncurry(a.f.unapply(x)), uncurry(a.g.unapply(x))))
      else const[X, Y**Z, V](a)
    ).coerce(ev.lift[V :=>: ?])

    def apply[X, Y, Z](a: Compose[X,Y,Z])(implicit ev: :=>:[X,Z] === A) = (
      if(a.containsVarOrApp(x))
        andThen(prod(a.f.unapply(x), a.g.unapply(x)), composeA[:=>:, **, T, H, X, Y, Z])
      else
        const[X, Z, V](a)
    ).coerce(ev.lift[V :=>: ?])

    def apply(a: Obj[A]) =
      if(a.f.containsVarOrApp(x)) obj(swap(a.f.unapply(x)))
      else compose(a.f, terminal)

    def apply[X](a: App[X,A]) =
      if(!a.f.containsVarOrApp(x)) andThen(a.a.unapply(x), a.f)
      else andThen(prod(a.f.unapply(x), a.a.unapply(x)), appA[:=>:, **, T, H, X, A])
  })


  private[Term] final def containsVarOrApp[V](v: Var[V]): Boolean = visit(new Visitor[Boolean] {

    def apply[X, Y](a:      Arr[X,Y])(implicit ev: (X :=>: Y)      === A) = false
    def apply[X]   (a:       Id[X])  (implicit ev: (X :=>: X)      === A) = false
    def apply[X, Y](a:      Snd[X,Y])(implicit ev: ((X**Y) :=>: Y) === A) = false
    def apply[X, Y](a:      Fst[X,Y])(implicit ev: ((X**Y) :=>: X) === A) = false
    def apply[X   ](a: Terminal[X])  (implicit ev: (X :=>: T)      === A) = false

    def apply(a: Var[A]) = a == v

    def apply[X, Y, Z](a: Uncurry[X,Y,Z])(implicit ev: :=>:[**[X,Y],Z] === A) =
      a.f.containsVarOrApp(v)

    def apply[X, Y, Z](a: Curry[X,Y,Z])(implicit ev: :=>:[X,:=>:[Y,Z]] === A) =
      a.f.containsVarOrApp(v)

    def apply[X, Y, Z](a: Prod[X,Y,Z])(implicit ev: :=>:[X,**[Y,Z]] === A) =
      a.f.containsVarOrApp(v) || a.g.containsVarOrApp(v)

    def apply[X, Y, Z](a: Compose[X,Y,Z])(implicit ev: :=>:[X,Z] === A) =
      a.f.containsVarOrApp(v) || a.g.containsVarOrApp(v)

    def apply(a: Obj[A]) =
      a.f.containsVarOrApp(v)

    def apply[X](a: App[X,A]) = true
  })

  final def compile(implicit CC: CCC.AuxHI[:=>:, **, T]): A = visit(new Visitor[A] {

    def apply[X, Y]   (a:       Arr[X,Y])(implicit ev: (X :=>: Y)      === A) = ev(a.f)
    def apply[X]      (a:          Id[X])(implicit ev: (X :=>: X)      === A) = ev(CC.id[X])
    def apply[X, Y]   (a:       Snd[X,Y])(implicit ev: ((X**Y) :=>: Y) === A) = ev(CC.snd[X, Y])
    def apply[X, Y]   (a:       Fst[X,Y])(implicit ev: ((X**Y) :=>: X) === A) = ev(CC.fst[X, Y])
    def apply[X]      (a:    Terminal[X])(implicit ev: (X :=>: T)      === A) = ev(CC.terminal[X])
    def apply[X, Y, Z](a: Uncurry[X,Y,Z])(implicit ev: ((X**Y) :=>: Z) === A) = ev(CC.uncurry(a.f.compile))
    def apply[X, Y, Z](a:   Curry[X,Y,Z])(implicit ev: (X :=>: Y:=>:Z) === A) = ev(CC.curry(a.f.compile))
    def apply[X, Y, Z](a:    Prod[X,Y,Z])(implicit ev: (X :=>: (Y**Z)) === A) = ev(CC.prod(a.f.compile, a.g.compile))
    def apply[X, Y, Z](a: Compose[X,Y,Z])(implicit ev: (X :=>: Z)      === A) = ev(CC.compose(a.f.compile, a.g.compile))

    def apply(a: Obj[A]) = sys.error("Cannot compile Obj.")
    def apply(a: Var[A]) = sys.error("Cannot compile variable.")
    def apply[X](a: App[X,A]) = sys.error("Cannot compile function application.")
  })


  /* Syntax */

  // Not a usual map signagure. This is to abuse Scala's `for` syntax.
  def map[B](f: τ[A] => τ[B]): τ[B] =
    f(this)

  // Not a usual flatMap signagure. This is to abuse Scala's `for` syntax.
  def flatMap[B](f: τ[A] => τ[B]): τ[B] =
    f(this)

  def **[B](b: τ[B]): τ[A**B] = pair(this, b)

}

object Term {

  // wrap primitive arrow
  def arr[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B): Term[:=>:, **, T, H, A :=>: B] = Arr(f)

  // Cartesian operations
  def id[:=>:[_, _], **[_, _], T, H[_, _], A]: Term[:=>:, **, T, H, A :=>: A] = Id()
  def compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, B :=>: C], g: Term[:=>:, **, T, H, A :=>: B]): Term[:=>:, **, T, H, A :=>: C] = Compose(f, g)
  def fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]: Term[:=>:, **, T, H, (A**B) :=>: A] = Fst()
  def snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]: Term[:=>:, **, T, H, (A**B) :=>: B] = Snd()
  def prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B], g: Term[:=>:, **, T, H, A :=>: C]): Term[:=>:, **, T, H, A :=>: (B**C)] = Prod(f, g)
  def terminal[:=>:[_, _], **[_, _], T, H[_, _], A]: Term[:=>:, **, T, H, A :=>: T] = Terminal()
  def curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, (A**B) :=>: C]): Term[:=>:, **, T, H, A :=>: B :=>: C] = Curry(f)
  def uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B :=>: C]): Term[:=>:, **, T, H, (A**B) :=>: C] = Uncurry(f)

  // object A represented as an arrow from terminal object to A (eliminated during compilation)
  def obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: Term[:=>:, **, T, H, T :=>: A]): Term[:=>:, **, T, H, A] = Obj(f)

  // Lambda operations (will be eliminated during compilation)
  def freshVar[:=>:[_, _], **[_, _], T, H[_, _], A]: Var[:=>:, **, T, H, A] = new Var
  def app[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: Term[:=>:, **, T, H, A :=>: B], a: Term[:=>:, **, T, H, A]): Term[:=>:, **, T, H, B] = App(f, a)


  // derived Cartesian closed operations

  def constA[:=>:[_, _], **[_, _], T, H[_, _], A, B]: Term[:=>:, **, T, H, A :=>: B :=>: A] =
    curry(fst[:=>:, **, T, H, A, B])

  def const[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B]): Term[:=>:, **, T, H, C :=>: A :=>: B] =
    curry(compose(f, snd[:=>:, **, T, H, C, A]))

  def andThen[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B], g: Term[:=>:, **, T, H, B :=>: C]): Term[:=>:, **, T, H, A :=>: C] =
    compose(g, f)

  def flip[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, (A**B) :=>: C]): Term[:=>:, **, T, H, (B**A) :=>: C] =
    compose(f, prod(snd[:=>:, **, T, H, B, A], fst[:=>:, **, T, H, B, A]))

  def swap[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B :=>: C]): Term[:=>:, **, T, H, B :=>: A :=>: C] =
    curry(flip(uncurry(f)))

  def pair[:=>:[_, _], **[_, _], T, H[_, _], A, B](a: Term[:=>:, **, T, H, A], b: Term[:=>:, **, T, H, B]): Term[:=>:, **, T, H, A**B] =
    app(app(curry(id[:=>:, **, T, H, A**B]), a), b)

  def appA[:=>:[_, _], **[_, _], T, H[_, _], A, B]: Term[:=>:, **, T, H, ((A :=>: B) ** A) :=>: B] =
    uncurry(id[:=>:, **, T, H, A :=>: B])

  def composeA[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: Term[:=>:, **, T, H, ((B :=>: C) ** (A :=>: B)) :=>: A :=>: C] =
    flip(curry(flip(compose(uncurry(flip(andThen(appA[:=>:, **, T, H, A, B], curry(flip(appA[:=>:, **, T, H, B, C]))))), assocL))))

  def assocR[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: Term[:=>:, **, T, H, ((A**B)**C) :=>: (A**(B**C))] = {
    val pa = compose(fst[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pb = compose(snd[:=>:, **, T, H, A, B], fst[:=>:, **, T, H, A**B, C])
    val pc = snd[:=>:, **, T, H, A**B, C]
    prod(pa, prod(pb, pc))
  }

  def assocL[:=>:[_, _], **[_, _], T, H[_, _], A, B, C]: Term[:=>:, **, T, H, (A**(B**C)) :=>: ((A**B)**C)] = {
    val pa = fst[:=>:, **, T, H, A, B**C]
    val pb = compose(fst[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    val pc = compose(snd[:=>:, **, T, H, B, C], snd[:=>:, **, T, H, A, B**C])
    prod(prod(pa, pb), pc)
  }


  // implementation

  case class Arr[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B) extends Term[:=>:, **, T, H, A :=>: B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Id[:=>:[_, _], **[_, _], T, H[_, _], A]() extends Term[:=>:, **, T, H, A :=>: A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Compose[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, B :=>: C], g: Term[:=>:, **, T, H, A :=>: B]) extends Term[:=>:, **, T, H, A :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Fst[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends Term[:=>:, **, T, H, (A**B) :=>: A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Snd[:=>:[_, _], **[_, _], T, H[_, _], A, B]() extends Term[:=>:, **, T, H, (A**B) :=>: B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Prod[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B], g: Term[:=>:, **, T, H, A :=>: C]) extends Term[:=>:, **, T, H, A :=>: (B**C)] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Terminal[:=>:[_, _], **[_, _], T, H[_, _], A]() extends Term[:=>:, **, T, H, A :=>: T] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Curry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, (A**B) :=>: C]) extends Term[:=>:, **, T, H, A :=>: B :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Uncurry[:=>:[_, _], **[_, _], T, H[_, _], A, B, C](f: Term[:=>:, **, T, H, A :=>: B :=>: C]) extends Term[:=>:, **, T, H, (A**B) :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class Obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: Term[:=>:, **, T, H, T :=>: A]) extends Term[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class App[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: Term[:=>:, **, T, H, A :=>: B], a: Term[:=>:, **, T, H, A]) extends Term[:=>:, **, T, H, B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  class Var[:=>:[_, _], **[_, _], T, H[_, _], A] private[Term]() extends Term[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  def sameVar[:=>:[_, _], **[_, _], T, H[_, _], X, Y](x: Var[:=>:, **, T, H, X], y: Var[:=>:, **, T, H, Y]): Option[X === Y] =
    if(x eq y) Some(Leibniz.force[Nothing, Any, X, Y])
    else None

//  def compile[:=>:[_, _], **[_, _], T, A, B](t: Term[:=>:, **, T, A :=>: B])(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: B = {
//    // assuming:
//    //  - t is a closed term;
//    //  - any App and Obj is inside some Abs (e.g. the outermost term is Abs)
//
//    val t1 = t.elimAbs
//
//    // t1 contains no Abs, Var, App or Obj nodes
//
//    t1.compile
//  }

  def internalize[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: Term[:=>:, **, T, H, A] => Term[:=>:, **, T, H, B]): Term[:=>:, **, T, H, A :=>: B] = {
    val v = Term.freshVar[:=>:, **, T, H, A]
    f(v).unapply(v)
  }

}

trait TermVisitor[:=>:[_, _], **[_, _], T, H[_, _], A, R] {
  import Term._

  def apply[X, Y, Z](a:    Curry[:=>:, **, T, H, X, Y, Z])(implicit ev: (X :=>: Y :=>: Z) === A) : R
  def apply[X, Y, Z](a:  Uncurry[:=>:, **, T, H, X, Y, Z])(implicit ev: ((X ** Y) :=>: Z) === A) : R
  def apply[X, Y, Z](a:  Compose[:=>:, **, T, H, X, Y, Z])(implicit ev: (X :=>: Z)        === A) : R
  def apply[X, Y, Z](a:     Prod[:=>:, **, T, H, X, Y, Z])(implicit ev: (X :=>: (Y**Z))   === A) : R
  def apply[X, Y]   (a:      Fst[:=>:, **, T, H, X, Y])   (implicit ev: ((X**Y) :=>: X)   === A) : R
  def apply[X, Y]   (a:      Snd[:=>:, **, T, H, X, Y])   (implicit ev: ((X**Y) :=>: Y)   === A) : R
  def apply[X]      (a:       Id[:=>:, **, T, H, X])      (implicit ev: (X :=>: X)        === A) : R
  def apply[X]      (a: Terminal[:=>:, **, T, H, X])      (implicit ev: (X :=>: T)        === A) : R
  def apply[X, Y]   (a:      Arr[:=>:, **, T, H, X, Y])   (implicit ev: (X :=>: Y)        === A) : R
  def apply[X]      (a:      App[:=>:, **, T, H, X, A])                                          : R
  def apply         (a:      Obj[:=>:, **, T, H, A])                                             : R
  def apply         (a:      Var[:=>:, **, T, H, A])                                             : R
}
