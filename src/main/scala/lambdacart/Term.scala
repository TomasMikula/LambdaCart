package lambdacart

import scalaz.Leibniz
import scalaz.Leibniz.===

/** Hybrid representation containing both lambda terms and operations of
  * a Cartesian closed category. Used as an intermediate representation
  * in the translation from lambda expressions to Cartesian closed operations.
  */
sealed trait Term[:=>:[_, _], **[_, _], T, A] {
  import Term._

  type τ[X]             =          Term[:=>:, **, T, X]

  type Id[X]            =       Term.Id[:=>:, **, T, X]
  type Var[X]           =      Term.Var[:=>:, **, T, X]
  type Obj[X]           =      Term.Obj[:=>:, **, T, X]
  type App[X, Y]        =      Term.App[:=>:, **, T, X, Y]
  type Abs[X, Y]        =      Term.Abs[:=>:, **, T, X, Y]
  type Arr[X, Y]        =      Term.Arr[:=>:, **, T, X, Y]
  type Fst[X, Y]        =      Term.Fst[:=>:, **, T, X, Y]
  type Snd[X, Y]        =      Term.Snd[:=>:, **, T, X, Y]
  type Prod[X, Y, Z]    =     Term.Prod[:=>:, **, T, X, Y, Z]
  type Terminal[X]      = Term.Terminal[:=>:, **, T, X]
  type Compose[X, Y, Z] =  Term.Compose[:=>:, **, T, X, Y, Z]
  type Curry[X, Y, Z]   =    Term.Curry[:=>:, **, T, X, Y, Z]
  type Uncurry[X, Y, Z] =  Term.Uncurry[:=>:, **, T, X, Y, Z]

  type Visitor[R]       =   TermVisitor[:=>:, **, T, A, R]

  private type Transformer = Visitor[τ[A]]

  // Note: Methods implemented separately in each case class due to
  // major suckiness of pattern matching on GADTs.

  /** Returns `f` such that `f(x) = this` and `x` does not occur in `f`.
    */
  protected def unapply[X](x: Var[X]): τ[X :=>: A]

  protected def containsVarOrApp[X](v: Var[X]): Boolean

  def compile(implicit CC: CCC.Aux[:=>:, **, T]): A

  def visit[Z](visitor: Visitor[Z]): Z

  private def transform(tr: Transformer): τ[A] = visit(tr)

  private[Term] def coerce[B](implicit ev: A === B): τ[B] = ev.subst[τ](this)

  def size: Int = visit(new Visitor[Int] {
    def apply(a: Var[A]): Int = 1
    def apply[X](a: App[X,A]): Int = 1 + a.f.size + a.a.size
    def apply[X, Y](a: Abs[X,Y])(implicit ev: (X :=>: Y) === A): Int = 1 + a.b.size
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

  /** Abstraction elimination. Returns an equivalent term that contains no lambda abstractions.
    * When `this` is a closed term, the result also contains no variables.
    */
  final def elimAbs: τ[A] = transform(new Transformer {

    def apply[X, Y](a:      Arr[X,Y])(implicit ev: (X :=>: Y)      === A) = a.coerce
    def apply[X]   (a:       Id[X])  (implicit ev: (X :=>: X)      === A) = a.coerce
    def apply[X, Y](a:      Snd[X,Y])(implicit ev: ((X**Y) :=>: Y) === A) = a.coerce
    def apply[X, Y](a:      Fst[X,Y])(implicit ev: ((X**Y) :=>: X) === A) = a.coerce
    def apply[X   ](a: Terminal[X])  (implicit ev: (X :=>: T)      === A) = a.coerce
    def apply      (a:      Var[A])                                       = a

    def apply[X, Y, Z](a: Uncurry[X,Y,Z])(implicit ev: :=>:[**[X,Y],Z] === A) =
      Uncurry(a.f.elimAbs).coerce

    def apply[X, Y, Z](a: Curry[X,Y,Z])(implicit ev: :=>:[X,:=>:[Y,Z]] === A) =
      Curry(a.f.elimAbs).coerce

    def apply[X, Y, Z](a: Prod[X,Y,Z])(implicit ev: :=>:[X,**[Y,Z]] === A) =
      Prod(a.f.elimAbs, a.g.elimAbs).coerce

    def apply[X, Y, Z](a: Compose[X,Y,Z])(implicit ev: :=>:[X,Z] === A) =
      Compose(a.f.elimAbs, a.g.elimAbs).coerce

    def apply(a: Obj[A]) =
      Obj(a.f.elimAbs)

    def apply[X](a: App[X,A]) =
      App(a.f.elimAbs, a.a.elimAbs)

    def apply[X, Y](a: Abs[X,Y])(implicit ev: (X :=>: Y) === A) =
      a.b.elimAbs.unapply(a.a).coerce
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
  def arr[:=>:[_, _], **[_, _], T, A, B](f: A :=>: B): Term[:=>:, **, T, A :=>: B] = Arr(f)

  // Cartesian operations
  def id[:=>:[_, _], **[_, _], T, A]: Term[:=>:, **, T, A :=>: A] = Id()
  def compose[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, B :=>: C], g: Term[:=>:, **, T, A :=>: B]): Term[:=>:, **, T, A :=>: C] = Compose(f, g)
  def fst[:=>:[_, _], **[_, _], T, A, B]: Term[:=>:, **, T, (A**B) :=>: A] = Fst()
  def snd[:=>:[_, _], **[_, _], T, A, B]: Term[:=>:, **, T, (A**B) :=>: B] = Snd()
  def prod[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B], g: Term[:=>:, **, T, A :=>: C]): Term[:=>:, **, T, A :=>: (B**C)] = Prod(f, g)
  def terminal[:=>:[_, _], **[_, _], T, A]: Term[:=>:, **, T, A :=>: T] = Terminal()
  def curry[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, (A**B) :=>: C]): Term[:=>:, **, T, A :=>: B :=>: C] = Curry(f)
  def uncurry[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B :=>: C]): Term[:=>:, **, T, (A**B) :=>: C] = Uncurry(f)

  // object A represented as an arrow from terminal object to A (eliminated during compilation)
  def obj[:=>:[_, _], **[_, _], T, A](f: Term[:=>:, **, T, T :=>: A]): Term[:=>:, **, T, A] = Obj(f)

  // Lambda operations (will be eliminated during compilation)
  def freshVar[:=>:[_, _], **[_, _], T, A]: Var[:=>:, **, T, A] = new Var
  def abs[:=>:[_, _], **[_, _], T, A, B](a: Var[:=>:, **, T, A], b: Term[:=>:, **, T, B]): Term[:=>:, **, T, A :=>: B] = Abs(a, b)
  def app[:=>:[_, _], **[_, _], T, A, B](f: Term[:=>:, **, T, A :=>: B], a: Term[:=>:, **, T, A]): Term[:=>:, **, T, B] = App(f, a)


  // derived Cartesian operations

  def constA[:=>:[_, _], **[_, _], T, A, B]: Term[:=>:, **, T, A :=>: B :=>: A] =
    curry(fst[:=>:, **, T, A, B])

  def const[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B]): Term[:=>:, **, T, C :=>: A :=>: B] =
    curry(compose(f, snd[:=>:, **, T, C, A]))

  def andThen[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B], g: Term[:=>:, **, T, B :=>: C]): Term[:=>:, **, T, A :=>: C] =
    compose(g, f)

  def flip[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, (A**B) :=>: C]): Term[:=>:, **, T, (B**A) :=>: C] =
    compose(f, prod(snd[:=>:, **, T, B, A], fst[:=>:, **, T, B, A]))

  def swap[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B :=>: C]): Term[:=>:, **, T, B :=>: A :=>: C] =
    curry(flip(uncurry(f)))

  def pair[:=>:[_, _], **[_, _], T, A, B](a: Term[:=>:, **, T, A], b: Term[:=>:, **, T, B]): Term[:=>:, **, T, A**B] =
    app(app(curry(id[:=>:, **, T, A**B]), a), b)

  def appA[:=>:[_, _], **[_, _], T, A, B]: Term[:=>:, **, T, ((A :=>: B) ** A) :=>: B] =
    uncurry(id[:=>:, **, T, A :=>: B])

  def composeA[:=>:[_, _], **[_, _], T, A, B, C]: Term[:=>:, **, T, ((B :=>: C) ** (A :=>: B)) :=>: A :=>: C] =
    flip(curry(flip(compose(uncurry(flip(andThen(appA[:=>:, **, T, A, B], curry(flip(appA[:=>:, **, T, B, C]))))), assocL))))

  def assocR[:=>:[_, _], **[_, _], T, A, B, C]: Term[:=>:, **, T, ((A**B)**C) :=>: (A**(B**C))] = {
    val pa = compose(fst[:=>:, **, T, A, B], fst[:=>:, **, T, A**B, C])
    val pb = compose(snd[:=>:, **, T, A, B], fst[:=>:, **, T, A**B, C])
    val pc = snd[:=>:, **, T, A**B, C]
    prod(pa, prod(pb, pc))
  }

  def assocL[:=>:[_, _], **[_, _], T, A, B, C]: Term[:=>:, **, T, (A**(B**C)) :=>: ((A**B)**C)] = {
    val pa = fst[:=>:, **, T, A, B**C]
    val pb = compose(fst[:=>:, **, T, B, C], snd[:=>:, **, T, A, B**C])
    val pc = compose(snd[:=>:, **, T, B, C], snd[:=>:, **, T, A, B**C])
    prod(prod(pa, pb), pc)
  }


  // implementation

  case class Arr[:=>:[_, _], **[_, _], T, A, B](f: A :=>: B) extends Term[:=>:, **, T, A :=>: B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = false
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: B] =
      const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: B = f
  }

  case class Id[:=>:[_, _], **[_, _], T, A]() extends Term[:=>:, **, T, A :=>: A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = false
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: A] =
      const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: A = CC.id[A]
  }

  case class Compose[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, B :=>: C], g: Term[:=>:, **, T, A :=>: B]) extends Term[:=>:, **, T, A :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = f.containsVarOrApp(v) || g.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: C] =
      if(containsVarOrApp(x))
        andThen(prod(f.unapply(x), g.unapply(x)), composeA[:=>:, **, T, A, B, C])
      else
        const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: C =
      CC.compose(f.compile, g.compile)
  }

  case class Fst[:=>:[_, _], **[_, _], T, A, B]() extends Term[:=>:, **, T, (A**B) :=>: A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = false
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: (A**B) :=>: A] =
      const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): (A**B) :=>: A =
      CC.fst[A, B]
  }

  case class Snd[:=>:[_, _], **[_, _], T, A, B]() extends Term[:=>:, **, T, (A**B) :=>: B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = false
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: (A**B) :=>: B] =
      const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): (A**B) :=>: B =
      CC.snd[A, B]
  }

  case class Prod[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B], g: Term[:=>:, **, T, A :=>: C]) extends Term[:=>:, **, T, A :=>: (B**C)] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = f.containsVarOrApp(v) || g.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>: , **, T, X :=>: A :=>: (B**C)] =
      if(containsVarOrApp(x)) curry(prod(uncurry(f.unapply(x)), uncurry(g.unapply(x))))
      else const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: (B**C) =
      CC.prod(f.compile, g.compile)
  }

  case class Terminal[:=>:[_, _], **[_, _], T, A]() extends Term[:=>:, **, T, A :=>: T] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = false
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: T] =
      const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: T =
      CC.terminal[A]
  }

  case class Curry[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, (A**B) :=>: C]) extends Term[:=>:, **, T, A :=>: B :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = f.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: B :=>: C] =
      if(containsVarOrApp(x)) curry(curry(andThen(assocR[:=>:, **, T, X, A, B], uncurry(f.unapply(x)))))
      else const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: B :=>: C =
      CC.curry(f.compile)
  }

  case class Uncurry[:=>:[_, _], **[_, _], T, A, B, C](f: Term[:=>:, **, T, A :=>: B :=>: C]) extends Term[:=>:, **, T, (A**B) :=>: C] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = f.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: (A**B) :=>: C] =
      if(containsVarOrApp(x)) curry(andThen(assocL[:=>:, **, T, X, A, B], uncurry(uncurry(f.unapply(x)))))
      else const(this)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): (A**B) :=>: C =
      CC.uncurry(f.compile)
  }

  case class Obj[:=>:[_, _], **[_, _], T, A](f: Term[:=>:, **, T, T :=>: A]) extends Term[:=>:, **, T, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = f.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A] =
      if(f.containsVarOrApp(x)) obj(swap(f.unapply(x)))
      else compose(f, terminal)
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A =
      sys.error("Cannot compile Obj.")
  }

  case class Abs[:=>:[_, _], **[_, _], T, A, B](a: Term.Var[:=>:, **, T, A], b: Term[:=>:, **, T, B]) extends Term[:=>:, **, T, A :=>: B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = a == v || b.containsVarOrApp(v)
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A :=>: B] =
      sys.error("Abstraction should have been eliminated first.")
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A :=>: B =
      sys.error("Cannot compile lambda abstraction.")
  }

  case class App[:=>:[_, _], **[_, _], T, A, B](f: Term[:=>:, **, T, A :=>: B], a: Term[:=>:, **, T, A]) extends Term[:=>:, **, T, B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = true
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: B] =
      if(!f.containsVarOrApp(x)) andThen(a.unapply(x), f)
      else andThen(prod(f.unapply(x), a.unapply(x)), appA[:=>:, **, T, A, B])
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): B =
      sys.error("Cannot compile function application.")
  }

  class Var[:=>:[_, _], **[_, _], T, A] private[Term]() extends Term[:=>:, **, T, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
    protected def containsVarOrApp[X](v: Var[X]): Boolean = this == v
    protected def unapply[X](x: Var[X]): Term[:=>:, **, T, X :=>: A] =
      sameVar(this, x) match {
        case Some(ev) => ev.subst[λ[χ => Term[:=>:, **, T, χ :=>: A]]](id[:=>:, **, T, A])
        case None     => app(constA[:=>:, **, T, A, X], this)
      }
    def compile(implicit CC: CCC.Aux[:=>:, **, T]): A =
      sys.error("Cannot compile variable.")
  }

  def sameVar[:=>:[_, _], **[_, _], T, X, Y](x: Var[:=>:, **, T, X], y: Var[:=>:, **, T, Y]): Option[X === Y] =
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

  def internalize[:=>:[_, _], **[_, _], T, A, B](f: Term[:=>:, **, T, A] => Term[:=>:, **, T, B]): Term[:=>:, **, T, A :=>: B] = {
    val v = Term.freshVar[:=>:, **, T, A]
    Term.abs(v, f(v))
  }

}

trait TermVisitor[:=>:[_, _], **[_, _], T, A, R] {
  import Term._

  def apply[X, Y, Z](a:    Curry[:=>:, **, T, X, Y, Z])(implicit ev: (X :=>: Y :=>: Z) === A) : R
  def apply[X, Y, Z](a:  Uncurry[:=>:, **, T, X, Y, Z])(implicit ev: ((X ** Y) :=>: Z) === A) : R
  def apply[X, Y, Z](a:  Compose[:=>:, **, T, X, Y, Z])(implicit ev: (X :=>: Z)        === A) : R
  def apply[X, Y, Z](a:     Prod[:=>:, **, T, X, Y, Z])(implicit ev: (X :=>: (Y**Z))   === A) : R
  def apply[X, Y]   (a:      Fst[:=>:, **, T, X, Y])   (implicit ev: ((X**Y) :=>: X)   === A) : R
  def apply[X, Y]   (a:      Snd[:=>:, **, T, X, Y])   (implicit ev: ((X**Y) :=>: Y)   === A) : R
  def apply[X]      (a:       Id[:=>:, **, T, X])      (implicit ev: (X :=>: X)        === A) : R
  def apply[X]      (a: Terminal[:=>:, **, T, X])      (implicit ev: (X :=>: T)        === A) : R
  def apply[X, Y]   (a:      Arr[:=>:, **, T, X, Y])   (implicit ev: (X :=>: Y)        === A) : R
  def apply[X, Y]   (a:      Abs[:=>:, **, T, X, Y])   (implicit ev: (X :=>: Y)        === A) : R
  def apply[X]      (a:      App[:=>:, **, T, X, A])                                          : R
  def apply         (a:      Obj[:=>:, **, T, A])                                             : R
  def apply         (a:      Var[:=>:, **, T, A])                                             : R
}
