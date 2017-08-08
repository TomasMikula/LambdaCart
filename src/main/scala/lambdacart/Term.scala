package lambdacart

import lambdacart.util.{~~>, LeibnizOps}
import scalaz.Leibniz
import scalaz.Leibniz.===

sealed trait DataTerm[:=>:[_, _], **[_, _], T, H[_, _], A] {
  import CodeTerm._
  import DataTerm._

  type $[X]       =         DataTerm[:=>:, **, T, H, X]
  type φ[X, Y]    =         CodeTerm[:=>:, **, T, H, X, Y]

  type Var[X]     =     DataTerm.Var[:=>:, **, T, H, X]
  type Obj[X]     =     DataTerm.Obj[:=>:, **, T, H, X]
  type App[X, Y]  =     DataTerm.App[:=>:, **, T, H, X, Y]

  type Visitor[R] = DataTerm.Visitor[:=>:, **, T, H, A, R]

  def visit[R](v: Visitor[R]): R


  type :≡>:[X, Y] = Either[X :=>: Y, Var[Y]]

  def wrap[X, Y](f: FreeCCC[:≡>:, **, T, H, X, Y]): φ[X, Y] = CodeTerm.wrap(f)

  def id[X]: φ[X, X]                                      = wrap(FreeCCC.id[:≡>:, **, T, H, X])
  def compose[X, Y, Z](f: φ[Y, Z], g: φ[X, Y]): φ[X, Z]   = wrap(FreeCCC.compose[:≡>:, **, T, H, X, Y, Z](f.unwrap, g.unwrap))
  def fst[X, Y]: φ[(X**Y), X]                             = wrap(FreeCCC.fst)
  def snd[X, Y]: φ[(X**Y), Y]                             = wrap(FreeCCC.snd)
  def prod[X, Y, Z](f: φ[X, Y], g: φ[X, Z]): φ[X, (Y**Z)] = wrap(FreeCCC.prod[:≡>:, **, T, H, X, Y, Z](f.unwrap, g.unwrap))
  def terminal[X]: φ[X, T]                                = wrap(FreeCCC.terminal)
  def curry[X, Y, Z](f: φ[(X**Y), Z]): φ[X, H[Y, Z]]      = wrap(FreeCCC.curry[:≡>:, **, T, H, X, Y, Z](f.unwrap))
  def uncurry[X, Y, Z](f: φ[X, H[Y, Z]]): φ[(X**Y), Z]    = wrap(FreeCCC.uncurry[:≡>:, **, T, H, X, Y, Z](f.unwrap))

  def constA[X, Y]: φ[X, H[Y, X]]                       = wrap(FreeCCC.constA)
  def getConst[X, Y](f: φ[T, H[X, Y]]): φ[X, Y]         = wrap(FreeCCC.getConst[:≡>:, **, T, H, X, Y](f.unwrap))
  def andThen[X, Y, Z](f: φ[X, Y], g: φ[Y, Z]): φ[X, Z] = wrap(FreeCCC.andThen[:≡>:, **, T, H, X, Y, Z](f.unwrap, g.unwrap))
  def flip[X, Y, Z](f: φ[(X**Y), Z]): φ[(Y**X), Z]      = wrap(FreeCCC.flip[:≡>:, **, T, H, X, Y, Z](f.unwrap))
  def swap[X, Y, Z](f: φ[X, H[Y, Z]]): φ[Y, H[X, Z]]    = wrap(FreeCCC.swap[:≡>:, **, T, H, X, Y, Z](f.unwrap))
  def eval[X, Y]: φ[H[X, Y] ** X, Y]                    = wrap(FreeCCC.eval)
  def assocR[X, Y, Z]: φ[((X**Y)**Z), (X**(Y**Z))]      = wrap(FreeCCC.assocR)
  def assocL[X, Y, Z]: φ[(X**(Y**Z)), ((X**Y)**Z)]      = wrap(FreeCCC.assocL)
  def diag[X]: φ[X, (X ** X)]                           = wrap(FreeCCC.diag)
  def parallel[X1, X2, Y1, Y2](f: φ[X1, Y1], g: φ[X2, Y2]): φ[(X1**X2), (Y1**Y2)] =
    wrap(FreeCCC.parallel[:≡>:, **, T, H, X1, X2, Y1, Y2](f.unwrap, g.unwrap))

  def size: Int = visit(new Visitor[Int] {
    def apply(a: Var[A]): Int = 1
    def apply[X](a: App[X,A]): Int = 1 + a.f.size + a.a.size
    def apply(a: Obj[A]): Int = 1 + a.f.size
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
      if(!a.f.containsVar(v)) andThen(a.a.unapply(v), CodeTerm.code(a.f))
      else andThen(prod(a.f.unapply(v), a.a.unapply(v)), eval[X, A])

    def apply(a: Var[A]) =
      sameVar(a, v) match {
        case Some(ev) => id[A].castA[V](ev)
        case None     => constVar(a)
      }
  })

  def code: φ[T, A] =
    visit(new Visitor[φ[T, A]] {
      def apply   (a: Obj[A])   = a.f
      def apply   (a: Var[A])   = constVar(a)
      def apply[X](a: App[X, A])= compose(CodeTerm.code(a.f), a.a.code)
    })


  /* Syntax */

  // Not a usual map signagure. This is to abuse Scala's `for` syntax.
  def map[B](f: $[A] => $[B]): $[B] =
    f(this)

  // Not a usual flatMap signagure. This is to abuse Scala's `for` syntax.
  def flatMap[B](f: $[A] => $[B]): $[B] =
    f(this)

  def **[B](b: $[B]): $[A ** B] = app(app(curry(id[A**B]), this), b)
  def **[B, C](f: φ[B, C]): $[A ** H[B, C]] = this ** f.data
  def get_1[X, Y](implicit ev: A === (X ** Y)): $[X] = app(fst[X, Y], ev.subst[$](this))
  def get_2[X, Y](implicit ev: A === (X ** Y)): $[Y] = app(snd[X, Y], ev.subst[$](this))
}

object DataTerm {
  import CodeTerm._

  case class Obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: CodeTerm[:=>:, **, T, H, T, A]) extends DataTerm[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class App[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]], a: DataTerm.Var[:=>:, **, T, H, A]) extends DataTerm[:=>:, **, T, H, B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  class Var[:=>:[_, _], **[_, _], T, H[_, _], A] private[lambdacart]() extends DataTerm[:=>:, **, T, H, A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  def sameVar[:=>:[_, _], **[_, _], T, H[_, _], X, Y](x: Var[:=>:, **, T, H, X], y: Var[:=>:, **, T, H, Y]): Option[X === Y] =
    if(x eq y) Some(Leibniz.force[Nothing, Any, X, Y])
    else None

  trait Visitor[:=>:[_, _], **[_, _], T, H[_, _], A, R] {
    def apply[X](a: App[:=>:, **, T, H, X, A]): R
    def apply   (a: Obj[:=>:, **, T, H, A])   : R
    def apply   (a: Var[:=>:, **, T, H, A])   : R
  }


  // object A represented as an arrow from terminal object to A
  def obj[:=>:[_, _], **[_, _], T, H[_, _], A](f: CodeTerm[:=>:, **, T, H, T, A]): DataTerm[:=>:, **, T, H, A] = Obj(f)

  // arrow application
  def app[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: CodeTerm[:=>:, **, T, H, A, B], a: DataTerm[:=>:, **, T, H, A]): DataTerm[:=>:, **, T, H, B] =
    f.app(a)

  def app[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]], a: DataTerm[:=>:, **, T, H, A]): DataTerm[:=>:, **, T, H, B] =
    app(code(f), a)
}


/** Hybrid representation containing both
  *  - operations of a Cartesian closed category; and
  *  - free variables.
  *
  * Used as an intermediate representation in the translation
  * from lambda expressions to Cartesian closed operations.
  *
  * Free variables are eliminated via the [[#unapply]] method.
  */
final class CodeTerm[:=>:[_, _], **[_, _], T, H[_, _], A, B](
  val unwrap: FreeCCC[λ[(α, β) => Either[α :=>: β, DataTerm.Var[:=>:, **, T, H, β]]], **, T, H, A, B]
) {
  import CodeTerm._
  import DataTerm._

  type $[X]    =     DataTerm[:=>:, **, T, H, X]
  type φ[X, Y] =     CodeTerm[:=>:, **, T, H, X, Y]
  type Var[X]  = DataTerm.Var[:=>:, **, T, H, X]

  type :≡>:[X, Y] = Either[X :=>: Y, Var[Y]]
  type Repr[X, Y] = FreeCCC[:≡>:, **, T, H, X, Y]

//  type Arr[X, Y]        =      FreeCCC.Arr[:=>:, **, T, H, X, Y]
  type Id[X]            =       FreeCCC.Id[:≡>:, **, T, H, X]
  type Fst[X, Y]        =      FreeCCC.Fst[:≡>:, **, T, H, X, Y]
  type Snd[X, Y]        =      FreeCCC.Snd[:≡>:, **, T, H, X, Y]
  type Prod[X, Y, Z]    =     FreeCCC.Prod[:≡>:, **, T, H, X, Y, Z]
  type Terminal[X]      = FreeCCC.Terminal[:≡>:, **, T, H, X]
  type Compose[X, Y, Z] =  FreeCCC.Compose[:≡>:, **, T, H, X, Y, Z]
  type Curry[X, Y, Z]   =    FreeCCC.Curry[:≡>:, **, T, H, X, Y, Z]
  type Uncurry[X, Y, Z] =  FreeCCC.Uncurry[:≡>:, **, T, H, X, Y, Z]

  type Visitor[R]       =  CodeTerm.Visitor[:=>:, **, T, H, A, B, R]


  def visit[R](v: Visitor[R]): R = unwrap.visit(v)

  def const[Z]: φ[Z, H[A, B]] = wrap(unwrap.const[Z]: Repr[Z, H[A, B]])

  def data: DataTerm[:=>:, **, T, H, H[A, B]] =
    obj(this.const[T])

  def castA[X](implicit ev: A === X): CodeTerm[:=>:, **, T, H, X, B] =
    ev.subst[CodeTerm[:=>:, **, T, H, ?, B]](this)

  def castB[Y](implicit ev: B === Y): CodeTerm[:=>:, **, T, H, A, Y] =
    ev.subst[CodeTerm[:=>:, **, T, H, A, ?]](this)

  def prod[C](that: φ[A, C]): φ[A, B ** C] =
    wrap(this.unwrap prod that.unwrap)

  def compose[Z](that: φ[Z, A]): φ[Z, B] =
    wrap(this.unwrap compose that.unwrap)

  def curry[X, Y](implicit ev: A === (X ** Y)): φ[X, H[Y, B]] =
    wrap(this.unwrap.curry)

  def uncurry[X, Y](implicit ev: B === H[X, Y]): φ[A**X, Y] =
    wrap(this.unwrap.uncurry)

  def size: Int = unwrap.size

  def containsVar[V](v: Var[V]): Boolean =
    unwrap.containsVar(v)

  /** Eliminates the free variable `v` from this term. */
  def unapply[V](v: Var[V]): φ[V, H[A, B]] =
    wrap(unwrap.unapply(v))

  /** Compiles this function term into the underlying Cartesian closed category.
    *
    * All free variables must be eliminated before compilation (see [[#unapply]]).
    * Otherwise, it is a runtime error.
    */
  def compile(implicit C: CCC.Aux[:=>:, **, T, H]): A :=>: B =
    unwrap.foldMap(Λ[α, β](_ match {
      case  Left(f) => f
      case Right(v) => sys.error("Cannot compile variable.")
    }): :≡>: ~~> :=>:)

  def app(a: $[A]): $[B] =
    a.visit(new DataTerm.Visitor[:=>:, **, T, H, A, DataTerm[:=>:, **, T, H, B]] {
      def apply[X](a: App[:=>:, **, T, H, X, A]) =
        App((CodeTerm.this compose CodeTerm.code(a.f)).data, a.a)

      def apply(a: Obj[:=>:, **, T, H, A]) =
        obj(CodeTerm.this compose a.f)

      def apply(a: Var[A]) =
        App(CodeTerm.this.data, a)
    })


  /* Syntax */

  def **[C]   (c: $[C]   ): $[H[A, B] ** C]       = this.data ** c
  def **[C, D](f: φ[C, D]): $[H[A, B] ** H[C, D]] = this.data ** f.data


  /** Enrich the free representation with some operations. */
  private implicit class ReprOps[P, Q](f: Repr[P, Q]) {

    def containsVar[V](v: Var[V]): Boolean = f.visit(new CodeTerm.Visitor[:=>:, **, T, H, P, Q, Boolean] {
      def apply[Y, Z](a:    Curry[P, Y, Z])(implicit ev:  H[Y, Z] === Q) = a.f.containsVar(v)
      def apply[X, Y](a:  Uncurry[X, Y, Q])(implicit ev: (X ** Y) === P) = a.f.containsVar(v)
      def apply[Y]   (a:  Compose[P, Y, Q])                              = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y, Z](a:     Prod[P, Y, Z])(implicit ev:   (Y**Z) === Q) = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y]   (a:      Fst[Q, Y])   (implicit ev:   (Q**Y) === P) = false
      def apply[X]   (a:      Snd[X, Q])   (implicit ev:   (X**Q) === P) = false
      def apply      (a:       Id[P])      (implicit ev:        P === Q) = false
      def apply      (a: Terminal[P])      (implicit ev:        T === Q) = false
      def apply      (a: P :=>: Q)                                       = false
      def apply      (b: Var[Q])                                         = b.containsVar(v)
    })

    def unapply[V](v: Var[V]): Repr[V, H[P, Q]] = f.visit(new CodeTerm.Visitor[:=>:, **, T, H, P, Q, Repr[V, H[P, Q]]] {

      def apply   (a:       P :=>: Q)                            = primitive(a).unwrap.const[V]
      def apply   (a:       Id[P]   )(implicit ev:      P === Q) = a.castB[Q].const[V]
      def apply[Y](a:      Fst[Q, Y])(implicit ev: (Q**Y) === P) = a.castA[P].const[V]
      def apply[X](a:      Snd[X, Q])(implicit ev: (X**Q) === P) = a.castA[P].const[V]
      def apply   (a: Terminal[P]   )(implicit ev:      T === Q) = a.castB[Q].const[V]

      def apply[X, Y](a: Uncurry[X, Y, Q])(implicit ev: (X ** Y) === P) = (
        if(a.containsVar(v)) curry(andThen(assocL[V, X, Y], uncurry(uncurry(a.f.unapply(v)))))
        else a.const[V]
      ).castB(ev.lift[H[?, Q]])

      def apply[Y, Z](a: Curry[P, Y, Z])(implicit ev: H[Y, Z] === Q) = (
        if(a.containsVar(v)) curry(curry(andThen(assocR[V, P, Y], uncurry(a.f.unapply(v)))))
        else                 a.const[V]
      ).castB(ev.lift[H[P, ?]])

      def apply[Y, Z](a: Prod[P, Y, Z])(implicit ev: (Y**Z) === Q) = (
        if(a.containsVar(v)) curry(prod(uncurry(a.f.unapply(v)), uncurry(a.g.unapply(v))))
        else                 a.const[V]
      ).castB(ev.lift[H[P, ?]])

      def apply[Y](a: Compose[P, Y, Q]) =
        if(a.containsVar(v)) {
          val f: Repr[V**P, H[V, Q]] = compose(swap(a.f.unapply(v)), uncurry(a.g.unapply(v)))
          val g: Repr[(V**V)**P, Q] = compose(flip(uncurry(f)), assocR[V, V, P])
          val diag1: Repr[V**P, (V**V)**P] = parallel(diag[V], id)
          curry(compose(g, diag1))
        } else {
          a.const[V]
        }

      def apply(q: Var[Q]) =
        sameVar(q, v) match {
          case Some(ev) => constA[Q, P].castA[V](ev)
          case None     => constVar[P, Q](q).const[V]
        }
    })
  }
}

object CodeTerm {
  import DataTerm._
  import FreeCCC._

  def wrap[:=>:[_, _], **[_, _], T, H[_, _], A, B](
    f: FreeCCC[λ[(α, β) => Either[α :=>: β, DataTerm.Var[:=>:, **, T, H, β]]], **, T, H, A, B]
  ): CodeTerm[:=>:, **, T, H, A, B] =
    new CodeTerm(f)

  // wrap primitive arrow
  def primitive[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: A :=>: B): CodeTerm[:=>:, **, T, H, A, B] = {
    type :≡>:[X, Y] = Either[X :=>: Y, Var[:=>:, **, T, H, Y]]
    wrap(FreeCCC.lift[:≡>:, **, T, H, A, B](Left(f)))
  }

  // wrap a variable as a constant function
  def constVar[:=>:[_, _], **[_, _], T, H[_, _], Z, A](a: Var[:=>:, **, T, H, A]): CodeTerm[:=>:, **, T, H, Z, A] = {
    type :≡>:[X, Y] = Either[X :=>: Y, Var[:=>:, **, T, H, Y]]
    wrap(FreeCCC.lift[:≡>:, **, T, H, Z, A](Right(a)))
  }

  // treat function object as a function
  def code[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, H[A, B]]): CodeTerm[:=>:, **, T, H, A, B] = {
    type :≡>:[X, Y] = Either[X :=>: Y, Var[:=>:, **, T, H, Y]]
    wrap(getConst[:≡>:, **, T, H, A, B](f.code.unwrap))
  }

  /** Internalize a Scala funciton as a `:=>:` arrow. */
  def internalize[:=>:[_, _], **[_, _], T, H[_, _], A, B](f: DataTerm[:=>:, **, T, H, A] => DataTerm[:=>:, **, T, H, B]): CodeTerm[:=>:, **, T, H, A, B] = {
    val v = new Var[:=>:, **, T, H, A]
    f(v).unapply(v)
  }

  trait Visitor[:=>:[_, _], **[_, _], T, H[_, _], A, B, R]
  extends FreeCCC.Visitor[λ[(α, β) => Either[α :=>: β, Var[:=>:, **, T, H, β]]], **, T, H, A, B, R] {

    def apply(f: A :=>: B): R
    def apply(b: Var[B]): R

    override def apply(f: Lift[A, B]): R =
      f.f match {
        case  Left(f) => apply(f)
        case Right(b) => apply(b)
      }

    // Convenience type aliases and methods

    type Var[X] = DataTerm.Var[:=>:, **, T, H, X]
    type φ[X, Y] = CodeTerm[:=>:, **, T, H, X, Y]
    type :≡>:[X, Y] = Either[X :=>: Y, Var[Y]]
    type Φ[X, Y] = FreeCCC[:≡>:, **, T, H, X, Y]

    def constVar[Z, X](x: Var[X]): Φ[Z, X] = FreeCCC.lift[:≡>:, **, T, H, Z, X](Right(x))

    def id[X]: Φ[X, X]                                      = FreeCCC.id[:≡>:, **, T, H, X]
    def compose[X, Y, Z](f: Φ[Y, Z], g: Φ[X, Y]): Φ[X, Z]   = FreeCCC.compose[:≡>:, **, T, H, X, Y, Z](f, g)
    def fst[X, Y]: Φ[(X**Y), X]                             = FreeCCC.fst
    def snd[X, Y]: Φ[(X**Y), Y]                             = FreeCCC.snd
    def prod[X, Y, Z](f: Φ[X, Y], g: Φ[X, Z]): Φ[X, (Y**Z)] = FreeCCC.prod[:≡>:, **, T, H, X, Y, Z](f, g)
    def terminal[X]: Φ[X, T]                                = FreeCCC.terminal
    def curry[X, Y, Z](f: Φ[(X**Y), Z]): Φ[X, H[Y, Z]]      = FreeCCC.curry[:≡>:, **, T, H, X, Y, Z](f)
    def uncurry[X, Y, Z](f: Φ[X, H[Y, Z]]): Φ[(X**Y), Z]    = FreeCCC.uncurry[:≡>:, **, T, H, X, Y, Z](f)

    def constA[X, Y]: Φ[X, H[Y, X]]                       = FreeCCC.constA
    def getConst[X, Y](f: Φ[T, H[X, Y]]): Φ[X, Y]         = FreeCCC.getConst[:≡>:, **, T, H, X, Y](f)
    def andThen[X, Y, Z](f: Φ[X, Y], g: Φ[Y, Z]): Φ[X, Z] = FreeCCC.andThen[:≡>:, **, T, H, X, Y, Z](f, g)
    def flip[X, Y, Z](f: Φ[(X**Y), Z]): Φ[(Y**X), Z]      = FreeCCC.flip[:≡>:, **, T, H, X, Y, Z](f)
    def swap[X, Y, Z](f: Φ[X, H[Y, Z]]): Φ[Y, H[X, Z]]    = FreeCCC.swap[:≡>:, **, T, H, X, Y, Z](f)
    def eval[X, Y]: Φ[H[X, Y] ** X, Y]                    = FreeCCC.eval
    def assocR[X, Y, Z]: Φ[((X**Y)**Z), (X**(Y**Z))]      = FreeCCC.assocR
    def assocL[X, Y, Z]: Φ[(X**(Y**Z)), ((X**Y)**Z)]      = FreeCCC.assocL
    def diag[X]: Φ[X, (X ** X)]                           = FreeCCC.diag
    def parallel[X1, X2, Y1, Y2](f: Φ[X1, Y1], g: Φ[X2, Y2]): Φ[(X1**X2), (Y1**Y2)] =
      FreeCCC.parallel[:≡>:, **, T, H, X1, X2, Y1, Y2](f, g)
  }
}
