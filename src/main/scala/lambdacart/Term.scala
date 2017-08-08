package lambdacart

import lambdacart.util.{~~>, LeibnizOps}
import scalaz.Leibniz
import scalaz.Leibniz.===

trait Terms { self: Dsl =>
  import CodeTerm._
  import DataTerm._

  // ⨪ is Unicode U+2A2A
  type :⨪>:[X, Y] = Either[X :=>: Y, Var[Y]]

sealed trait DataTerm[A] {

  type Visitor[R] = DataTerm.Visitor[A, R]

  def visit[R](v: Visitor[R]): R


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

  def code: φ[Unit, A] =
    visit(new Visitor[φ[Unit, A]] {
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
  def **[B, C](f: φ[B, C]): $[A ** Hom[B, C]] = this ** f.data
  def get_1[X, Y](implicit ev: A === (X ** Y)): $[X] = app(fst[X, Y], ev.subst[$](this))
  def get_2[X, Y](implicit ev: A === (X ** Y)): $[Y] = app(snd[X, Y], ev.subst[$](this))
}

object DataTerm {

  case class Obj[A](f: CodeTerm[Unit, A]) extends DataTerm[A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  case class App[A, B](f: DataTerm[Hom[A, B]], a: DataTerm.Var[A]) extends DataTerm[B] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  class Var[A] private[lambdacart]() extends DataTerm[A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  def sameVar[X, Y](x: Var[X], y: Var[Y]): Option[X === Y] =
    if(x eq y) Some(Leibniz.force[Nothing, Any, X, Y])
    else None

  trait Visitor[A, R] {
    def apply[X](a: App[X, A]): R
    def apply   (a: Obj[A])   : R
    def apply   (a: Var[A])   : R
  }


  // object A represented as an arrow from terminal object to A
  def obj[A](f: CodeTerm[Unit, A]): DataTerm[A] = Obj(f)

  // arrow application
  def app[A, B](f: CodeTerm[A, B], a: DataTerm[A]): DataTerm[B] =
    f.app(a)

  def app[A, B](f: DataTerm[Hom[A, B]], a: DataTerm[A]): DataTerm[B] =
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
final class CodeTerm[A, B](val unwrap: FreeCCC[:⨪>:, **, Unit, Hom, A, B]) {

  type Repr[X, Y] = FreeCCC[:⨪>:, **, Unit, Hom, X, Y]

  type Visitor[R]       =  CodeTerm.Visitor[A, B, R]


  def visit[R](v: Visitor[R]): R = unwrap.visit(v)

  def const[Z]: φ[Z, Hom[A, B]] = wrap(unwrap.const[Z]: Repr[Z, Hom[A, B]])

  def data: DataTerm[Hom[A, B]] =
    DataTerm.obj(this.const[Unit])

  def castA[X](implicit ev: A === X): CodeTerm[X, B] =
    ev.subst[CodeTerm[?, B]](this)

  def castB[Y](implicit ev: B === Y): CodeTerm[A, Y] =
    ev.subst[CodeTerm[A, ?]](this)

  def prod[C](that: φ[A, C]): φ[A, B ** C] =
    wrap(this.unwrap prod that.unwrap)

  def compose[Z](that: φ[Z, A]): φ[Z, B] =
    wrap(this.unwrap compose that.unwrap)

  def curry[X, Y](implicit ev: A === (X ** Y)): φ[X, Hom[Y, B]] =
    wrap(this.unwrap.curry)

  def uncurry[X, Y](implicit ev: B === Hom[X, Y]): φ[A**X, Y] =
    wrap(this.unwrap.uncurry)

  def size: Int = unwrap.size

  def containsVar[V](v: Var[V]): Boolean =
    unwrap.containsVar(v)

  /** Eliminates the free variable `v` from this term. */
  def unapply[V](v: Var[V]): φ[V, Hom[A, B]] =
    wrap(unwrap.unapply(v))

  /** Compiles this function term into the underlying Cartesian closed category.
    *
    * All free variables must be eliminated before compilation (see [[#unapply]]).
    * Otherwise, it is a runtime error.
    */
  def compile: A :=>: B =
    unwrap.foldMap(Λ[α, β](_ match {
      case  Left(f) => f
      case Right(v) => sys.error("Cannot compile variable.")
    }): :⨪>: ~~> :=>:)

  def app(a: $[A]): $[B] =
    a.visit(new DataTerm.Visitor[A, DataTerm[B]] {
      def apply[X](a: App[X, A]) =
        App((CodeTerm.this compose CodeTerm.code(a.f)).data, a.a)

      def apply(a: Obj[A]) =
        DataTerm.obj(CodeTerm.this compose a.f)

      def apply(a: Var[A]) =
        App(CodeTerm.this.data, a)
    })


  /* Syntax */

  def **[C]   (c: $[C]   ): $[Hom[A, B] ** C]       = this.data ** c
  def **[C, D](f: φ[C, D]): $[Hom[A, B] ** Hom[C, D]] = this.data ** f.data


  /** Enrich the free representation with some operations. */
  private implicit class ReprOps[P, Q](f: Repr[P, Q]) {

    def containsVar[V](v: Var[V]): Boolean = f.visit(new CodeTerm.Visitor[P, Q, Boolean] {
      def apply[Y, Z](a:    Curry[P, Y, Z])(implicit ev: Hom[Y, Z] === Q) = a.f.containsVar(v)
      def apply[X, Y](a:  Uncurry[X, Y, Q])(implicit ev: (X ** Y) === P)  = a.f.containsVar(v)
      def apply[Y]   (a:  Compose[P, Y, Q])                               = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y, Z](a:     Prod[P, Y, Z])(implicit ev:   (Y**Z) === Q)  = a.f.containsVar(v) || a.g.containsVar(v)
      def apply[Y]   (a:      Fst[Q, Y])   (implicit ev:   (Q**Y) === P)  = false
      def apply[X]   (a:      Snd[X, Q])   (implicit ev:   (X**Q) === P)  = false
      def apply      (a:       Id[P])      (implicit ev:        P === Q)  = false
      def apply      (a: Terminal[P])      (implicit ev:     Unit === Q)  = false
      def apply      (a: P :=>: Q)                                        = false
      def apply      (b: Var[Q])                                          = b.containsVar(v)
    })

    def unapply[V](v: Var[V]): Repr[V, Hom[P, Q]] = f.visit(new CodeTerm.Visitor[P, Q, Repr[V, Hom[P, Q]]] {

      def apply   (a:       P :=>: Q)                            = primitive(a).unwrap.const[V]
      def apply   (a:       Id[P]   )(implicit ev:      P === Q) = a.castB[Q].const[V]
      def apply[Y](a:      Fst[Q, Y])(implicit ev: (Q**Y) === P) = a.castA[P].const[V]
      def apply[X](a:      Snd[X, Q])(implicit ev: (X**Q) === P) = a.castA[P].const[V]
      def apply   (a: Terminal[P]   )(implicit ev:   Unit === Q) = a.castB[Q].const[V]

      def apply[X, Y](a: Uncurry[X, Y, Q])(implicit ev: (X ** Y) === P) = (
        if(a.containsVar(v)) curry(andThen(assocL[V, X, Y], uncurry(uncurry(a.f.unapply(v)))))
        else a.const[V]
      ).castB(ev.lift[Hom[?, Q]])

      def apply[Y, Z](a: Curry[P, Y, Z])(implicit ev: Hom[Y, Z] === Q) = (
        if(a.containsVar(v)) curry(curry(andThen(assocR[V, P, Y], uncurry(a.f.unapply(v)))))
        else                 a.const[V]
      ).castB(ev.lift[Hom[P, ?]])

      def apply[Y, Z](a: Prod[P, Y, Z])(implicit ev: (Y**Z) === Q) = (
        if(a.containsVar(v)) curry(prod(uncurry(a.f.unapply(v)), uncurry(a.g.unapply(v))))
        else                 a.const[V]
      ).castB(ev.lift[Hom[P, ?]])

      def apply[Y](a: Compose[P, Y, Q]) =
        if(a.containsVar(v)) {
          val f: Repr[V**P, Hom[V, Q]] = compose(swap(a.f.unapply(v)), uncurry(a.g.unapply(v)))
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

  def wrap[A, B](f: FreeCCC[:⨪>:, **, Unit, Hom, A, B]): CodeTerm[A, B] =
    new CodeTerm(f)

  // wrap primitive arrow
  def primitive[A, B](f: A :=>: B): CodeTerm[A, B] =
    wrap(FreeCCC.lift[:⨪>:, **, Unit, Hom, A, B](Left(f)))

  // wrap a variable as a constant function
  def constVar[Z, A](a: Var[A]): CodeTerm[Z, A] =
    wrap(FreeCCC.lift[:⨪>:, **, Unit, Hom, Z, A](Right(a)))

  // Cartesian closed operations on code terms (delegated to FreeCCC)
  def id[X]: φ[X, X]                                      = wrap(FreeCCC.id)
  def compose[X, Y, Z](f: φ[Y, Z], g: φ[X, Y]): φ[X, Z]   = wrap(FreeCCC.compose(f.unwrap, g.unwrap))
  def fst[X, Y]: φ[(X**Y), X]                             = wrap(FreeCCC.fst)
  def snd[X, Y]: φ[(X**Y), Y]                             = wrap(FreeCCC.snd)
  def prod[X, Y, Z](f: φ[X, Y], g: φ[X, Z]): φ[X, (Y**Z)] = wrap(FreeCCC.prod(f.unwrap, g.unwrap))
  def terminal[X]: φ[X, Unit]                             = wrap(FreeCCC.terminal)
  def curry[X, Y, Z](f: φ[(X**Y), Z]): φ[X, Hom[Y, Z]]    = wrap(FreeCCC.curry(f.unwrap))
  def uncurry[X, Y, Z](f: φ[X, Hom[Y, Z]]): φ[(X**Y), Z]  = wrap(FreeCCC.uncurry(f.unwrap))

  def constA[X, Y]: φ[X, Hom[Y, X]]                       = wrap(FreeCCC.constA)
  def getConst[X, Y](f: φ[Unit, Hom[X, Y]]): φ[X, Y]      = wrap(FreeCCC.getConst(f.unwrap))
  def andThen[X, Y, Z](f: φ[X, Y], g: φ[Y, Z]): φ[X, Z]   = wrap(FreeCCC.andThen(f.unwrap, g.unwrap))
  def flip[X, Y, Z](f: φ[(X**Y), Z]): φ[(Y**X), Z]        = wrap(FreeCCC.flip(f.unwrap))
  def swap[X, Y, Z](f: φ[X, Hom[Y, Z]]): φ[Y, Hom[X, Z]]  = wrap(FreeCCC.swap(f.unwrap))
  def eval[X, Y]: φ[Hom[X, Y] ** X, Y]                    = wrap(FreeCCC.eval)
  def assocR[X, Y, Z]: φ[((X**Y)**Z), (X**(Y**Z))]        = wrap(FreeCCC.assocR)
  def assocL[X, Y, Z]: φ[(X**(Y**Z)), ((X**Y)**Z)]        = wrap(FreeCCC.assocL)
  def diag[X]: φ[X, (X ** X)]                             = wrap(FreeCCC.diag)
  def parallel[X1, X2, Y1, Y2](f: φ[X1, Y1], g: φ[X2, Y2]): φ[(X1**X2), (Y1**Y2)] =
    wrap(FreeCCC.parallel(f.unwrap, g.unwrap))

  // treat function object as a function
  def code[A, B](f: DataTerm[Hom[A, B]]): CodeTerm[A, B] =
    getConst[A, B](f.code)

  /** Internalize a Scala funciton as an arrow. */
  def internalize[A, B](f: DataTerm[A] => DataTerm[B]): CodeTerm[A, B] = {
    val v = new Var[A]
    f(v).unapply(v)
  }

  trait Visitor[A, B, R] extends FreeCCC.Visitor[:⨪>:, **, Unit, Hom, A, B, R] {

    def apply(f: A :=>: B): R
    def apply(b: Var[B]): R

    override def apply(f: Lift[A, B]): R =
      f.f match {
        case  Left(f) => apply(f)
        case Right(b) => apply(b)
      }

    // Convenience type aliases and methods

    type Φ[X, Y] = FreeCCC[:⨪>:, **, Unit, Hom, X, Y]

    def constVar[Z, X](x: Var[X]): Φ[Z, X] = FreeCCC.lift[:⨪>:, **, Unit, Hom, Z, X](Right(x))

    def id[X]: Φ[X, X]                                      = FreeCCC.id
    def compose[X, Y, Z](f: Φ[Y, Z], g: Φ[X, Y]): Φ[X, Z]   = FreeCCC.compose(f, g)
    def fst[X, Y]: Φ[(X**Y), X]                             = FreeCCC.fst
    def snd[X, Y]: Φ[(X**Y), Y]                             = FreeCCC.snd
    def prod[X, Y, Z](f: Φ[X, Y], g: Φ[X, Z]): Φ[X, (Y**Z)] = FreeCCC.prod(f, g)
    def terminal[X]: Φ[X, Unit]                             = FreeCCC.terminal
    def curry[X, Y, Z](f: Φ[(X**Y), Z]): Φ[X, Hom[Y, Z]]    = FreeCCC.curry(f)
    def uncurry[X, Y, Z](f: Φ[X, Hom[Y, Z]]): Φ[(X**Y), Z]  = FreeCCC.uncurry(f)

    def constA[X, Y]: Φ[X, Hom[Y, X]]                       = FreeCCC.constA
    def getConst[X, Y](f: Φ[Unit, Hom[X, Y]]): Φ[X, Y]      = FreeCCC.getConst(f)
    def andThen[X, Y, Z](f: Φ[X, Y], g: Φ[Y, Z]): Φ[X, Z]   = FreeCCC.andThen(f, g)
    def flip[X, Y, Z](f: Φ[(X**Y), Z]): Φ[(Y**X), Z]        = FreeCCC.flip(f)
    def swap[X, Y, Z](f: Φ[X, Hom[Y, Z]]): Φ[Y, Hom[X, Z]]  = FreeCCC.swap(f)
    def eval[X, Y]: Φ[Hom[X, Y] ** X, Y]                    = FreeCCC.eval
    def assocR[X, Y, Z]: Φ[((X**Y)**Z), (X**(Y**Z))]        = FreeCCC.assocR
    def assocL[X, Y, Z]: Φ[(X**(Y**Z)), ((X**Y)**Z)]        = FreeCCC.assocL
    def diag[X]: Φ[X, (X ** X)]                             = FreeCCC.diag
    def parallel[X1, X2, Y1, Y2](f: Φ[X1, Y1], g: Φ[X2, Y2]): Φ[(X1**X2), (Y1**Y2)] =
      FreeCCC.parallel(f, g)
  }
}

}
