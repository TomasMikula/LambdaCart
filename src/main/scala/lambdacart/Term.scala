package lambdacart

import lambdacart.util.{~~>, LeibnizOps}
import lambdacart.util.typealigned.{ACons, AList, ANil}
import scalaz.Leibniz
import scalaz.Leibniz.===

trait Terms { self: Dsl =>
  import CodeTerm._
  import DataTerm._

  // ⨪ is Unicode U+2A2A
  type :⨪>:[X, Y] = Either[X :->: Y, Var[Y]]

sealed trait DataTerm[A] {

  type Visitor[R] = DataTerm.Visitor[A, R]

  def visit[R](v: Visitor[R]): R


  def size: Int = visit(new Visitor[Int] {
    def apply(a: Var[A]): Int = 1
    def apply(a: Obj[A]): Int = 1 + a.f.size
  })

  def containsVar[V](v: Var[V]): Boolean = visit(new Visitor[Boolean] {
    def apply(a: Var[A]) = a == v
    def apply(a: Obj[A]) = a.f.containsVar(v)
  })

  /** Returns `f` such that `f(x) = this` and `x` does not occur in `f`.
    */
  def unapply[V](v: Var[V]): φ[V, A] = visit(new Visitor[φ[V, A]] {
    def apply(a: Obj[A]) =
      if(a.f.containsVar(v)) compose(uncurry(a.f.unapply(v)), prod(id, terminal))
      else compose(a.f, terminal)

    def apply(a: Var[A]) =
      sameVar(a, v) match {
        case Some(ev) => id[A].castA[V](ev)
        case None     => constVar(a)
      }
  })

  def code: φ[Unit, A] =
    visit(new Visitor[φ[Unit, A]] {
      def apply(a: Obj[A]) = a.f
      def apply(a: Var[A]) = constVar(a)
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

  class Var[A] private[lambdacart]() extends DataTerm[A] {
    def visit[R](visitor: Visitor[R]): R = visitor(this)
  }

  def sameVar[X, Y](x: Var[X], y: Var[Y]): Option[X === Y] =
    if(x eq y) Some(Leibniz.force[Nothing, Any, X, Y])
    else None

  trait Visitor[A, R] {
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

  type Visitor[R] = CodeTerm.Visitor[A, B, R]

  def visit[R](v: Visitor[R]): R =
    unwrap.visit(v)

  def const[Z]: φ[Z, Hom[A, B]] =
    wrap(unwrap.const[Z])

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

  def andThen[C](that: φ[B, C]): φ[A, C] =
    that compose this

  def size: Int = unwrap.size

  def containsVar[V](v: Var[V]): Boolean = visit(new Visitor[Boolean] {
    def caseCurry[Y, Z]  (f: φ[A ** Y, Z]     )(implicit ev: Hom[Y,Z] === B) = f.containsVar(v)
    def caseConst[X, Y]  (f: φ[X, Y]          )(implicit ev: Hom[X,Y] === B) = f.containsVar(v)
    def caseUncurry[X, Y](f: φ[X, Hom[Y, B]]  )(implicit ev: A === (X ** Y)) = f.containsVar(v)
    def caseCompose[Y]   (f: φ[Y,B], g: φ[A,Y])                              = f.containsVar(v) || g.containsVar(v)
    def caseProd[Y, Z]   (f: φ[A,Y], g: φ[A,Z])(implicit ev:   (Y**Z) === B) = f.containsVar(v) || g.containsVar(v)
    def caseFst[Y]                             (implicit ev:   A === (B**Y)) = false
    def caseSnd[X]                             (implicit ev:   A === (X**B)) = false
    def caseId                                 (implicit ev:        A === B) = false
    def caseTerminal                           (implicit ev:     Unit === B) = false
    def casePrimitive    (f: A :->: B)                                       = false
    def caseConstVar     (q: Var[B])                                         = q.containsVar(v)
  })

  /** Eliminates the free variable `v` from this term. */
  def unapply[V](v: Var[V]): φ[V, Hom[A, B]] = visit(new Visitor[φ[V, Hom[A, B]]] {

    def casePrimitive(f: A :->: B) = primitive(f).const[V]

    def caseId      (implicit ev:      A === B) = const[V]
    def caseFst[Y]  (implicit ev: A === (B**Y)) = const[V]
    def caseSnd[X]  (implicit ev: A === (X**B)) = const[V]
    def caseTerminal(implicit ev:   Unit === B) = const[V]

    def caseUncurry[X, Y](f: φ[X, Hom[Y, B]])(implicit ev: A === (X ** Y)) =
      if(f.containsVar(v))
        curry(assocL[V, X, Y] andThen uncurry(uncurry(f.unapply(v)))).castB(ev.flip.lift[Hom[?, B]])
      else const[V]

    def caseCurry[Y, Z](f: φ[A ** Y, Z])(implicit ev: Hom[Y, Z] === B) =
      if(f.containsVar(v)) curry(curry(assocR[V, A, Y] andThen uncurry(f.unapply(v)))).castB(ev.lift[Hom[A, ?]])
      else                 const[V]

    def caseConst[X, Y](f: φ[X, Y])(implicit ev: Hom[X,Y] === B) =
      if(f.containsVar(v)) curry(fst[V, A] andThen f.unapply(v)).castB(ev.lift[Hom[A, ?]])
      else                 const[V]

    def caseProd[Y, Z](f: φ[A, Y], g: φ[A, Z])(implicit ev: (Y**Z) === B) =
      if(f.containsVar(v) && g.containsVar(v)) curry((uncurry(f.unapply(v)) prod uncurry(g.unapply(v))).castB)
      else if (f.containsVar(v))               curry((uncurry(f.unapply(v)) prod g.compose(snd)).castB)
      else if (g.containsVar(v))               curry((f.compose(snd[V, A]) prod uncurry(g.unapply(v))).castB)
      else                                     const[V]

    def caseCompose[Y](f: φ[Y, B], g: φ[A, Y]) =
      if(f.containsVar(v) && g.containsVar(v)) {
        val f1: φ[V, Hom[Y, B]] = f.unapply(v)
        val g1: φ[V, Hom[A, Y]] = g.unapply(v)
        curry(((f1 compose fst[V, A]) prod uncurry(g1)) andThen eval)
      } else if(f.containsVar(v)) {
        curry(parallel(f.unapply(v), g) andThen eval)
      } else if(g.containsVar(v)) {
        curry(uncurry(g.unapply(v)) andThen f)
      } else {
        const[V]
      }

    def caseConstVar(q: Var[B]) =
      sameVar(q, v) match {
        case Some(ev) => constA[B, A].castA[V](ev)
        case None     => curry(constVar[V**A, B](q))
      }
  })

  /** Compiles this function term into the underlying Cartesian closed category.
    *
    * All free variables must be eliminated before compilation (see [[#unapply]]).
    * Otherwise, it is a runtime error.
    */
  def compile: A :->: B =
    unwrap.foldMap(Λ[α, β](_ match {
      case  Left(f) => f
      case Right(v) => sys.error("Cannot compile variable.")
    }): :⨪>: ~~> :->:)

  def app(a: $[A]): $[B] =
    a.visit(new DataTerm.Visitor[A, DataTerm[B]] {
      def apply(a: Obj[A]) =
        DataTerm.obj(CodeTerm.this compose a.f)

      def apply(a: Var[A]) =
        Obj(constVar[Unit, A](a) andThen CodeTerm.this)
    })

  override def toString = unwrap.toString


  /* Syntax */

  def **[C]   (c: $[C]   ): $[Hom[A, B] ** C]         = this.data ** c
  def **[C, D](f: φ[C, D]): $[Hom[A, B] ** Hom[C, D]] = this.data ** f.data
}

object CodeTerm {
  import DataTerm._

  def wrap[A, B](f: FreeCCC[:⨪>:, **, Unit, Hom, A, B]): CodeTerm[A, B] =
    new CodeTerm(f)

  // wrap primitive arrow
  def primitive[A, B](f: A :->: B): CodeTerm[A, B] =
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
  def flipArg[X, Y, Z](f: φ[(X**Y), Z]): φ[(Y**X), Z]     = wrap(FreeCCC.flipArg(f.unwrap))
  def swapArgs[X,Y,Z](f: φ[X, Hom[Y,Z]]): φ[Y, Hom[X, Z]] = wrap(FreeCCC.swapArgs(f.unwrap))
  def eval[X, Y]: φ[Hom[X, Y] ** X, Y]                    = wrap(FreeCCC.eval)
  def assocR[X, Y, Z]: φ[((X**Y)**Z), (X**(Y**Z))]        = wrap(FreeCCC.assocR)
  def assocL[X, Y, Z]: φ[(X**(Y**Z)), ((X**Y)**Z)]        = wrap(FreeCCC.assocL)
  def diag[X]: φ[X, (X ** X)]                             = wrap(FreeCCC.diag)
  def parallel[X1, X2, Y1, Y2](f: φ[X1, Y1], g: φ[X2, Y2]): φ[(X1**X2), (Y1**Y2)] =
    wrap(FreeCCC.parallel(f.unwrap, g.unwrap))
  def sequence[U, V, W, X](f: φ[U, V], g: φ[V, W], h: φ[W, X]): φ[U, X] =
    wrap(FreeCCC.sequence(f.unwrap :: g.unwrap :: AList(h.unwrap)))
  def sequence[U, V, W, X, Y](f: φ[U, V], g: φ[V, W], h: φ[W, X], i: φ[X, Y]): φ[U, Y] =
    wrap(FreeCCC.sequence(f.unwrap :: g.unwrap :: h.unwrap :: AList(i.unwrap)))

  // treat function object as a function
  def code[A, B](f: DataTerm[Hom[A, B]]): CodeTerm[A, B] =
    getConst[A, B](f.code)

  /** Internalize a Scala funciton as an arrow. */
  def internalize[A, B](f: DataTerm[A] => DataTerm[B]): CodeTerm[A, B] = {
    val v = new Var[A]
    f(v).unapply(v)
  }

  def optimize[A, B](f: CodeTerm[A, B]): CodeTerm[A, B] =
    wrap(f.unwrap.optim)

  trait Visitor[A, B, R] extends FreeCCC.Visitor[:⨪>:, **, Unit, Hom, A, B, R] {
    import FreeCCC._

    def casePrimitive    (f: A :->: B)                                         : R
    def caseConstVar     (b: Var[B])                                           : R
    def caseCompose[X]   (f: φ[X, B], g: φ[A, X])                              : R
    def caseId                                   (implicit ev:        A === B) : R
    def caseProd   [X, Y](f: φ[A, X], g: φ[A, Y])(implicit ev: (X ** Y) === B) : R
    def caseFst    [X]                           (implicit ev: A === (B ** X)) : R
    def caseSnd    [X]                           (implicit ev: A === (X ** B)) : R
    def caseTerminal                             (implicit ev:     Unit === B) : R
    def caseCurry  [X, Y](f: φ[(A**X), Y])       (implicit ev: Hom[X,Y] === B) : R
    def caseUncurry[X, Y](f: φ[X, Hom[Y, B]])    (implicit ev: A === (X ** Y)) : R
    def caseConst  [X, Y](f: φ[X, Y])            (implicit ev: Hom[X,Y] === B) : R

    final override def apply(f: Sequence[A, B]) = f.fs.tail match {
      case ev @ ANil()   => f.fs.head.castB(ev.leibniz).visit(this)
      case ACons(f1, fs) => fs match {
        case ev @ ANil() => caseCompose(wrap(f1.castB(ev.leibniz)), wrap(f.fs.head))
        case fs          => caseCompose(wrap(Sequence(f1 +: fs)), wrap(f.fs.head))
      }
    }

    final override def apply      (f: Id[A]           )(implicit ev:        A === B) = caseId
    final override def apply[X]   (f: Fst[B, X]       )(implicit ev: A === (B ** X)) = caseFst
    final override def apply[X]   (f: Snd[X, B]       )(implicit ev: A === (X ** B)) = caseSnd
    final override def apply[X, Y](f: Prod[A, X, Y]   )(implicit ev: (X ** Y) === B) = caseProd(wrap(f.f), wrap(f.g))
    final override def apply      (f: Terminal[A]     )(implicit ev:     Unit === B) = caseTerminal
    final override def apply[X, Y](f: Curry[A, X, Y]  )(implicit ev: Hom[X,Y] === B) = caseCurry(wrap(f.f))
    final override def apply[X, Y](f: Uncurry[X, Y, B])(implicit ev: A === (X ** Y)) = caseUncurry(wrap(f.f))
    final override def apply[X, Y](f: Const[A, X, Y]  )(implicit ev: Hom[X,Y] === B) = caseConst(wrap(f.f))
    final override def apply      (f: Lift[A, B]) =
      f.f match {
        case  Left(f) => casePrimitive(f)
        case Right(b) => caseConstVar(b)
      }
  }
}

}
