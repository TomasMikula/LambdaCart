package lambdacart

trait Dsl extends Terms {
  import CodeTerm._
  import DataTerm._

  type :->:[A, B]
  type **[A, B]
  type Unit
  type Hom[A, B]
  type ->:[A, B] = Hom[A, B]

  type $[A]    = DataTerm[A]
  type φ[A, B] = CodeTerm[A, B]

  implicit def ccc: CCC.Aux[:->:, **, Unit, Hom]

  def φ[A, R](f: $[A] => $[R]): φ[A, R] =
    optimize(internalize(f))

  def φ[A, B, R](f: ($[A], $[B]) => $[R]): φ[A, B ->: R] =
    φ(a => φ[B, R](f(a, _)).data)

  def φ[A, B, C, R](f: ($[A], $[B], $[C]) => $[R]): φ[A, B ->: C ->: R] =
    φ((a, b) => φ[C, R](f(a, b, _)).data)

  def φ[A, B, C, D, R](f: ($[A], $[B], $[C], $[D]) => $[R]): φ[A, B ->: C ->: D ->: R] =
    φ((a, b, c) => φ[D, R](f(a, b, c, _)).data)

  def φ[A, B, C, D, E, R](f: ($[A], $[B], $[C], $[D], $[E]) => $[R]): φ[A, B ->: C ->: D ->: E ->: R] =
    φ((a, b, c, d) => φ[E, R](f(a, b, c, d, _)).data)

  def φ[A, B, C, D, E, F, R](f: ($[A], $[B], $[C], $[D], $[E], $[F]) => $[R]): φ[A, B ->: C ->: D ->: E ->: F ->: R] =
    φ((a, b, c, d, e) => φ[F, R](f(a, b, c, d, e, _)).data)

  def obj[A](f: Unit :->: A): $[A] =
    DataTerm.obj(primitive(f))

  def both[A, B, C](ab: $[A**B])(f: $[A] => $[B] => $[C]): $[C] = {
    val f1: φ[A, B ->: C] = φ((a, b) => f(a)(b))
    app(uncurry(f1), ab)
  }

  def apply[A, R](f: $[A] => $[R]): A :->: R =
    φ(f).compile
  def apply[A, B, R](f: ($[A], $[B]) => $[R]): A :->: B ->: R =
    φ(f).compile
  def apply[A, B, C, R](f: ($[A], $[B], $[C]) => $[R]): A :->: B ->: C ->: R =
    φ(f).compile
  def apply[A, B, C, D, R](f: ($[A], $[B], $[C], $[D]) => $[R]): A :->: B ->: C ->: D ->: R =
    φ(f).compile
  def apply[A, B, C, D, E, R](f: ($[A], $[B], $[C], $[D], $[E]) => $[R]): A :->: B ->: C ->: D ->: E ->: R =
    φ(f).compile
  def apply[A, B, C, D, E, F, R](f: ($[A], $[B], $[C], $[D], $[E], $[F]) => $[R]): A :->: B ->: C ->: D ->: E ->: F ->: R =
    φ(f).compile


  implicit class ArrowSyntax[A, B](f: A :->: B) {
    def apply(a: $[A]): $[B] = app(primitive[A, B](f), a)
  }
  implicit class CodeTermSyntax[A, B](f: φ[A, B]) {
    def apply(a: $[A]): $[B] = app(f, a)
  }
  implicit class HomSyntax[A, B](f: $[A ->: B]) {
    def apply(a: $[A]): $[B] = app(f, a)
  }
  implicit class HomArrowSyntax[A, B, C](f: (A ->: B) :->: C) {
    def apply(g: A :->: B): $[C] = this(primitive[A, B](g))
    def apply(g: φ[A, B]): $[C] = app(primitive[A ->: B, C](f), g.data)
    def apply(g: $[A] => $[B]): $[C] = apply(φ(g))
  }
  implicit class HomCodeTermSyntax[A, B, C](f: φ[A ->: B, C]) {
    def apply(g: A :->: B): $[C] = this(primitive[A, B](g))
    def apply(g: φ[A, B]): $[C] = app(f, g.data)
    def apply(g: $[A] => $[B]): $[C] = apply(φ(g))
  }
  implicit class HomHomSyntax[A, B, C](f: $[Hom[A ->: B, C]]) {
    def apply(g: A :->: B): $[C] = this(primitive[A, B](g))
    def apply(g: φ[A, B]): $[C] = app(f, g.data)
    def apply(g: $[A] => $[B]): $[C] = apply(φ(g))

    // This one should be covered by HomSyntax[A ->: B, C](f).apply(g),
    // but isn't ¯\_(ツ)_/¯
    def apply(g: $[A ->: B]): $[C] = app(f, g)
  }
  implicit class ProductSyntax[A, B](ab: $[A**B]) {
    def _1: $[A] = ab.get_1[A, B]
    def _2: $[B] = ab.get_2[A, B]
  }
}


/**** Extended DSL interface for DSLs that support additional common primitives.
  ** This doesn't have to be supported by all DSLs.
  **/
trait ExtendedDsl extends Dsl {
  // sum type
  type \/[A, B]
  def -\/[A, B]: A :->: (A\/B)
  def \/-[A, B]: B :->: (A\/B)
  def either[A, B, C]: (A \/ B) :->: (A ->: C) ->: (B ->: C) ->: C

  // some special sum types
  type Maybe[A] = Unit \/ A
  type Bool = Unit \/ Unit
  def maybe[A, B]: Maybe[A] :->: (Unit ->: B) ->: (A ->: B) ->: B = either[Unit, A, B]
  def ifThenElse[A]: Bool :->: (Unit ->: A) ->: (Unit ->: A) ->: A = either[Unit, Unit, A]

  // primitives for forming recursive types
  type Fix[F[_]]
  def fix[F[_]]: F[Fix[F]] :->: Fix[F]
  def unfix[F[_]]: Fix[F] :->: F[Fix[F]]

  // linked list (example of a recursive type)
  type Lst[A] = Fix[Unit \/ ?]
  // some list operations would be appropriate :-)


  // Primitive for recursive computations.
  //
  //                   initial value
  //                  /
  def doWhile[A, B]: A :->: (A ->: (A\/B)) ->: B
  //                             \
  //                              iteration (apply until it returns a B)
}
