package lambdacart

trait Dsl {
  import Term._

  type :=>:[A, B]
  type **[A, B]
  type Unit
  type Hom[A, B]

  type τ[A] = Term[:=>:, **, Unit, Hom, A]

  implicit def CC: CCC.AuxHI[:=>:, **, Unit]

  def τ[A, R](φ: τ[A] => τ[R]): τ[A :=>: R] =
    internalize(φ)

  def τ[A, B, R](φ: (τ[A], τ[B]) => τ[R]): τ[A :=>: B :=>: R] =
    τ[A, B :=>: R](a => τ(b => φ(a, b)))

  def τ[A, B, C, R](φ: (τ[A], τ[B], τ[C]) => τ[R]): τ[A :=>: B :=>: C :=>: R] =
    τ[A, B, C :=>: R]((a, b) => τ(c => φ(a, b, c)))

  def τ[A, B, C, D, R](φ: (τ[A], τ[B], τ[C], τ[D]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: R] =
    τ[A, B, C, D :=>: R]((a, b, c) => τ(d => φ(a, b, c, d)))

  def τ[A, B, C, D, E, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: E :=>: R] =
    τ[A, B, C, D, E :=>: R]((a, b, c, d) => τ(e => φ(a, b, c, d, e)))

  def τ[A, B, C, D, E, F, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E], τ[F]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: E :=>: F :=>: R] =
    τ[A, B, C, D, E, F :=>: R]((a, b, c, d, e) => τ(f => φ(a, b, c, d, e, f)))

  def Obj[A](f: Unit :=>: A): τ[A] =
    Term.obj(arr[:=>:, **, Unit, Hom, Unit, A](f))

  def both[A, B, C](ab: τ[A**B])(f: τ[A] => τ[B] => τ[C]): τ[C] = {
    val f1: τ[A :=>: B :=>: C] = τ((a: τ[A]) => τ(f(a)))
    app(uncurry(f1), ab)
  }

  def apply[A, R](φ: τ[A] => τ[R]): A :=>: R =
    parse(φ).compile
  def apply[A, B, R](φ: (τ[A], τ[B]) => τ[R]): A :=>: B :=>: R =
    parse(φ).compile
  def apply[A, B, C, R](φ: (τ[A], τ[B], τ[C]) => τ[R]): A :=>: B :=>: C :=>: R =
    parse(φ).compile
  def apply[A, B, C, D, R](φ: (τ[A], τ[B], τ[C], τ[D]) => τ[R]): A :=>: B :=>: C :=>: D :=>: R =
    parse(φ).compile
  def apply[A, B, C, D, E, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E]) => τ[R]): A :=>: B :=>: C :=>: D :=>: E :=>: R =
    parse(φ).compile
  def apply[A, B, C, D, E, F, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E], τ[F]) => τ[R]): A :=>: B :=>: C :=>: D :=>: E :=>: F :=>: R =
    parse(φ).compile

  def parse[A, R](φ: τ[A] => τ[R]): τ[A :=>: R] =
    τ(φ).elimAbs
  def parse[A, B, R](φ: (τ[A], τ[B]) => τ[R]): τ[A :=>: B :=>: R] =
    τ(φ).elimAbs
  def parse[A, B, C, R](φ: (τ[A], τ[B], τ[C]) => τ[R]): τ[A :=>: B :=>: C :=>: R] =
    τ(φ).elimAbs
  def parse[A, B, C, D, R](φ: (τ[A], τ[B], τ[C], τ[D]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: R] =
    τ(φ).elimAbs
  def parse[A, B, C, D, E, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: E :=>: R] =
    τ(φ).elimAbs
  def parse[A, B, C, D, E, F, R](φ: (τ[A], τ[B], τ[C], τ[D], τ[E], τ[F]) => τ[R]): τ[A :=>: B :=>: C :=>: D :=>: E :=>: F :=>: R] =
    τ(φ).elimAbs


  implicit class ArrowSyntax[A, B](f: A :=>: B) {
    def apply(a: τ[A]): τ[B] = app(arr(f), a)
  }
  implicit class ArrowArrowSyntax[A, B, C](f: (A :=>: B) :=>: C) {
    def apply(g: A :=>: B): τ[C] = app(arr(f), arr(g))
    def apply(g: τ[A :=>: B]): τ[C] = app(arr(f), g)
    def apply(g: τ[A] => τ[B]): τ[C] = app(arr(f), τ(g))
  }
  implicit class ArrowTermSyntax[A, B](f: τ[A :=>: B]) {
    def apply(a: τ[A]): τ[B] = app(f, a)
  }
  implicit class ArrowArrowTermSyntax[A, B, C](f: τ[(A :=>: B) :=>: C]) {
    def apply(g: A :=>: B): τ[C] = app(f, arr(g))
    def apply(g: τ[A :=>: B]): τ[C] = app(f, g)
    def apply(g: τ[A] => τ[B]): τ[C] = app(f, τ(g))
  }
  implicit class ProductSyntax[A, B](ab: τ[A**B]) {
    def _1: τ[A] = app(fst[:=>:, **, Unit, Hom, A, B], ab)
    def _2: τ[B] = app(snd[:=>:, **, Unit, Hom, A, B], ab)
  }
}


/**** Extended DSL interface for DSLs that support additional common primitives.
  ** This doesn't have to be supported by all DSLs.
  **/
trait ExtendedDsl extends Dsl {
  // sum type
  type \/[A, B]
  def -\/[A, B]: A :=>: (A\/B)
  def \/-[A, B]: B :=>: (A\/B)
  def either[A, B, C]: (A \/ B) :=>: (A :=>: C) :=>: (B :=>: C) :=>: C

  // some special sum types
  type Maybe[A] = Unit \/ A
  type Bool = Unit \/ Unit
  def maybe[A, B]: Maybe[A] :=>: (Unit :=>: B) :=>: (A :=>: B) :=>: B = either[Unit, A, B]
  def ifThenElse[A]: Bool :=>: (Unit :=>: A) :=>: (Unit :=>: A) :=>: A = either[Unit, Unit, A]

  // primitives for forming recursive types
  type Fix[F[_]]
  def fix[F[_]]: F[Fix[F]] :=>: Fix[F]
  def unfix[F[_]]: Fix[F] :=>: F[Fix[F]]

  // linked list (example of a recursive type)
  type Lst[A] = Fix[Unit \/ ?]
  // some list operations would be appropriate :-)


  // Primitive for recursive computations.
  //
  //                   initial value
  //                  /
  def doWhile[A, B]: A :=>: (A :=>: (A\/B)) :=>: B
  //                              \
  //                               iteration (apply until it returns a B)
}
