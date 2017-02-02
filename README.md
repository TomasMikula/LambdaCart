# LambdaCart
Lambda syntax for Scala EDSLs


## Motivation

It is often useful to be able to manipulate a DSL program as a _value_, e.g. in order to analyze it, optimize it, store it in a database...
So let's say our DSL programs are _values_ of type `Prg[A, B]` (programs typically transform inputs to outputs, so let's include the input and output type in the type of program). The DSL implementation/library will provide us some predefined values of `Prg[A, B]` (for various `A`, `B`) and some means to combine them into new programs.

Now, it would be very convenient if we could combine them just like we combine ordinary Scala functions&mdash;using lambda expressions:

```scala
x => { /* body, optionally referring to x */ }
```

That is, name a placeholder for input and use it in the definition of the output. (If you are happy with writing your DSL programs in point-free style, you can stop reading.)

DSLs often support this by just embedding ordinary Scala functions (e.g. Free monad-based DSLs). However, you **cannot analyze a function**, or store it in a database (or at least you shouldn't).

This project introduces a technique to give lambda syntax to DSLs, without embedding functions, without macros or string parsing.


## Idea

Scala's lambda syntax only produces Scala functions. We can't have

```scala
(a: A) => { /* body */ }
```

produce a value of type `Prg[A, B]`; it produces a function, i.e. a value of type `A => B`.

The idea is to define a slightly different function:

```scala
(a: τ[A]) => { /* body */ }
```

of type `τ[A] => τ[B]`. Type `τ` (the Greek letter "tau") is defined in this library and stands for "term". Now, inside the body, the variable `a` doesn't have type `A`, but the goal is to provide enough syntactic convenience (via implicit conversions) so that e.g. `f: Prg[A, B]` can be used as `A => B` and `a: τ[A]` can be used as `A`, i.e. `f(a)` would compile as an expression of type `τ[B]`, with value `App(f, a)`. It really just captures the abstract syntax tree of "function" applications (except the functions are now of type `Prg[_, _]`).

Once we have a function `τ[A] => τ[B]`, we can apply it to a fresh variable `x` (of type `Var[A] extends τ[A]`) and obtain a term `b: τ[B]` representing (abstract syntax of) the body of the function. `x` now appears as a free variable in `b`. From `x` and `b` we form

```scala
Abs(x, b): τ[Prg[A, B]]
```

i.e. a term representing lambda abstraction. Altogether, the `τ` tree contains these nodes:

```scala
     class Var[X] extends τ[X]
case class Abs[X, Y](x: Var[X], y: τ[Y]) extends τ[Prg[X, Y]]
case class App[X, Y](f: τ[Prg[X, Y]], x: τ[X]) extends τ[Y]
case class Arr[X, Y](f: Prg[X, Y]) extends τ[Prg[X, Y]]
```

The first three are terms of lambda calculus, the last one is to embed existing programs (`Arr` stands for "arrow").

The remaining question is how to convert `τ[Prg[A, B]]` to `Prg[A, B]`, i.e. how to eliminate all the lambda abstractions and applications (variable reference will go away automatically with abstraction elimination when converting a _closed_ term (i.e. a term without free variables)). For the conversion, we will require some operations on `Prg`. One minimal set of operations is that of a _Cartesian closed category_, and we will go with it:

```scala
/** Cartesian closed category. */
trait CCC[:=>:[_, _]] {
  /** product */
  type **[A, B]

  /** terminal object */
  type Unit

  def id[A]: A :=>: A
  def compose[A, B, C](f: B :=>: C, g: A :=>: B): A :=>: C
  def fst[A, B]: (A ** B) :=>: A
  def snd[A, B]: (A ** B) :=>: B
  def prod[A, B, C](f: A :=>: B, g: A :=>: C): A :=>: (B ** C)
  def terminal[A]: A :=>: Unit
  def curry[A, B, C](f: (A ** B) :=>: C): A :=>: B :=>: C
  def uncurry[A, B, C](f: A :=>: B :=>: C): (A ** B) :=>: C
}

object CCC {
  type Aux[:=>:[_, _], &[_, _], T] = CCC[:=>:] {
    type **[A, B] = A & B
    type Unit = T
  }
}
```

All we need to do now, as designers of `Prg`, is to implement an instance of `CCC[Prg]`.


## Example

Assume a DSL given to us that supports `CCC` operations and gives us some primitives:

```scala
trait MyDsl {
  type :=>:[A, B]
  type **[A, B]
  type Unit

  implicit def CC: CCC.Aux[:=>:, **, Unit]

  type \/[A, B]
  type Maybe[A] = Unit \/ A

  /** Case analysis on \/ */
  def either[A, B, C]: (A \/ B) :=>: (A :=>: C) :=>: (B :=>: C) :=>: C

  /** Case analysis on Maybe */
  def maybe[A, B]: Maybe[A] :=>: (Unit :=>: B) :=>: (A :=>: B) :=>: B =
    either[Unit, A, B]

  /** "pattern matching" on A**B */
  def both[A, B, C](ab: τ[A**B])(f: τ[A] => τ[B] => τ[C]): τ[C]


  type Nat

  def inc: Nat :=>: Nat
  def dec: Nat :=>: Maybe[Nat]

  def zero: τ[Nat]

  /** while loop as a primitive */
  def doWhile[A, B]: A :=>: (A :=>: (A\/B)) :=>: B


  // Interface for interpreting arrows

  type Native[A]
  def exec[A, B](a: Native[A])(f: A :=>: B): Native[B]
  def exec[A, B, C](a: Native[A], b: Native[B])(f: A :=>: B :=>: C): Native[C]
  def encodeInt(i: Int): Native[Nat]
  def decodeInt(n: Native[Nat]): Int
}
```

We can use these to build our DSL programs:

```scala
def one: τ[Nat] = inc(zero)

// for-loop in terms of while-loop
//
//                   # of iterations
//                  /       initial value
//                 /       /          iteration (loop body)
//                /       /          / 
def forLoop[A]: Nat :=>: A :=>: (A :=>: A) :=>: A =
  dsl { n => τ(a => τ(f =>
    doWhile[A**Nat, A]( a**n )( both(_) { a => n =>
      maybe[Nat, (A**Nat)\/A](dec(n)) (
        _ => \/-(a)                  )(
        n => -\/(f(a)**n)             )
    })
  ))}


// Addition as iterated increment
def plus: Nat :=>: Nat :=>: Nat =
  dsl { a => τ(b =>
    forLoop(a)(b)(inc)
  )}

// Multiplication as iterated addition
def times: Nat :=>: Nat :=>: Nat =
  dsl { a => τ(b =>
    forLoop(a)(zero)(plus(b))
  )}


// factorial
def fac: Nat :=>: Nat = dsl { n =>
  forLoop(n)(one ** one)( both(_) { acc => i =>
    times(acc)(i) ** inc(i)
  })._1
}

assert(decodeInt(exec(encodeInt(2), encodeInt(2))(plus)) == 4)
assert(decodeInt(exec(encodeInt(7))(fac)) == 5040)
```

The function `τ` above has signature

```scala
def τ[A, B](f: τ[A] => τ[B]): τ[A :=>: B]
```

and is used to convert a function on terms into a term of an arrow type.

The function `dsl` has signature

```scala
def dsl[A, B](f: τ[A] => τ[B]): A :=>: B
```

and performs the translation from lambda terms to arrows of a Cartesian closed category. The translation assumes that it is passed a closed term and any occurrence of function application (`App` node) is inside a lambda abstraction (`Abs` node).

The methods `**`, `_1`, `_2` are overridden syntax for product formation and deconstruction.

Notice that we don't see what `Nat` _is_. We only see what we can do with it. Similarly, we don't see how "pairs" `A**B` are represented. It could well be that the implementation of `MyDsl` represents all data as bit strings:

```scala
type Nat      = BitString
type **[A, B] = BitString
type \/[A, B] = BitString
type Unit     = BitString
```

Yet we program with them as if `A**B` is `(A, B)`, `A \/ B` is `Either[A, B]` and `Unit` is `scala.Unit`. The translation to `CCC` operations (and their correct implementation) ensures we interpret every bit string correctly.


## Limitations

### Recursion

Simply typed lambda expressions (anonymous functions) don't give any means for expressing recursion. If we need recursion, our DSL has to introduce it as a primitive. We have seen this above with the `doWhile` primitive.

### Custom data types and pattern matching

Our DSL gave us some primitive types and type constructors to define new ones. We cannot, however, use Scala's case class syntax to define data types of our DSL and then use Scala's pattern matching syntax to define arrows that work on those data types.

Above, we have seen special arrows like `both`, `either`, `maybe` that simulate pattern matching on `**`, `\/`, `Maybe`, respectively.


## Further work

### Term size reduction

The currently implemented translation from lambda terms to CCC arrows produces arrows of enormous size even for small lambda expressions. As such, it serves as a proof of concept, but is not of practical use. Although it is expected that the translation can increase the size of terms exponentially, I'm pretty sure the current implementation can be improved significantly. The laws of Cartesian closed categories can serve as a basis for reducing the terms. (The only thing that deters me from doing it is pretty bad support for pattern matching on GADTs in Scala.)

### Linear types

An interesting area to investigate would be whether we could extend this to support "linear" arrows. My high-level idea is to annotate input and output types of an arrow, and elements of a pair, with _arities_, where arity of an input says how many times the arrow consumes the input, arity of an output says how many times the result can be consumed. Arity would be one of _ι_, _ω_, with _ι_ meaning exactly once and _ω_ meaning any number of times (including 0). We would modify the arrow combinators (and syntax via implicit conversions) so that they respect the arity annotations. So we could possibly ensure that a linear variable is only passed to an arrow that respects its linearity. However, we also have to ensure that a linear variable is passed to such an arrow at most once. Perhaps it is possible to write a macro that would check this.
