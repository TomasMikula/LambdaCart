package demo

import scala.annotation.tailrec
import lambdacart._

/**** Interface of our DSL.
  ** This is what users will program against.
  **/
trait MyDsl extends ExtendedDsl { dsl =>
  // For users, Nat is an abstract type.
  // They don't get to see its representation.
  type Nat

  def inc: Nat :->: Nat
  def dec: Nat :->: Maybe[Nat]

  def zero: $[Nat]
  def one: $[Nat] = inc(zero)


  //                   # of iterations
  //                  /       initial value
  //                 /       /          iteration (loop body)
  //                /       /          / 
  def forLoop[A]: Nat :->: A ->: (A ->: A) ->: A =
    dsl { (n, a, f) =>
      doWhile[A**Nat, A]( a**n )( both(_) { a => n =>
        maybe[Nat, (A**Nat)\/A](dec(n)) (
          _ => \/-(a)                  )(
          n => -\/(f(a)**n)             )
      })
    }


  def plus: Nat :->: Nat ->: Nat =
    dsl { (a, b) =>
      forLoop(a)(b)(inc)
    }
  
  def times: Nat :->: Nat ->: Nat =
    dsl { (a, b) =>
      forLoop(a)(zero)(plus(b))
    }


  // Interface for interpreting arrows

  type Native[A]
  def exec[A, B](a: Native[A])(f: A :->: B): Native[B]
  def exec[A, B, C](a: Native[A], b: Native[B])(f: A :->: B ->: C): Native[C]
  def encodeInt(i: Int): Native[Nat]
  def decodeInt(n: Native[Nat]): Int

  // For testing purposes
  def sizeOf[A, B](f: A :->: B): Int
}

object MyDsl {
  val instance: MyDsl = MyDslImpl
}

/**** Implementation of our DSL.
  ** Hidden from the users.
  **/
private[demo] object MyDslImpl extends MyDsl {

  type Nat = Int
  type :->:[A, B] = List[Inst]
  type **[A, B] = (A, B)
  type \/[A, B] = Either[A, B]

  type Unit = scala.Unit

  val zero: $[Nat] = obj(List(Zero))

  def doWhile[A, B]: A :->: (A :->: (A\/B)) :->: B = List(Curried(List(While)))

  def -\/[A, B]: A :->: (A \/ B) = List(ToLeft)
  def \/-[A, B]: B :->: (A \/ B) = List(ToRight)
  def either[A, B, C]: (A \/ B) :->: (A :->: C) :->: (B :->: C) :->: C =
    List(Curried(List(Curried(List(Either)))))

  def fix[F[_]]: F[Fix[F]] :->: Fix[F] = List()
  def unfix[F[_]]: Fix[F] :->: F[Fix[F]] = List()
  
  val inc: Nat :->: Nat = List(Inc)
  val dec: Nat :->: Maybe[Nat] = List(Dec)

  def encodeInt(i: Int): Native[Nat] = {
    require(i >= 0)
    i
  }

  def decodeInt(n: Native[Nat]): Int = n

  def sizeOf[A, B](f: A :->: B): Int = {
    @tailrec def go(sum: Int, is: List[Inst]): Int =
      is match {
        case i :: is => i match {
          case Iter(f)        => go(sum + 1, f ::: is)
          case Curried(f)     => go(sum + 1, f ::: is)
          case Papplied(f, a) => go(sum + 2, f ::: is) // XXX: should implement sizeOf(a)
          case _              => go(sum + 1,       is)
        }
        case Nil     => sum
      }

    go(0, f)
  }

  sealed abstract class Inst
  case object Dup extends Inst      // duplicate the top of the stack
  case object Pop extends Inst      // remove an element off the top of the stack
  case object Null extends Inst     // replace the top of the stack with Unit
  case object Zero extends Inst     // replace the top of the stack with 0
  case object Inc extends Inst      // increment the top of the stack by 1
  case object Dec extends Inst      // decrement the top of the stack by 1, return (0)\/(n-1)
  case object Swap extends Inst     // swap the two topmost elements
  case object Merge extends Inst    // merge the two topmost elements into one
  case object Unmerge extends Inst  // reverse of Merge
  case object ToLeft extends Inst   // wrap top of the stack in Left
  case object ToRight extends Inst  // wrap top of the stack in Right
  case object Load extends Inst     // decode instructions from the top of the stack and execute next
  case object Either extends Inst   // primitive conditional
  case object While extends Inst    // primitive while-loop
  case class Iter(f: List[Inst]) extends Inst // implementation of while, after loading instructions from data
  case class Curried(f: List[Inst]) extends Inst
  case class Papplied(f: List[Inst], a: Any) extends Inst // function taking a pair partially applied to the first argument


  type Native[A] = A

  def exec[A, B](a: Native[A])(f: A :->: B): Native[B] = {
    val stack = execStack(List(a), f)

    assert(stack.size == 1)

    stack.head.asInstanceOf[B]
  }

  def exec[A, B, C](a: Native[A], b: Native[B])(f: A :->: B ->: C): Native[C] = {
    val stack1 = execStack(List(a, b), f)

    assert(stack1.size == 2)
    assert(stack1(1) == b)

    val stack2 = execStack(stack1.tail, stack1.head.asInstanceOf[List[Inst]])

    assert(stack2.size == 1)

    stack2.head.asInstanceOf[C]
  }

  @tailrec private def execStack(stack: List[Any], prg: List[Inst]): List[Any] =
    prg match {
      case i::is => i match {
        case Dup => execStack(stack.head :: stack, is)
        case Pop => execStack(stack.tail, is)
        case Null => execStack(()::stack.tail, is)
        case Zero => execStack(0::stack.tail, is)
        case Inc => execStack((stack.head.asInstanceOf[Int] + 1)::stack.tail, is)
        case Dec => execStack((if(stack.head == 0) Left(0) else Right(stack.head.asInstanceOf[Int] - 1))::stack.tail, is)
        case Swap => execStack(stack(1)::stack(0)::stack.drop(2), is)
        case Merge => execStack((stack(0), stack(1))::stack.drop(2), is)
        case Unmerge => execStack(stack.head.asInstanceOf[(Any, Any)] match { case (a, b) => a::b::stack.tail }, is)
        case ToLeft => execStack(Left(stack.head)::stack.tail, is)
        case ToRight => execStack(Right(stack.head)::stack.tail, is)
        case Load => execStack(stack.tail, stack.head.asInstanceOf[List[Inst]] ::: is)
        case Either =>
          stack.head.asInstanceOf[((Either[Any, Any], List[Inst]), List[Inst])] match {
            case ((Left(a), onA), _)  => execStack(a::stack.tail, onA ::: is)
            case ((Right(b), _), onB) => execStack(b::stack.tail, onB ::: is)
          }
        case While =>
          val (a, f) = stack.head.asInstanceOf[(Any, List[Inst])]
          execStack(a::stack.tail, f ::: Iter(f) :: is)
        case Iter(body) =>
          stack.head match {
            case Left(a)  => execStack(a::stack.tail, body ::: Iter(body) :: is)
            case Right(b) => execStack(b::stack.tail,                        is)
          }
        case Curried(f) => execStack(List(Papplied(f, stack.head)) :: stack.tail, is)
        case Papplied(f, a) => execStack((a, stack.head)::stack.tail, f ::: is)
      }
      case Nil =>
        stack
    }

  implicit def ccc: CCC.Aux[:->:, **, Unit, Hom] = new CCC[:->:] {
    type **[A, B] = MyDslImpl.**[A, B]
    type Unit = MyDslImpl.Unit
    type Hom[A, B] = MyDslImpl.Hom[A, B]

    def id[A]: A :->: A = List()
    def compose[A, B, C](f: B :->: C, g: A :->: B): A :->: C = g ::: f
    def fst[A, B]: (A**B) :->: A = Unmerge :: Swap :: Pop :: Nil
    def snd[A, B]: (A**B) :->: B = Unmerge :: Pop :: Nil
    def prod[A, B, C](f: A :->: B, g: A :->: C): A :->: (B**C) = Dup :: g ::: Swap :: f ::: Merge :: Nil
    def terminal[A]: A :->: Unit = Null :: Nil
    def curry[A, B, C](f: (A**B) :->: C): A :->: B :->: C = Curried(f) :: Nil
    def uncurry[A, B, C](f: A :->: B :->: C): (A**B) :->: C = Unmerge :: f ::: Load :: Nil
  }

}
