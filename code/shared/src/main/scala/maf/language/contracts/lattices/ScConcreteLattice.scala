package maf.language.contracts.lattices

import maf.core
import maf.core.{Address, BasicEnvironment, Environment, Identity, MayFail}
import maf.language.CScheme.TID
import maf.language.contracts.ScSchemeLattice
import maf.language.contracts.lattices.ScConcreteValues.ScConcreteAddress
import maf.language.scheme.SchemeLambdaExp
import maf.language.scheme.lattices.{SchemeLattice, SchemeOp}
import maf.language.scheme.interpreter.ConcreteValues
import maf.lattice.interfaces.BoolLattice
import maf.language.contracts.ScLattice._
import maf.language.contracts.ScLattice
import maf.language.scheme.primitives.SchemePrimitive
import maf.core.LatticeTopUndefined

object ScConcreteValues {
  sealed trait ScValue

  trait ScConcreteAddress extends Address
  object ScConcreteAddress {
    def apply(addr: ConcreteValues.Addr): ScConcreteWrappedAddress = {
      ScConcreteWrappedAddress(addr)
    }
  }

  case class ScConcreteAddressIdentity(idn: Identity) extends ScConcreteAddress

  case class ScConcreteWrappedAddress(addr: ConcreteValues.Addr) extends ScConcreteAddress {
    override def printable: Boolean = true

    override def idn: Identity = Identity.none

    override def productArity: Int = 1

    override def productElement(n: Int): Any = n match {
      case 0 => addr
      case _ => throw new NoSuchElementException
    }

    override def canEqual(that: Any): Boolean = that match {
      case ScConcreteWrappedAddress(thatAddr) => addr.canEqual(thatAddr)
      case _                                  => false
    }
  }

  implicit class EnvWrapper(m: ConcreteValues.Env)
      extends BasicEnvironment[ScConcreteAddress](m.map { case (k, v) =>
        (k, ScConcreteAddress(v))
      })

  case class ConcreteSchemeValue(v: ConcreteValues.Value) extends ScValue

  /**
   * A pair of two values, this is also included in the scheme intepreter, but
   * we cannot use it for the Scheme + contract interpreter because our value domain
   * is strictly larger than the vanilla Scheme domain
   */
  case class ConsValue(car: ScValue, cdr: ScValue) extends ScValue

  /**
   * A vector of values, this is also included in the Scheme interpreter,
   *  but we cannot use it for Scheme + contract interpreter because our value domain
   *  is strictly larger htan the vanilla Scheme domain
   */
  case class VectorValue(
      size: BigInt,
      elems: Map[BigInt, ScValue],
      init: ScValue)
      extends ScValue

  /** Value of the error that gets generated when a contract is violated */

  case class BlameValue(blame: Blame) extends ScValue

  /** value for an arrow contract */
  case class GrdValue(grd: Grd[ScConcreteAddress]) extends ScValue

  /** value for a guarded function */
  case class ArrValue(arr: Arr[ScConcreteAddress]) extends ScValue

  /** An unknown symbolic value, used to represent user input or other sources of unknown input * */
  case class OpqValue(opq: Opq) extends ScValue

  /** A parameterless lambda */
  case class ThunkValue(t: Thunk[ScConcreteAddress]) extends ScValue

  /** A flat contract */
  case class FlatValue(flat: Flat[ScConcreteAddress]) extends ScValue

  /** A closure */
  case class ClosureValue(clo: Clo[ScConcreteAddress]) extends ScValue
}

trait ScConcreteLattice extends ScSchemeLattice[ScConcreteValues.ScValue, ScConcreteAddress] {
  import ScConcreteValues._
  import ConcreteValues.Value._

  type Addr = ScConcreteAddress
  type L = ScValue

  /** An implementation of the Scheme lattice */
  override val schemeLattice: SchemeLattice[ScValue, ScConcreteAddress] = new SchemeLattice[ScValue, ScConcreteAddress] {

    /** Can this value be considered true for conditionals? */
    override def isTrue(x: ScValue): Boolean = x match {
      case ConcreteSchemeValue(Bool(false)) => false
      case _                                => true
    }

    /** Can this value be considered false for conditionals? */
    override def isFalse(x: ScValue): Boolean = x match {
      case ConcreteSchemeValue(Bool(false)) => true
      case _                                => false
    }

    /** Performs an SchemeOp on the abstract values */
    override def op(op: SchemeOp)(args: List[ScValue]): MayFail[ScValue, core.Error] =
      throw new Exception("no operations implemented in the lattice")

    /** Extract closures contained in this value */
    override def getClosures(x: ScValue): Set[(SchemeLambdaExp, Env)] = x match {
      case ConcreteSchemeValue(Clo(lambda, env)) =>
        Set((lambda, EnvWrapper(env)))
      case _ => Set()
    }

    /** Extract primitives contained in this value */
    override def getPrimitives(x: ScValue): Set[String] = x match {
      case ConcreteSchemeValue(Primitive(p)) => Set(p)
      case _                                 => Set()
    }

    /** Extract continuations contained in this value */
    override def getContinuations(x: ScValue): Set[K] = x match {
      // Concrete values of Scheme do not have continuations in MAF
      case _ => Set()
    }

    /** Extract pointers contained in this value */
    override def getPointerAddresses(x: ScValue): Set[Addr] = x match {
      case ConcreteSchemeValue(Pointer(v)) => Set(ScConcreteAddress(v))
      case _                               => Set()
    }

    /** Extract the thread identifiers in this value */
    override def getThreads(x: ScValue): Set[TID] = x match {
      // Our contract analysis does not support threads (yet)
      case _ => Set()
    }

    /** Injection of an integer */
    override def number(x: BigInt): ScValue = ConcreteSchemeValue(Integer(x))

    /** Top element for all integers */
    override def numTop: ScValue = throw new Exception("no top values in concrete execution")

    /** Injection of a float */
    override def real(x: Double): ScValue = ConcreteSchemeValue(Real(x))

    /** Top element for floats */
    override def realTop: ScValue = throw new Exception("no top values in concrete execution")

    /** Injection of a string */
    override def string(x: String): ScValue = ConcreteSchemeValue(Str(x))

    /** Top element for strings */
    override def stringTop: ScValue = throw new Exception("no top values in concrete execution")

    /** Injection of a boolean */
    override def bool(x: Boolean): ScValue = ConcreteSchemeValue(Bool(x))

    /** Injection of a character */
    override def char(x: Char): ScValue = ConcreteSchemeValue(Character(x))

    /** Top element for all characters */
    override def charTop: ScValue = throw new Exception("no top values in concrete execution")

    /** Injection of a primitive function */
    override def primitive(x: String): ScValue = ConcreteSchemeValue(Primitive(x))

    /** Injection of a closure */
    override def closure(x: (SchemeLambdaExp, Env)): ScValue = x._2 match {
      case BasicEnvironment(m) =>
        ConcreteSchemeValue(
          Clo(x._1,
              m.map { case (k, v) =>
                (k, v.addr)
              }
          )
        )
    }

    /** Injection of a symbol */
    override def symbol(x: String): ScValue = ConcreteSchemeValue(Symbol(x))

    /** Top element for all symbols */
    override def symbolTop: ScValue = throw new Exception("no top values in concrete execution")

    /** Injection of a cons cell. */
    override def cons(car: ScValue, cdr: ScValue): ScValue =
      ConsValue(car, cdr)

    /** Injection of the nil value */
    override def nil: ScValue = ConcreteSchemeValue(Nil)

    /** Injection of a pointer (to a cons cell, vector, etc.) */
    override def pointer(a: Addr): ScValue = ConcreteSchemeValue(Pointer(a.addr))

    /** Injection of a continuation */
    override def cont(k: K): ScValue =
      throw new Exception("continuation values are not supported in concrete execution mode")

    /** Injection of a thread identifier */
    override def thread(tid: TID): ScValue =
      throw new Exception("threads are not supported in the contract language")

    /** Creates a new lock. */
    override def lock(threads: Set[TID]): ScValue =
      throw new Exception("threads are not supported in the contract language")

    /** Acquires a given lock. */
    override def acquire(lock: ScValue, caller: TID): MayFail[ScValue, core.Error] =
      throw new Exception("threads are not supported in the contract language")

    /** Releases a given lock. */
    override def release(lock: ScValue, caller: TID): MayFail[ScValue, core.Error] =
      throw new Exception("threads are not supported in the contract language")

    override def void: ScValue = ConcreteSchemeValue(Void)

    /** A lattice has a bottom element */
    override def bottom: ScValue =
      throw new Exception("bottom not supported in concrete execution mode")

    /** A lattice has a top element (might be undefined) */
    override def top: ScValue =
      throw new Exception("bottom not supported in concrete execution mode")

    /** Elements of the lattice can be joined together */
    override def join(x: ScValue, y: => ScValue): ScValue =
      throw new Exception("join not supported in concrete execution mode")

    /** Subsumption between two elements can be checked */
    override def subsumes(x: ScValue, y: => ScValue): Boolean =
      throw new Exception("subsumption not supported in concrete execution mode")

    /** Equality check, returning an abstract result */
    override def eql[B: BoolLattice](x: ScValue, y: ScValue): B =
      throw new Exception("eql not supported in concrete execution mode")

    override def show(v: ScValue): String = v.toString()
  }

  /** Inject a guard in the abstract domain */
  def grd(grd: Grd[Addr]): ScValue = GrdValue(grd)

  /** Inject an arrow (monitors on functions) in the abstract domain */
  def arr(arr: Arr[Addr]): ScValue = ArrValue(arr)

  /** Inject a blame in the abstract domain */
  def blame(blame: Blame): ScValue = BlameValue(blame)

  /** Inject an opaque value in the abstract domain */
  def opq(opq: Opq): ScValue = OpqValue(opq)

  /** Inject a thunk in the abstract domain */
  def thunk(thunk: Thunk[Addr]): ScValue = ThunkValue(thunk)

  /** Inject a flat contract in the abstract domain */
  def flat(flat: Flat[Addr]): ScValue = FlatValue(flat)

  /** Inject a closure in the abstract domain */
  def closure(clo: ScLattice.Clo[Addr]): ScValue = ClosureValue(clo)

  /** Extract a set of arrow (monitors on functions) from the abstract value */
  def getArr(value: L): Set[Arr[Addr]] = value match {
    case ArrValue(arr) => Set(arr)
    case _             => Set()
  }

  /** Extract a set of blames from the abstract value */
  def getBlames(value: L): Set[Blame] = value match {
    case BlameValue(blame) => Set(blame)
    case _                 => Set()
  }

  /** Extract a set of guards from the abstract value */
  def getGrd(value: L): Set[Grd[Addr]] = value match {
    case GrdValue(grd) => Set(grd)
    case _             => Set()
  }

  /** Extract a set of opaque values from the abstract value */
  def getOpq(value: L): Set[Opq] = value match {
    case OpqValue(opq) => Set(opq)
    case _             => Set()
  }

  /** Extracts the set of thunks from the abstract domain */
  def getThunk(value: L): Set[Thunk[Addr]] = value match {
    case ThunkValue(thunk) => Set(thunk)
    case _                 => Set()
  }

  /** Extracts the set of flat contracts from the abtract values */
  def getFlat(value: L): Set[Flat[Addr]] = value match {
    case FlatValue(flat) => Set(flat)
    case _               => Set()
  }

  /** Extrracts a closure from the abstract domai n */
  def getClosure(value: L): Set[ScLattice.Clo[Addr]] = value match {
    case ClosureValue(clo) => Set(clo)
    case _                 => Set()
  }

  /** Returns the symbolic representation of the value if available */
  def getSymbolic(value: L): Option[String] = value match {
    case ConcreteSchemeValue(svalue) =>
      svalue match {
        case prim: ConcreteValues.Prim => Some(prim.name)
        case _                         => None // TODO: values such as numbers and so on can also be symbolicly represented
      }
    case _ => None
  }

  /** Returns the set of scheme primitives of the value */
  def getPrimitives(value: L): Set[SchemePrimitive[L, Addr]] = ??? // TODO: implement scheme primitives

  /*==================================================================================================================*/

  def isDefinitelyOpq(value: L): Boolean = value match {
    case OpqValue(_) => true
    case _           => false
  }

  def isDefinitelyArrow(value: L): Boolean = value match {
    case ArrValue(_) => true
    case _           => false
  }

  /** Returns true if the value is possible a blame */
  def isBlame(value: L): Boolean = value match {
    case BlameValue(_) => true
    case _             => false
  }

  /** Returns true if the value is possibly a thunk */
  def isThunk(value: L): Boolean = value match {
    case ThunkValue(_) => true
    case _             => false
  }

  /** Returns true if the value is possible a flat contract */
  def isFlat(value: L): Boolean = value match {
    case FlatValue(_) => true
    case _            => false
  }

  /** Returns true iof the value is possibly a closure */
  def isClosure(value: L): Boolean = value match {
    case ClosureValue(_) => true
    case _               => false
  }

  override def join(x: L, y: => L): L =
    throw new Exception("not supposed to join in the concrete domain")

  override def bottom: L = schemeLattice.bottom

  def op(op: ScOp)(args: List[L]): MayFail[L, maf.core.Error] =
    throw new Exception("operations should be implemented as primitives")
}
