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

object ScConcreteValues {
  sealed trait ScValue

  case class ScConcreteAddress(addr: ConcreteValues.Addr) extends Address {
    override def printable: Boolean = true

    override def idn: Identity = Identity.none

    override def productArity: Int = 1

    override def productElement(n: Int): Any = n match {
      case 0 => addr
      case _ => throw new NoSuchElementException
    }

    override def canEqual(that: Any): Boolean = that match {
      case ScConcreteAddress(thatAddr) => addr.canEqual(thatAddr)
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
}

trait ScConcreteLattice extends ScSchemeLattice[ScConcreteValues.ScValue, ScConcreteAddress] {
  import ScConcreteValues._
  import ConcreteValues.Value._

  type Addr = ScConcreteAddress

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
}
