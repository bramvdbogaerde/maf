package maf.modular.contracts.analyses

import maf.core.Identity
import maf.language.contracts.{ScExp, ScIdentifier, ScLattice, ScSchemeLattice}
import maf.modular.ModAnalysis
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.benchmarks.Timeout
import maf.modular.contracts.semantics._
import maf.modular.contracts.domain._
import maf.modular.contracts._

object SimpleScSemantics {
  val primitivesMap = Map(
    ">" -> ">/c",
    "=" -> "=/c",
    "<" -> "</c",
    "-" -> "-/c",
    "+" -> "+/c",
    "*" -> "*/c",
    "/" -> "//c",
    "string=?" -> "string=?/c",
    "number?" -> "int?/c",
    "string?" -> "string?/c",
    "nonzero?" -> "nonzero?/c",
    "any?" -> "any?/c",
    "true?" -> "true?/c",
    "false?" -> "false?/c",
    "procedure?" -> "proc?/c",
    "bool?" -> "bool?/c",
    "and" -> "and/c",
    "or" -> "or/c",
    "not" -> "not/c",
    "number?" -> "int?/c",
    "char?" -> "char?/c",
    "pair?" -> "pair?/c",
    "string-length" -> "string-length",
    "null?" -> "null?/c"
  )
}

case class NoOpMonad[X]()
abstract class SimpleScSemantics(prg: ScExp)
    extends ModAnalysis(prg)
       with ScBigStepSemanticsScheme
       with ScBigStepSemanticsMonitored
       with ScStandardComponents
       with ScSchemePrimitives
       with FIFOWorklistAlgorithm[ScExp] { outer =>

  val primitivesMap: Map[String, String] = SimpleScSemantics.primitivesMap
  override def analyzeWithTimeout(timeout: Timeout.T): Unit = {
    setup()
    super.analyzeWithTimeout(timeout)
  }

  override def intraAnalysis(component: Component) =
    new IntraAnalysis(component) with IntraScBigStepSemantics with IntraScBigStepSemanticsMonitored {
      case class PS(pure: Val, symbolic: ScExp) extends IsPostValue

      override type M[X] = NoOpMonad[X]

      /** A value combined with some symbolic information */
      override type PostValue = PS

      /** The type of a mapping between an addresses and a value */
      override type StoreCache = maf.core.Store[Addr, PostValue]

      /** The t ype of a raw value without any symbolic information */
      override type Val = outer.Value

      /** The type of an address */
      override type Addr = outer.Addr

      /** The type of primitive values */
      override type Prim = ()

      /** A concrete store */
      override type ConcreteStore = this.type
      implicit override val lattice: ScSchemeLattice[Value, SimpleScSemantics.this.Addr] = outer.lattice
      override val allocator: Allocator = new Allocator {

        /** Generic allocation based on identity */
        override def alloc(idn: Identity): Addr = ???

        /** Allocate a pair in the memory of the machine */
        override def allocCons(
            car: PostValue,
            cdr: PostValue,
            carIdn: Identity,
            cdrIdn: Identity
          ): ScEvalM[PostValue] = ???

        /** Allocates an address for a variable */
        override def allocVar(id: ScIdentifier): Addr = ???

        override def allocPrim(name: String): Addr = ???

        /**
         * Views an address from the abstract ScAddreses class
         * as an address for this semanticds
         */
        override def view[Context](addr: ScAddresses[Context]): Addr = ???
      }

      /**
       * Returns the primitive implementation associated with the given name
       *
       * @param v the name of the primitive to lookup
       * @return the implementation of the primitive with the given name
       */
      override def primMap(v: String): Prim = ???

      /** Returns a list of available primitives */
      override def primitives: List[String] = ???

      /** Returns the name of the given primitive */
      override def primName(p: Prim): String = ???

      /** Results in a blaming error */
      override def throwBlameError(blame: ScLattice.Blame): ScEvalM[Unit] = ???

      /**
       * Calls the given primive with the given argument,
       * it requires the original  expression due to store allocation
       * functions that might use the identity of the original expression,
       * for concrete executions this is not used
       *
       * @param p    the primitive that needs to be applied
       * @param args a list of arguments that need to be passed to the primitive
       * @return an computation that applies the given primitive and returns a value
       */
      override def callPrimitive(p: PrimitiveOperator, args: List[Argument]): ScEvalM[PS] = ???

      /** Calls the given closure with the given arguments */
      override def call(clo: ScLattice.Clo[SimpleScSemantics.this.Addr], operands: List[PostValue]): ScEvalM[PostValue] = ???

      /**
       * Looks up the given identifier and returns its address if defined, otherwise allocates an address
       * and returns it
       */
      override def lookupOrDefine(identifier: ScIdentifier): ScEvalM[SimpleScSemantics.this.Addr] = ???

      /**
       * Returns true if the given path condition is satisfiable
       *
       * @param pc the path condition to solve for
       * @return true if the path condition is satisfiable otherwise false
       */
      override def solve(pc: PC): Boolean = ???

      /** An instance of the monad typeclass */
      override def abstractMonadInstance: ScAbstractSemanticsMonad[M] = new ScAbstractSemanticsMonad[NoOpMonad] {

        /**
         * Is supposed to halt the computation, when
         * the monad is sequenced with another
         *
         * <code>
         * void >> ( effectful { println("not reachable") } )
         * </code>
         */
        override def void[X]: NoOpMonad[X] = NoOpMonad()

        /** Injects a value in the Monad */
        override def pure[X](v: => X): NoOpMonad[X] = NoOpMonad()

        override def flatMap[X, Y](m: NoOpMonad[X], f: X => NoOpMonad[Y]): NoOpMonad[Y] = NoOpMonad()
      }

      /** Modifies the PC using the given function */
      override def modifyPC(f: PC => PC): ScEvalM[Unit] = ???

      /** Adds the given symbolic information to the given raw value */
      override def value(v: Value, s: PC): PS = ???

      /**
       * Applies f with the list of ignored identities,
       * ignored identities refer to values of which the validity of the
       * contract does not matter
       */
      override def withIgnoredIdentities[X](f: List[Identity] => X): ScEvalM[X] = ???

      /** Adds an ignored identity to the context */
      override def addIgnored(idns: Iterable[Identity]): ScEvalM[Unit] = ???

      override def withEnv[B](f: Env => ScEvalM[B]): ScEvalM[B] = ???

      /** Applies the modification function to the current environment */
      override def modifyEnv(f: Env => Env): ScEvalM[Unit] = ???

      /**
       * Nondeterministicly execute the given branches
       * optionally, a value can be given that determines which branch was chosen.
       * True = the t branch
       * False = the f branch
       */
      override def nondet[X](
          t: ScEvalM[X],
          f: ScEvalM[X],
          v: Option[Boolean]
        ): ScEvalM[X] = ???

      /**
       * Same as nondet but works with a set of branches, here the optional v value to
       * indicate which branch was taken cannot be used.
       */
      override def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = ???

      /**
       * Returns a computation that applies the given function with the current
       * path condition
       */
      override def withPc[X](f: PC => X): ScEvalM[X] = ???

      /**
       * Returns a computation that applies the given function with the current
       * store cache.
       */
      override def withStoreCache[X](f: StoreCache => ScEvalM[X]): ScEvalM[X] = ???

      /**
       * Returns a computation that applies the given function on the current store cache
       * and expects a tuple of a value and a new store cache
       */
      override def withStoreCacheExplicit[X](f: StoreCache => (X, StoreCache)): ScEvalM[X] = ???

      /** Same as addToCache but joins the value in the cache according to some lattice (only for abstract domains) */
      override def joinInCache(addr: SimpleScSemantics.this.Addr, value: PS): ScEvalM[Unit] = ???

      /**
       * Given a computation that yields states that contain sets of values, this operator yields a single computation
       * that gives rises to a state for every element in the given set.
       */
      override def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = ???

      /**
       * Action that prints the current store as a table
       * to the screen. Useful for debugging.
       */
      override def printStore: ScEvalM[Unit] = ???

      /** Removes the given addresses from the store */
      override def evict(addresses: List[SimpleScSemantics.this.Addr]): ScEvalM[Unit] = ???

      override def readSafe(addr: Addr): ScEvalM[PostValue] = ???

      /**
       * Writes the given value to the given address
       *
       * @param addr  the address to write the value to
       * @param value the value to write to the given address
       * @return a computation that writes the given value to the address
       */
      override def write(addr: SimpleScSemantics.this.Addr, value: PS): ScEvalM[Unit] = ???

      /** Forcefully write to the store */
      override def writeForce(addr: SimpleScSemantics.this.Addr, value: PS): ScEvalM[Unit] = ???

      override def evaluatedValue(value: PostValue): ScEvalM[PostValue] = pure(value)

      /** Run the given computation without any initial context */
      override def run[A](c: ScEvalM[A]): A = ???
    }
}
