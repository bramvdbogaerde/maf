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
    "null?" -> "null?/c",
    "dependent-contract?" -> "dependent-contract/c"
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
    }
}
