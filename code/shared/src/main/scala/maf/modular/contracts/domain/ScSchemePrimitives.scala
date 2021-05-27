package maf.modular.contracts.domain

import maf.modular.contracts.semantics._
import maf.modular.contracts._
import maf.core.{BasicEnvironment, Identity}
import maf.language.contracts.ScExp
import maf.language.contracts.ScLattice.{Arr, Grd, Thunk}
import maf.modular.GlobalStore
import maf.language.contracts.ScSchemeLattice
import maf.language.scheme.primitives.SchemePrimitive
import maf.core.Address
import maf.language.contracts.ScNil
import maf.language.contracts.ScIdentifier

/** Primitives that can be use in both the static analysis and concrete analysis */
trait ScSharedSchemePrimitives[Addr <: Address] {
  type Context
  type Value
  val lattice: ScSchemeLattice[Value, Addr]

  implicit def viewAddr(addr: ScAddresses[Context]): Addr
  def updateStore(v: (Addr, Value), symbolic: ScExp = ScNil()): Unit

  trait Implies {
    def ~>(implies: Implies): Implies

    def collectDomainContracts(
        implies: Implies
      ): List[Addr] = implies match {
      case StringImplication(prim) => List(viewAddr(ScPrimAddr(prim)))
      case Implication(left, right) =>
        collectDomainContracts(left) ++ collectDomainContracts(right)
    }

    def asGrd(name: String): Value = this match {
      case Implication(left, StringImplication(range)) =>
        val rangeMaker = lattice.thunk(Thunk(viewAddr(ScPrimAddr(range))))
        val rangeMakerAddr = viewAddr(ScPrimRangeAddr(name))

        updateStore(rangeMakerAddr -> rangeMaker)
        lattice.grd(Grd(collectDomainContracts(left), rangeMakerAddr))

      case _ => throw new Exception("unsupported ")
    }
  }

  case class StringImplication(s: String) extends Implies {
    def ~>(implies: Implies): Implies = Implication(this, implies)
  }

  implicit def stringImplication(s: String): StringImplication = StringImplication(s)

  case class Implication(left: Implies, right: Implies) extends Implies {
    override def ~>(implies: Implies): Implies = Implication(this, implies)
  }

  private def primitives =
    Map(
      "+" -> ("number?" ~> "number?" ~> "number?"),
      "-" -> ("number?" ~> "number?" ~> "number?"),
      "*" -> ("number?" ~> "number?" ~> "number?"),
      "/" -> ("number?" ~> "nonzero?" ~> "number?"),
      "=" -> ("number?" ~> "number?" ~> "bool?"),
      //"number?" -> ("any?" ~> "bool?"),
      //"procedure?" -> ("any?" ~> "bool?"),
      //"bool?" -> ("any?" ~> "bool?"),
      //">" -> ("number?" ~> "number?" ~> "bool?"),
      "<" -> ("number?" ~> "number?" ~> "bool?"),
      //"=<" -> ("number?" ~> "number?" ~> "bool?"),
      //"dependent-contract?" -> ("any?" ~> "bool?"),
      //"any?" -> ("any?" ~> "bool?"),
      // "and" -> ("any?" ~> "any?" ~> "any?"),
      //"or" -> ("any?" ~> "any?" ~> "any?"),
      "nonzero?" -> ("number?" ~> "bool?"),
      "pair?" -> ("any?" ~> "bool?"),
      //"not" -> ("any?" ~> "bool?"),
      "char?" -> ("any?" ~> "bool?"),
      "vector?" -> ("any?" ~> "bool?"),
      "string?" -> ("any?" ~> "bool?"),
      "string-length" -> ("string?" ~> "number?"),
      "symbol?" -> ("any?" ~> "bool?"),
      "true?" -> ("any?" ~> "bool?"),
      "false?" -> ("any?" ~> "bool?"),
      "null?" -> ("any?" ~> "any?"),
      "cons" -> ("any?" ~> "any?" ~> "pair?"),
      "car" -> ("pair?" ~> "any?"),
      "cdr" -> ("pair?" ~> "any?")
    )

  def setupMonitoredPrimitives(): Unit =
    primitives.foreach { case (name, implies) =>
      val contractAddr = viewAddr(ScGrdAddr(name))
      val primAddr = viewAddr(ScPrimAddr(name))
      val grd = implies.asGrd(name)
      updateStore(contractAddr -> grd)
      updateStore(primAddr -> lattice.schemeLattice.primitive(name), ScIdentifier(name, Identity.none))
      updateStore(
        viewAddr(ScMonitoredPrimAddr(name)) -> lattice.arr(
          Arr(Identity.none, Identity.none, contractAddr, primAddr)
        )
      )
    }

  val primNames: Set[String]

  private lazy val otherPrimitives =
    primNames -- primitives.map(_._1)

  /** Inject the other scheme primitives that do not have a contract (yet) */
  def setupOtherPrimitives(): Unit =
    otherPrimitives.foreach { name =>
      updateStore(viewAddr(ScPrimAddr(name)) -> lattice.schemeLattice.primitive(name), ScIdentifier(name, Identity.none))
    }

  def primBindings: Iterable[(String, Addr)] =
    primitives.keys.map(name => (name, viewAddr(ScMonitoredPrimAddr(name)))) ++
      otherPrimitives.map(name => (name, viewAddr(ScPrimAddr(name))))

}

trait ScSchemePrimitives extends ScModSemanticsScheme with GlobalStore[ScExp] { outer =>
  override var store: Map[Addr, Value] = Map()

  def primitives: ScSharedSchemePrimitives[outer.Addr] = new ScSharedSchemePrimitives[outer.Addr] {
    override type Value = outer.Value
    override type Context = outer.VarAllocationContext
    override val lattice: ScSchemeLattice[Value, Addr] = outer.lattice
    implicit override def viewAddr(addr: ScAddresses[Context]): Addr = addr

    override def updateStore(v: (Addr, Value), s: ScExp = ScNil()): Unit =
      store += v

    override val primNames: Set[String] =
      outer.primMap.keys.toSet
  }

  def baseEnv: Env = BasicEnvironment(primitives.primBindings.toMap)

  def primBindings: Iterable[(String, Addr)] =
    primitives.primBindings

  def setup(): Unit = {
    println("Setting up analysis")
    primitives.setupMonitoredPrimitives()
    primitives.setupOtherPrimitives()
  }
}
