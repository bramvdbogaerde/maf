package maf.modular.contracts

import maf.modular.contracts.semantics.ScSharedSemantics
import maf.language.contracts.ScExp
import maf.language.contracts.ScLattice
import maf.core.Identity
import maf.language.contracts.ScSchemeLattice
import maf.core.Address
import maf.language.contracts.ScIdentifier
import maf.language.contracts.lattices.ScConcreteValues
import maf.language.contracts.lattices.ScConcreteValues.ScConcreteAddress
import maf.language.contracts.lattices.ScConcreteLattice

class ConcolicTester extends ScSharedSemantics with ConcolicMonadAnalysis {

  override def evict(addresses: List[ScConcreteAddress]): ScEvalM[Unit] = ???

  implicit override val lattice: ScSchemeLattice[ScConcreteValues.ScValue, Addr] = new ScConcreteLattice {}

  override val allocator: Allocator = new Allocator {

    override def alloc(idn: Identity): ScConcreteAddress = ???

    override def allocCons(
        car: PS,
        cdr: PS,
        carIdn: Identity,
        cdrIdn: Identity
      ): ScEvalM[PS] = ???

    override def allocVar(id: ScIdentifier): ScConcreteAddress = ???

    override def view[Context](addr: ScAddresses[Context]): ScConcreteAddress = ???

  }

  override def primMap(v: String): Prim = ???

  override def primitives: List[String] = ???

  override def primName(p: Prim): String = ???

  override def throwBlameError(blame: ScLattice.Blame): ScEvalM[Unit] = ???

  override def callPrimitive(p: PrimitiveOperator, args: List[Argument]): ScEvalM[PostValue] = ???

  override def call(clo: ScLattice.Clo[ScConcreteAddress], operands: List[ScConcreteValues.ScValue]): ScEvalM[ScConcreteValues.ScValue] = ???

  override def lookupOrDefine(identifier: ScIdentifier): ScEvalM[ScConcreteAddress] = ???

  override def solve(pc: ScExp): Boolean = ???

}
