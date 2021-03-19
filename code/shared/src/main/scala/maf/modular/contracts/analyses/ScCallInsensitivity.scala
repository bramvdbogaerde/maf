package maf.modular.contracts.analyses

import maf.core.Identity
import maf.core.Position.Position
import maf.language.contracts.{ScIdentifier, ScLattice}

import maf.modular.contracts._
import maf.modular.contracts.semantics._

trait ScCallInsensitivity extends ScModSemanticsScheme {
  type AllocationContext = Component
  type VarAllocationContext = ComponentContext
  def allocVar(id: ScIdentifier, cmp: ComponentContext): ScVarAddr[VarAllocationContext] =
    ScVarAddr(id, cmp)
  def allocGeneric(idn: Identity, cmp: Component): ScGenericAddr[AllocationContext] =
    ScGenericAddr(idn, cmp)

  type ComponentContext = Unit
  def allocCtx(
      clo: ScLattice.Clo[Addr],
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext = ()

  def context(_cmp: Component): ComponentContext = ()
}
