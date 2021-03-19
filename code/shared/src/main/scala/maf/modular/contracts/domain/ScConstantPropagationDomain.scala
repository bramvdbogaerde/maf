package maf.modular.contracts.domain

import maf.core.Address
import maf.language.contracts.ScCoProductLattice

trait ScConstantPropagationDomain extends ScDomain {
  import maf.lattice.ConstantPropagation._

  val coProductLattice: ScCoProductLattice[I, B, Address] =
    new ScCoProductLattice[I, B, Address]()

  val lattice = coProductLattice.isScLattice
  type Value = coProductLattice.CoProductValue
}
