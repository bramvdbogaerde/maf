package maf.lattice.interfaces

import maf.core.Lattice

/** A maf.lattice for symbols */
trait SymbolLattice[Sym] extends Lattice[Sym] {
  def inject(sym: String): Sym
  def toString[S: StringLattice](n: Sym): S
}

object SymbolLattice {
  def apply[Sym: SymbolLattice]: SymbolLattice[Sym] = implicitly

}
