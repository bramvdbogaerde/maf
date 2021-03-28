package maf.concolic.contracts

import maf.language.scheme.interpreter.ConcreteValues.Value
import maf.language.contracts.ScLattice.Opq
import maf.language.contracts.ScIdentifier

/**
 * An input generator for concolic testing, it will
 * first serve values from the map, and then generates the randomly
 */
case class InputGenerator(inputs: Map[String, Value]) {

  /**
   * Generate a value for the given opaque value that is represented
   * by the given identifier
   */
  def generate(opq: Opq, name: ScIdentifier): Value =
    inputs.get(name.name).getOrElse(Oracle.fromOpq(opq))

}
