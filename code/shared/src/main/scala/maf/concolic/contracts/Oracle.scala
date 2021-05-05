package maf.concolic.contracts

import maf.language.scheme.interpreter.ConcreteValues
import scala.util.Random
import maf.language.contracts.ScLattice.Opq

/** An oracle that is able to provide (random) values of certain types */
object Oracle {
  import ConcreteValues.Value
  private var random: Random = new Random()

  /** Reseed the oracle, useful for unit testing */
  def reseed(seed: Int): Unit = {
    random = new Random(seed)
  }

  def randomStr: Value.Str =
    Value.Str(Array.fill(random.nextInt(10))(random.nextPrintableChar()).mkString)

  def randomSymbol: Value.Symbol =
    Value.Symbol(Array.fill(random.nextInt(10))(random.nextPrintableChar()).mkString)

  def randomInteger: Value.Integer =
    Value.Integer(random.nextInt(10))

  def randomReal: Value.Real =
    Value.Real(random.nextDouble())

  def randomBool: Value.Bool =
    Value.Bool(random.nextBoolean())

  def randomCharacter: Value.Character =
    Value.Character(random.nextPrintableChar())

  private val generators: Map[String, () => Value] = Map(
    "string?" -> (() => randomStr),
    "symbol?" -> (() => randomSymbol),
    "number?" -> (() => randomInteger),
    "real?" -> (() => randomReal),
    "boolean?" -> (() => randomBool),
    "char?" -> (() => randomCharacter)
  )

  private def getRandom[T](v: IndexedSeq[T]): T =
    v(random.nextInt(v.size))

  // TODO: encode chosen generator in the path condition
  def fromOpq(opq: Opq): Value = {
    val options = opq.refinementSet.flatMap(generators.get(_)).toList
    if (options.size == 0) {
      // no refinements, just pick a random type
      getRandom(generators.values.toIndexedSeq).apply()
    } else {
      // get a random value from one of the types listed in the refinements
      getRandom(options.toIndexedSeq).apply()
    }
  }
}
