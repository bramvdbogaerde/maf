package maf.test.contracts

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should
import maf.modular.contracts.ConcolicTesting
import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues
import maf.language.contracts.SCExpCompiler

trait ScConcolicTesterTests extends AnyFlatSpec with should.Matchers {
  def createAnalysis(exp: ScExp): ConcolicTesting
  def analyze(program: String, expected: ConcreteValues.Value): Unit = {
    program should s"evaluate to ${expected}" in {
      val exp = SCExpCompiler.read(program)
      val analysis = createAnalysis(exp)
      analysis.analyzeOnce() shouldEqual expected
    }
  }

  import ConcreteValues.Value._
  analyze("(+ 1 1)", Integer(2))
  analyze("(if #t 1 2)", Integer(1))
  analyze("(if #f 1 2)", Integer(2))
}
