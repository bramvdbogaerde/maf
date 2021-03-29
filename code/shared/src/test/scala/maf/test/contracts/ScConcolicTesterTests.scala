package maf.test.contracts

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should
import maf.modular.contracts.ConcolicTesting
import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues
import maf.language.contracts.SCExpCompiler
import maf.concolic.contracts.Oracle
import maf.language.scheme.interpreter.ConcreteValues.Value

trait ScConcolicTesterTests extends AnyFlatSpec with should.Matchers {
  def createAnalysis(exp: ScExp): ConcolicTesting

  protected def withFixture(f: => Unit): Unit = {
    // seed the oracle so that the tests are predictable
    Oracle.reseed(0)
    // run the actual test
    f
  }

  protected def runAnalysis(program: String): Value = {
    val exp = SCExpCompiler.read(program)
    val analysis = createAnalysis(exp)
    analysis.analyzeOnce()
  }

  protected def analyze(program: String, expected: ConcreteValues.Value): Unit = withFixture {
    program should s"evaluate to ${expected}" in {
      runAnalysis(program) shouldEqual expected
    }
  }

  protected def analyzeMatches(program: String)(expected: PartialFunction[Any, _]): Unit = withFixture {
    program should s"match pattern" in {
      runAnalysis(program) should matchPattern(expected)
    }
  }

  import ConcreteValues.Value._
  analyze("(+ 1 1)", Integer(2))
  analyze("(if #t 1 2)", Integer(1))
  analyze("(if #f 1 2)", Integer(2))
  analyze("(> 3 2)", Bool(true))
  analyze("(< 3 2)", Bool(false))
  analyze("(= 0 0)", Bool(true))
  analyze("(true? #t)", Bool(true))
  analyze("(true? #f)", Bool(false))
  analyze("(false? #t)", Bool(false))
  analyze("(false? #f)", Bool(true))
  analyze("(define (f x) (= x 1)) (f 1)", Bool(true))
  analyze("(define (f x) (= x 1)) (f 0)", Bool(false))
  analyze("(define (f x) (+ x 1)) (f 1)", Integer(2))
  analyze("(define (f x) (if (= x 1) 1 0)) (f 1)", Integer(1))
  analyze("(define (f x) (if (= x 1) 1 0)) (f 0)", Integer(0))
  analyze("(define (fac x) (if (= x 0) 1 (* x (fac (- x 1))))) (fac 5)", Integer(120))
  analyzeMatches("(OPQ boolean?)") { case Bool(_) => }
  analyzeMatches("(OPQ number?)") { case Integer(_) => }
  analyzeMatches("(OPQ string?)") { case Str(_) => }
  analyzeMatches("(OPQ symbol?)") { case Symbol(_) => }
  analyzeMatches("(OPQ char?)") { case Character(_) => }
  analyzeMatches("(OPQ real?)") { case Real(_) => }
  //analyze("(define (fac x) (if (<= x 0) 1 (* x (fac (- x 1))))) (fac (OPQ number?))", Integer(120))
}
