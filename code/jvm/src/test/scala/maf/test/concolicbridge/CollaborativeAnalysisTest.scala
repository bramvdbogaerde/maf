package maf.test.concolicbridge

import maf.concolicbridge.ConcolicBridge
import maf.language.contracts.ScExp
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.test.ScTestsJVMGlobalStore
import maf.concolic.contracts.ConcolicTesting
import maf.concolic.ConcolicTestingJVM
import maf.language.contracts.SCExpCompiler
import maf.modular.contracts.semantics.ScModSemanticsScheme
import maf.modular.contracts._
import maf.concolicbridge.assumptions.AnalysisWithAssumptions

class CollaborativeAnalysisTest extends ScTestsJVMGlobalStore {
  class SimpleCollaborativeAnalysis(exp: ScExp) extends ConcolicBridge(exp) {
    var currentAnalysis: Option[ScModSemanticsCollaborativeTesting] = None
    var currentTester: Option[ConcolicTesting] = None

    override def modAnalysis(exp: ScExp): ScModSemanticsCollaborativeTesting = {
      currentAnalysis = Some(newAnalysis(exp))
      currentAnalysis.get
    }

    override def concolicTester(exp: ScExp): ConcolicTesting = {
      currentTester = Some(new ConcolicTestingJVM(exp))
      currentTester.get
    }
  }

  def analyze(exp: String): ScModSemanticsScheme = {
    withModifiedAnalysis(exp) { _ => }
  }

  def withModifiedAnalysis(exp: String)(f: SimpleCollaborativeAnalysis => Unit): ScModSemanticsScheme = {
    val expr = SCExpCompiler.read(exp)
    val analysis = new SimpleCollaborativeAnalysis(expr)
    f(analysis)
    analysis.analyze()
    analysis.currentAnalysis.get
  }

  "(+ 1 1)" should "equal 2" in {
    val result = analyze("(+ 1 1)")
    result.finalResult shouldEqual result.lattice.schemeLattice.number(2)
  }

  "(define (f x) (+ x 1)) (f 1)" should "equal 2" in {
    val result = analyze("(define (f x) (+ x 1)) (f 1)")
    result.finalResult shouldEqual result.lattice.schemeLattice.number(2)
  }

  "(define (f x) (if (> x 4) #t #f)) (f 5) (f 6)" should "be true" in {
    val result = analyze("(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)")
    result.finalResult shouldEqual result.lattice.schemeLattice.bool(true)
  }

  "(define (f x) (if (> x 4) #t #f)) (f 5) (f 6)" should "be bool top without assumptions" in {
    val result = withModifiedAnalysis("(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)") { analysis => analysis.disable("nondetif") }
    result.finalResult shouldEqual result.lattice.schemeLattice.boolTop
  }
}
