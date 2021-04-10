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
    val expr = SCExpCompiler.read(exp)
    val analysis = new SimpleCollaborativeAnalysis(expr)
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
}
