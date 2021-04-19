package maf.test.concolicbridge

import maf.concolicbridge.ConcolicBridge
import maf.language.contracts.ScExp
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.test.ScTestsJVMGlobalStore
import maf.concolic.contracts.ConcolicTesting
import maf.concolic.ConcolicTestingJVM
import maf.language.contracts.SCExpCompiler
import maf.modular.contracts.semantics.ScModSemanticsScheme
import maf.language.contracts.ScLattice.GuardUnverified
import maf.language.contracts.ScLattice.GuardVerified
import maf.language.contracts.ScLattice.GuardViolated

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

  "(make-guard)" should "evaluate to an unverified guard" in {
    val result = analyze("(make-guard)")
    result.lattice.getAssumptionGuard(result.finalResult).status shouldEqual GuardUnverified
  }

  "(make-verified-guard)" should "evaluate to a verified guard" in {
    val result = analyze("(make-verified-guard)")
    result.lattice.getAssumptionGuard(result.finalResult).status shouldEqual GuardVerified
  }

  "(make-violated-guard)" should "evaluate to a violated guard" in {
    val result = analyze("(make-violated-guard)")
    result.lattice.getAssumptionGuard(result.finalResult).status shouldEqual GuardViolated
  }

  "(+ 1 1)" should "equal 2" in {
    val result = analyze("(+ 1 1)")
    result.finalResult shouldEqual result.lattice.schemeLattice.number(2)
  }

  "(define (f x) (+ x 1)) (f 1)" should "equal 2" in {
    val result = analyze("(define (f x) (+ x 1)) (f 1)")
    result.finalResult shouldEqual result.lattice.schemeLattice.number(2)
  }

  "(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)" should "be true" in {
    val result = withModifiedAnalysis("(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)") { analysis => analysis.disable("pure") }
    result.finalResult shouldEqual result.lattice.schemeLattice.bool(true)
  }

  "(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)" should "be bool top without assumptions" in {
    val result = withModifiedAnalysis("(define (f x) (if (< x 4) #t #f)) (f 3) (f 2)") { analysis =>
      analysis.disable("nondetif"); analysis.disable("pure")
    }
    result.finalResult shouldEqual result.lattice.schemeLattice.boolTop
  }

  "(define (f x) (if (< x 4) #t #f)) (f 3) (f 5)" should "be bool top when the assumption is violated" in {
    val result = withModifiedAnalysis("(define (f x) (if (< x 4) #t #f)) (f 3) (f 5)") { analysis => analysis.disable("pure") }
    result.finalResult shouldEqual result.lattice.schemeLattice.boolTop
  }

  "nonblame assumption" should "fully verify a contract program without blaming" in {
    val program = """(define (</c x) (lambda (y) (< y x)))
     (define/contract (h x) (~ (</c 5) (lambda (x) number?))
       42)

     (define (g x) (h x))
     (define (f x)
       (if (< x 5) (g x) #f))
     (f 2)
     (f 3)
    """

    val result = withModifiedAnalysis(program) { analysis =>
      analysis.disable("pure")
      analysis.disable("value")
      analysis.disable("nondetif")
    }

    result.summary.blames.values.toSet shouldEqual Set()
  }

  "nonblame assumption" should "should be able to be disabled" in {
    val program = """(define (</c x) (lambda (y) (< y x)))
     (define/contract (h x) (~ (</c 5) (lambda (x) number?))
       42)

     (define (g x) (h x))
     (define (f x)
       (if (< x 5) (g x) #f))
     (f 2)
     (f 3)
    """

    val result = withModifiedAnalysis(program) { analysis =>
      analysis.disable("pure")
      analysis.disable("value")
      analysis.disable("nondetif")
      analysis.disable("nonblame")
    }

    result.summary.blames.values.size should be > 0
  }

  "nonblame assumption" should "should be able to verify cross-component path conditions" in {
    val program = """(define (</c x) (lambda (y) (< y x)))
     (define/contract (h x) (~ (</c 5) (lambda (x) number?))
       42)

     (define (g x) (h x))
     (define (f x)
       (if (< x 5) (g x) #f))
     (f (OPQ number?))
    """

    val result = withModifiedAnalysis(program) { analysis =>
      analysis.disable("pure")
      analysis.disable("value")
      analysis.disable("nondetif")
    }

    result.summary.blames.values.size shouldEqual 0
  }
}
