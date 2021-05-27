package maf.test.contracts

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should
import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues
import maf.language.contracts.SCExpCompiler
import maf.concolic.contracts.{ConcTree, ConcolicTesting, Oracle}
import maf.language.scheme.interpreter.ConcreteValues.Value
import maf.modular.contracts.semantics.ScModSemantics

import java.io.PrintWriter
import java.io.File
import maf.language.contracts.ScPrelude

trait ScConcolicTesterTests extends AnyFlatSpec with should.Matchers {
  def createAnalysis(exp: ScExp): ConcolicTesting

  protected def withFixture(f: => Unit): Unit = {
    // seed the oracle so that the tests are predictable
    Oracle.reseed(0)

    // TODO: make the counter for the gensym function part of the concolic context state
    ScModSemantics.reset

    // run the actual test
    f
  }

  protected def runAnalysis(program: String): Value = {
    val exp = SCExpCompiler.preludedRead(program)
    val analysis = createAnalysis(exp)
    analysis.analyzeOnce()
  }

  protected def runAnalysisComplete(program: String, name: String = "untitled"): List[Value] = {
    val exp = SCExpCompiler.read(program)
    val analysis = createAnalysis(exp)
    analysis.analyze()

    val writer = new PrintWriter(new File(s"./out/${name}.dot"))
    ConcTree.toDot(analysis.tree, writer)
    writer.close()

    analysis.results
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

  protected def analyzeComplete(
      program: String,
      expected: Set[Value],
      desc: String = "",
      name: String = "untitled"
    ): Unit = withFixture {
    program should s"evaluate to values ${if (desc.isEmpty) expected else desc}" in {
      runAnalysisComplete(program, name).toSet shouldEqual expected
    }
  }

  protected def analyzeWithPrelude(program: String, expected: Set[Value]): Unit =
    analyzeComplete(ScPrelude.preludeString ++ program, expected, program)

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

  analyzeComplete(
    "(define x (OPQ number?)) (define y 0) (if (> x 0) (set! y 1) (set! y 2)) (if (=  x 0) (set! y (+ y 1)) (set! y (+ y 2)))",
    Set(Integer(4), Integer(3)),
    name = "example1"
  )

  analyzeComplete(
    """
    (define (foo x)
        (if (< x 4)
            (foo (+ x 1))
            #t))

    (define (bar x)
      (if (< x 0)
          #f
          (foo x)))

    (bar (OPQ number?))
  """,
    Set(Bool(true), Bool(false)),
    name = "recursion"
  )

  analyzeComplete(
    """
    (define (foo x)
        (cond
          ((< x 0) #f)
          ((< x 4) (foo (+ x 1)))
          (else #t)))

    (foo (OPQ number?))
  """,
    Set(Bool(true), Bool(false)),
    name = "recursion2"
  )

  analyzeComplete(
    """
    (define (=/c a) (lambda (x) (= x a)))
    (define/contract (foo x)
      (-> (=/c 2) number?)
      (+ x 1))

    (foo (OPQ number?))
    """,
    Set(Integer(3)),
    name = "contracts1"
  )

  analyzeComplete(
    """
    (define (=/c a) (lambda (x) (= x a)))
    (define (>/c a) (lambda (x) (> x a)))

    (define/contract (bar x)
      (-> (>/c 1) number?)
      (+ x 1))

    (define/contract (foo x)
      (-> (=/c 2) number?)
      (bar x))

    (foo (OPQ number?))
    """,
    Set(Integer(3)),
    name = "contracts2"
  )
  analyzeMatches("(OPQ boolean?)") { case Bool(_) => }
  analyzeMatches("(OPQ number?)") { case Integer(_) => }
  analyzeMatches("(OPQ string?)") { case Str(_) => }
  analyzeMatches("(OPQ symbol?)") { case Symbol(_) => }
  analyzeMatches("(OPQ char?)") { case Character(_) => }
  analyzeMatches("(OPQ real?)") { case Real(_) => }
  analyzeMatches("(any? 5)") { case Bool(true) => }
  analyzeComplete(
    """
    (define (fib n)
      (if (< n 3)
          1
          (+ (fib (- n 1)) (fib (- n 2)))))
    (fib 3)
    """,
    Set(Integer(2)),
    name = "fibonnaci"
  )
  //analyzeComplete(
  //  """
  //  (define (foo n)
  //    (if (< n 10)
  //        1
  //        (foo (+ n 1))))
  //  (foo (OPQ number?))
  //  """,
  //  Set(Integer(1)),
  //  name = "foononterm"
  //)
  analyze("(define (fac x) (if (<= x 0) 1 (* x (fac (- x 1))))) (fac 5)", Integer(120))
}
