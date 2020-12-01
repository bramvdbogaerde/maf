package maf.cli.runnables

import maf.language.CScheme.CSchemeParser
import maf.language.scheme.SchemeExp
import maf.modular.ModAnalysis
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf._
import maf.modular.scheme.ssmodconc._
import maf.modular.worklist.LIFOWorklistAlgorithm
import maf.util.Reader
import maf.util.benchmarks.Timeout

import scala.concurrent.duration._

object AnalyzeProgram extends App {
  def one(bench: String, timeout: () => Timeout.T): Unit = {
    val text = CSchemeParser.parse(Reader.loadFile(bench))
    val a = new ModAnalysis(text) with KKallocModConc with SchemeConstantPropagationDomain
    with LIFOWorklistAlgorithm[SchemeExp] {
      val k = 1

      override def intraAnalysis(component: SmallStepModConcComponent) =
        new IntraAnalysis(component) with KCFAIntra
    }
    val b = new SimpleSchemeModFAnalysis(text) with SchemeConstantPropagationDomain
    with SchemeModFCallSiteSensitivity with LIFOWorklistAlgorithm[SchemeExp]

    val c = b
    c.analyze(timeout())
    val r = c.finalResult
    c.visited.foreach(println)
    c.deps.foreach(println)
    println(r)
  }

  val bench: List[String] = List(
    //"test/R5RS/SETL/setl-benchmarks/arithmetic.scm"
    "test/DEBUG2.scm"
  )

  bench.foreach({ b =>
    try {
      print(b + " => ")
      val t0 = System.currentTimeMillis()
      one(b, () => Timeout.start(Duration(2, MINUTES)))
      val t1 = System.currentTimeMillis()
      println(s"    in ${(t1 - t0)}ms")
    } catch {
      case t: Throwable =>
        println(s"Raised exception.")
        System.err.println(t.getMessage)
        t.printStackTrace() //t.getStackTrace.take(10).foreach(System.err.println)
        System.err.flush()
    }
  })

}
