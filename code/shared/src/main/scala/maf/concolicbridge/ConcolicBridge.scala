package maf.concolicbridge

import maf.language.contracts.ScExp
import maf.concolic.contracts.ConcolicTesting
import maf.util.benchmarks.Timeout

/** A type of analysis that combines concolic testing with the static analyser */
abstract class ConcolicBridge(exp: ScExp) {

  /** A modular analysis that will be used for analysing the program/ */
  def modAnalysis(exp: ScExp): ScModSemanticsWithInstrumentation

  /** Creates an instance of the ocncolic tester */
  def concolicTester(exp: ScExp): ConcolicTesting

  def analyze(): Unit = analyzeWithTimeout(Timeout.none)

  private def analysisRun(
      exp: ScExp,
      timeout: Timeout.T,
      verified: Set[String] = Set(),
      violated: Set[String] = Set()
    ): Unit = {
    if (timeout.reached) {
      throw new Exception("timeout reached")
    }

    // first we create a new analysis instance and run it
    val analysis = modAnalysis(exp)
    verified.foreach(analysis.verified)
    violated.foreach(analysis.violated)
    analysis.analyzeWithTimeout(timeout)

    // then we apply any instrumentation that might have been
    // introduced by the modular analysis
    val instrumented = analysis.instrumenter.run(exp)

    // finally we pass the instrumented expression to the
    // concolic tester and make it search for potential errors
    val tester = concolicTester(instrumented)
    tester.analyzeWithTimeout(timeout)

    val newVerified = analysis.assumed -- tester.violated

    // only continue to the next run if the violations or verified set
    // changes
    if (newVerified != verified || violated != tester.violated) {
      // continue to the next run
      analysisRun(instrumented, timeout, newVerified, tester.violated)
    }
  }

  def analyzeWithTimeout(timeout: Timeout.T): Unit =
    // kickstart the feedback loop
    analysisRun(exp, timeout)

}
