package maf.concolicbridge

import maf.language.contracts.ScExp
import maf.concolic.contracts.ConcolicTesting
import maf.util.benchmarks.Timeout
import maf.concolicbridge.assumptions.Tracker

/** A type of analysis that combines concolic testing with the static analyser */
abstract class ConcolicBridge(exp: ScExp) {

  /** Set of disabled assumptions */
  private var disabled: Set[String] = Set()
  def disable(assumption: String): Unit = {
    disabled += assumption
  }

  /** A modular analysis that will be used for analysing the program/ */
  def modAnalysis(exp: ScExp): ScModSemanticsCollaborativeTesting

  /** Creates an instance of the ocncolic tester */
  def concolicTester(exp: ScExp): ConcolicTesting

  def analyze(): Unit = analyzeWithTimeout(Timeout.none)

  private def analysisRun(
      exp: ScExp,
      timeout: Timeout.T,
      verified: Set[String] = Set(),
      violated: Set[String] = Set(),
      tracker: Tracker = Tracker()
    ): Unit = {
    if (timeout.reached) {
      throw new Exception("timeout reached")
    }

    // first we create a new analysis instance and run it
    val analysis = modAnalysis(exp)
    verified.foreach(analysis.registerVerified)
    analysis.tracker = tracker
    disabled.foreach(analysis.disableAssumption)

    analysis.analyzeWithTimeout(timeout)

    // then we apply any instrumentation that might have been
    // introduced by the modular analysis
    val instrumented = analysis.instrumenter.run(exp)

    if (instrumented != exp) {
      println(s"New program: ${instrumented}")
      // finally we pass the instrumented expression to the
      // concolic tester and make it search for potential errors
      val tester = concolicTester(instrumented)
      val updated = tester.analyzeWithTimeoutInstrumented(timeout)

      val newVerified = analysis.tracker.allAssumptions

      // only continue to the next run if the violations or verified set
      // changes
      if (instrumented != updated) {
        println(s"Got answer back from the concolic tester $updated")
        // continue to the next run
        analysisRun(updated, timeout, newVerified, Set(), analysis.copyTracker)
      }
    }
  }

  def analyzeWithTimeout(timeout: Timeout.T): Unit =
    // kickstart the feedback loop
    analysisRun(exp, timeout)

}
