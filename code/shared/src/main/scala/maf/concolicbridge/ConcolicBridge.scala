package maf.concolicbridge

import maf.language.contracts.ScExp
import maf.concolic.contracts.ConcolicTesting
import maf.util.benchmarks.Timeout
import maf.concolicbridge.assumptions.Tracker

sealed trait AnalysisState
case object Finished extends AnalysisState
case class Suspended(exp: ScExp, tracker: Tracker)(val k: (ScExp, Tracker) => AnalysisState) extends AnalysisState

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

  def sunspendableAnalyze(
      exp: ScExp,
      timeout: Timeout.T,
      tracker: Tracker = Tracker()
    ): AnalysisState = {
    if (timeout.reached) {
      throw new Exception("timeout reached")
    }

    // first we create a new analysis instance and run it
    val analysis = modAnalysis(exp)
    analysis.tracker = tracker
    disabled.foreach(analysis.disableAssumption)

    analysis.analyzeWithTimeout(timeout)
    // then we apply any instrumentation that might have been
    // introduced by the modular analysis
    val instrumented = analysis.instrumenter.run(exp)

    if (instrumented != exp) {
      Suspended(instrumented, tracker) { (exp, tracker) =>
        println(s"New program: ${exp}")
        // finally we pass the instrumented expression to the
        // concolic tester and make it search for potential errors
        val tester = concolicTester(exp)
        val updated = tester.analyzeWithTimeoutInstrumented(timeout)

        if (updated != exp) {
          Suspended(updated, tracker) { (exp, tracker) => sunspendableAnalyze(exp, timeout, tracker) }
        } else {
          Finished
        }
      }
    } else {
      Finished
    }
  }

  private def analysisRun(
      exp: ScExp,
      timeout: Timeout.T,
      tracker: Tracker = Tracker()
    ): Unit = {
    def loop(state: AnalysisState): Unit = state match {
      case s @ Suspended(exp, tracker) =>
        loop(s.k(exp, tracker))
      case Finished => ()
    }
    loop(sunspendableAnalyze(exp, timeout, tracker))
  }

  def analyzeWithTimeout(timeout: Timeout.T): Unit =
    // kickstart the feedback loop
    analysisRun(exp, timeout)

}
