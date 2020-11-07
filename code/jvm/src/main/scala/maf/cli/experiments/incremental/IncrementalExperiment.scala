package maf.cli.experiments.incremental

import maf.core.Expression
import maf.modular.GlobalStore
import maf.modular.incremental.IncrementalModAnalysis
import maf.util.Writer._
import maf.util.benchmarks.Timeout

trait IncrementalExperiment[E <: Expression] {
  // A list of programs on which the benchmark should be executed.
  def benchmarks(): Set[String]

  // Type of an analysis.
  type Analysis = IncrementalModAnalysis[E] with GlobalStore[E]

  // Analysis construction.
  def analysis(e: E): Analysis

  // Parsing.
  def parse(string: String): E

  // The timeout to be used. The timeout also indicates half of the time maximally spent on warm-up.
  def timeout(): Timeout.T

  // What is to be done for each benchmark program.
  def onBenchmark(file: String): Unit

  // Modifies the result to report an error during the experiments.
  def reportError(file: String): Unit

  // Where to write the results.
  val outputDir:  String = "benchOutput/incremental/"
  val outputFile: String

  // Creates a string representation of the final output.
  def createOutput(): String

  // Runs measurements on the benchmarks in a given trait, or uses specific benchmarks if passed as an argument.
  def measure(bench: Option[Set[String]] = None): Unit =
    bench.getOrElse(benchmarks()).foreach { file =>
      try {
        onBenchmark(file)
      } catch {
        case e: Exception => writeErrln(s"Running $file resulted in an exception: ${e.getMessage}\n")
          reportError(file)
        case e: VirtualMachineError => writeErrln(s"Running $file resulted in an error: ${e.getMessage}\n")
          reportError(file)
      }
      println()
    }

  def main(args: Array[String]): Unit = {
    setDefaultWriter(openTimeStamped(outputDir + outputFile))
    enableReporting()
    if (args.isEmpty)
      measure()
    else
      measure(Some(args.toSet))
    val out: String = createOutput()
    writeln(out)
    closeDefaultWriter()
    disableReporting()
  }
}
