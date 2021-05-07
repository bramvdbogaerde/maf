package maf.cli.experiments.contracts

import maf.language.contracts.{SCExpCompiler, ScExp}
import maf.modular.contracts.ScJVMAnalysis
import maf.util.{Reader, Writer}
import maf.util.benchmarks.Timer
import maf.util.benchmarks.Table

/** An auxiliary trait for benchmark soft contract verification programs */
trait ModAnalysisBenchmark extends Benchmarks {

  import maf.cli.experiments.ScAnalyses._

  val configurations: Map[String, ScExp => ScJVMAnalysis] =
    Map(
      //"localStore"  -> localStoreCallInsensitiveAnalysis,
      "globalStore" -> globalStoreCallInsensitiveAnalysis
    )

  /**
   * Run a single benchmark
   * @param createAnalysis a function that creates an analysis for the given program
   * @param benchmark the file to benchmark
   * @return the result of the benchmark, including the time it took to run the benchmark as w
   *         well as how many contract verifications had been performed.
   */
  def runBenchmark(
      createAnalysis: (Program => ScJVMAnalysis)
    )(
      benchmark: Benchmark
    ): BenchmarkResult = {
    println("================================================================================")
    println(s"Starting benchmark: ${benchmark}")

    val (elapsedTime, analysis) = Timer.time {
      val source = Reader.loadFile(benchmark)
      val program = SCExpCompiler.preludedRead(source)
      val analysis = createAnalysis(program)
      analysis.analyze()
      analysis
    }

    println(s"Finished benchmark in ${elapsedTime / (1000000)} ms")
    println(analysis.summary.blames)
    val result = BenchmarkResult(
      benchmark,
      elapsedTime,
      analysis.contractApplications,
      analysis.analysedComponents,
      analysis.verifiedContracts,
      analysis.distinctContracts,
      !analysis.allSafe || (analysis.allSafe && analysis.summary.blames.isEmpty)
    )

    result
  }

  /**
   * Run the given benchmarks
   * @param benchmarks the benchmarks to run
   * @param out the file to write the results of the benchmarks to.
   *            The results will be written in a CSV format.
   *            The name of the file should be without an extension, this function will open a file with
   *            the .csv extension.
   */
  def runBenchmarks(
      createAnalysis: (Program => ScJVMAnalysis)
    )(
      benchmarks: List[Benchmark],
      out: String
    ): Unit = {
    val results = benchmarks.map(runBenchmark(createAnalysis))
    val writer = Writer.open(s"$out.csv")

    val outTable = results.foldRight(Table.empty[String]) { _.addToTable(_) }

    writer.write(outTable.toCSVString())
    writer.close()
  }

  /**
   * Run the given list of benchmarks on all available configurations
   *
   * @param benchmarks the benchmarks to run
   * @param out the prefix of the filename in which the results should be stored (as CSV)
   */
  def runAll(benchmarks: List[Benchmark], out: String): Unit = {
    configurations.foreach { case (name, c) => runBenchmarks(c)(benchmarks, s"${out}_$name") }
  }

  def run(): Unit
}
