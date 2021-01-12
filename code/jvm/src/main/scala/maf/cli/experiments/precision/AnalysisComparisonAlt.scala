package maf.cli.experiments.precision

import maf.cli.experiments._
import maf.language.scheme._
import maf.lattice._
import maf.lattice.interfaces.{BoolLattice, CharLattice, IntLattice, RealLattice, StringLattice, SymbolLattice}
import maf.util.benchmarks._

import scala.concurrent.duration._

abstract class AnalysisComparisonAlt[Num: IntLattice, Rea: RealLattice, Bln: BoolLattice, Chr: CharLattice, Str: StringLattice, Smb: SymbolLattice]
    extends PrecisionBenchmarks {

  // the precision comparison is parameterized by:
  // - the analyses to compare in terms of precision
  // - the number of runs for the concrete interpreter
  def analyses: List[(SchemeExp => Analysis, String)]

  // and can, optionally, be configured in its timeouts (default: 20min.) and the number of concrete runs
  def timeout() = Timeout.start(Duration(20, MINUTES)) // timeout for the analyses
  def runs = 3 // number of runs for the concrete interpreter

  // keep the results of the benchmarks in a table
  var results: Table[Option[Int]] = Table.empty[Option[Int]]

  /**
   * For a given benchmark, compare each analysis with the result of the concrete interpreter
   * That is, count for each analysis how many values are strictly over-approximating the result of the concrete interpreter
   * All results are saved in the `result` table of this object
   *
   * @param path the name of / path to the benchmark program
   * @param program the Scheme expression of the benchmark program
   */
  protected def forBenchmark(path: Benchmark, program: SchemeExp): Unit = {
    // run the concrete interpreter analysis first
    val concreteResult = runInterpreter(program, path, Timeout.none, runs).get // no timeout set for the concrete interpreter
    // run the other analyses on the benchmark
    analyses.foreach { case (analysis, name) =>
      val otherResult = runAnalysis(analysis, name, program, path, timeout())
      val lessPrecise = otherResult.map(store => compareOrdered(store, concreteResult).size)
      results = results.add(path, name, lessPrecise)
    }
  }
}

object AnalysisComparisonAlt1
    extends AnalysisComparisonAlt[
      ConstantPropagation.I,
      ConstantPropagation.R,
      ConstantPropagation.B,
      ConstantPropagation.C,
      ConstantPropagation.S,
      Concrete.Sym
    ] {
  def analyses =
    // run some regular k-cfa analyses
    List(0, 1, 2).map { k =>
      (SchemeAnalyses.kCFAAnalysis(_, k), s"k-cfa (k = $k)")
    }
  def main(args: Array[String]) = runBenchmarks(
    Set(
      "test/R5RS/mceval.scm"
    )
  )

  def runBenchmarks(benchmarks: Set[Benchmark]) = {
    benchmarks.foreach(runBenchmark)
    println(results.prettyString(format = _.map(_.toString()).getOrElse("TIMEOUT")))
  }
}
