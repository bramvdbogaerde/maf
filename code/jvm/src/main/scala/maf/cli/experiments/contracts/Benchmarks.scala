package maf.cli.experiments.contracts

import java.io.File

import maf.language.contracts.{SCExpCompiler, ScExp}
import maf.modular.contracts.ScJVMAnalysis
import maf.util.{Reader, Writer}
import maf.util.benchmarks.Timer
import maf.util.benchmarks.Table

trait Benchmarks {
  type Benchmark = String
  type Program = ScExp

  /**
   * Create a benchmark from file
   * @param filename the name of the file for which to create a benchmark
   * @return a new benchmark that can be executed using <code>runBenchmark</code>
   */
  def fromFile(filename: String): Benchmark = filename

  /**
   * Creates a list of benchmarks from the files in the given directory
   * @param dirname the name of the directory to read from
   * @return a list of benchmarks that can be executed using <code>runBenchmarks</code>
   */
  def fromDirectory(dirname: String): List[Benchmark] = {
    val dir = new File(dirname)
    if (dir.exists() && dir.isDirectory) {
      dir.listFiles.filter(_.isFile).map(_.getName).toList
    } else {
      throw new Exception("Directory did not exists or is not a directory")
    }
  }
}
