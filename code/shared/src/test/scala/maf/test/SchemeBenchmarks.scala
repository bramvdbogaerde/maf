package maf.test

import maf.bench.scheme.{IncrementalSchemeBenchmarkPrograms, SchemeBenchmarkPrograms}
import maf.util.datastructures.SmartUnion

trait VariousSequentialBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.various)
}

trait RandomSequentialBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.selectRandomSeq(40))
}

trait AllSequentialBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.sequentialBenchmarks)
}

trait ThreadBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.threads)
}

trait AllConcurrentBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.concurrentBenchmarks)
}

trait AllBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), SchemeBenchmarkPrograms.allBenchmarks)
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

trait ConcurrentIncrementalBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), IncrementalSchemeBenchmarkPrograms.threads)
}

trait SequentialIncrementalBenchmarks extends SchemeBenchmarkTests {
  override def benchmarks(): Set[Benchmark] = SmartUnion.sunion(super.benchmarks(), IncrementalSchemeBenchmarkPrograms.sequential)
}
