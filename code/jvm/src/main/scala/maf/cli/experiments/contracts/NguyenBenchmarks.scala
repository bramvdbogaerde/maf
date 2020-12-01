package maf.cli.experiments.contracts

case class NguyenBenchmarks() extends Benchmarks {
  def run(): Unit = {
    val testBenchmarks = List(
      fromFile("test/soft-contract/NguyenGTH18/safe/dynamic-tests.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/ack.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/even-odd.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/factorial-acc.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/factorial.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/fibonacci.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/tricky.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/softy/tak.rkt"),
      //fromFile("test/soft-contract/NguyenGTH18/safe/softy/subst.rkt")
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-01.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-02.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-04.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-05.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-06.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-07.rkt"),
      fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-09.rkt")
    )

    runAll(testBenchmarks, "test_benchmarks_svc")
  }
}
