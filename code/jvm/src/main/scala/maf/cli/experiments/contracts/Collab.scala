package maf.cli.experiments.contracts;

object Collab extends Benchmarks with CollabBenchmark {
  override val testBenchmarks: List[Benchmark] = List(
    //fromFile("test/soft-contract/NguyenGTH18/safe/dynamic-tests.rkt"),
    //fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/ack.rkt"),
    fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/even-odd.rkt"), // OK
    //fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/factorial-acc.rkt"), // memory error
    //fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/factorial.rkt"), // memory error
    fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/fibonacci.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/tricky.rkt"), // OK
    //fromFile("test/soft-contract/NguyenGTH18/safe/softy/tak.rkt"),
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-01.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-02.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-04.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-05.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-06.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-07.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-09.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-10.rkt"), // OK
    //fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-11.rkt"), // NOT OK
    //fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-13.rkt"), // variable "not" not found
    fromFile("test/soft-contract/NguyenGTH18/safe/octy/ex-14.rkt"),
    // fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/extensionality.rkt"), // infinite loop
    // fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/fact.rkt"), // arity mismatch in contract?
    fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/id-dependent.rkt"), // OK
    fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/impossible-precon.rkt") // OK
    // fromFile("test/soft-contract/NguyenGTH18/safe/sym-exe/recip.rkt") // variable "not" not found
  )

  def main(args: Array[String]): Unit = {
    runAll("collab_globalstore")
  }
}
