package maf.cli.experiments.contracts

import maf.modular.contracts.CollaborativeAnalysisJVM
import maf.language.contracts.SCExpCompiler
import maf.util.Reader
import maf.concolicbridge.Suspended
import maf.concolicbridge.AnalysisState
import maf.concolicbridge.Finished
import maf.util.benchmarks.Timeout
import maf.util.benchmarks.Table
import maf.util.Writer

case class CollabBenchmarkResult(
    benchmarkName: String,
    elapsedTime: Long,
    analysedComponents: Int,
    /** Number of verified contracts without using assumptions */
    verifiedContracts: Int,
    distinctContracts: Int,
    collabIterations: Int,
    /** How much time it took for each of the static analyses to run */
    elapsedAnalysisTimes: List[Long],
    /** How much time it took for each of the concolic testers to run */
    elapsedConcolicTimes: List[Long],
    /** How many assumptions we made */
    numberOfAssumptions: Int,
    /** How many contracts we have verified in each iteration */
    verifiedContractsOverTime: List[Int],
    /** How many assumptions were made but violated */
    violatedAssumptions: Int,
    /**
     * The number of assumptions that could be verified or were used
     *  as being verified
     */
    verifiedAssumptions: Int) {
  def addToTable(inTable: Table[String]): Table[String] = {
    var outTable = inTable
    outTable = outTable.add(this.benchmarkName, "elapsedTime", elapsedTime.toString)
    outTable = outTable.add(this.benchmarkName, "analyzedComponents", analysedComponents.toString)
    outTable = outTable.add(this.benchmarkName, "verifiedContracts", verifiedContracts.toString)
    outTable = outTable.add(this.benchmarkName, "distinctContracts", distinctContracts.toString)
    outTable = outTable.add(this.benchmarkName, "collabIterations", collabIterations.toString)
    outTable = outTable.add(this.benchmarkName, "elapsedAnalysisTimes", elapsedAnalysisTimes.mkString(":"))
    outTable = outTable.add(this.benchmarkName, "elapsedConcolicTimes", elapsedConcolicTimes.mkString(":"))
    outTable = outTable.add(this.benchmarkName, "numberOfAssumptions", numberOfAssumptions.toString)
    outTable = outTable.add(this.benchmarkName, "verifiedContractsOverTime", verifiedContractsOverTime.mkString(":"))
    outTable = outTable.add(this.benchmarkName, "violatedAssumptions", violatedAssumptions.toString)

    outTable
  }
}

object CollabBenchmark {
  import maf.language.contracts._
  case class Counter(
      numGuards: Integer = 0,
      numVerifiedGuards: Integer = 0,
      numViolatedguards: Integer = 0,
      numTests: Integer = 0,
      numVerifiedTests: Integer = 0,
      numViolatedTests: Integer = 0,
      numAssumptions: Integer = 0) {
    def combine(other: Counter): Counter =
      Counter(
        numGuards = this.numGuards + other.numGuards,
        numVerifiedGuards = this.numVerifiedGuards + other.numVerifiedGuards,
        numViolatedguards = this.numViolatedguards + other.numViolatedguards,
        numTests = this.numTests + other.numTests,
        numVerifiedTests = this.numVerifiedTests + other.numVerifiedTests,
        numViolatedTests = this.numViolatedTests + other.numViolatedTests,
        numAssumptions = this.numAssumptions + other.numAssumptions
      )
  }

  /**
   * Count the number of guards (verified, unverified or violated),
   * the number of tests associated with these guards (verified, unverified, violated) and the number of assumptions in the AST
   */
  def count(exp: ScExp): Counter = exp match {
    case ScBegin(expressions, _) =>
      expressions
        .map(e => count(e))
        .foldLeft(Counter())((c1, c2) => c1.combine(c2))

    case ScIf(condition, consequent, alternative, idn) =>
      val countCondition = count(condition)
      val countConsequent = count(consequent)
      val countAlternative = count(alternative)

      countCondition
        .combine(countConsequent)
        .combine(countAlternative)

    case ScAnd(exprs, _) =>
      exprs.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))

    case ScOr(exprs, _) =>
      exprs.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))

    case ScLetRec(_, _, body, _) =>
      count(body)

    case ScSet(_, value, _) =>
      count(value)

    case ScFunctionAp(ScIdentifier("make-guard", _), _, _, _) =>
      Counter(numGuards = 1)

    case ScFunctionAp(ScIdentifier("make-verified-guard", _), _, _, _) =>
      Counter(numVerifiedGuards = 1)

    case ScFunctionAp(ScIdentifier("make-violated-guard", _), _, _, _) =>
      Counter(numViolatedguards = 1)

    case ScFunctionAp(operator, operands, _, _) =>
      val countOperator = count(operator)
      val countOperands = operands.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))
      countOperator.combine(countOperands)

    case _: ScValue =>
      Counter()

    case _: ScIdentifier =>
      Counter()

    case ScMon(contract, expression, _, _) =>
      val countContract = count(contract)
      val countExpression = count(expression)
      countContract.combine(countExpression)

    case _: ScOpaque =>
      Counter()

    case ScDependentContract(domains, rangeMaker, _) =>
      val countDomains = domains.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))
      val countRangeMaker = count(rangeMaker)

      countDomains.combine(countRangeMaker)

    case ScFlatContract(expression, _) =>
      count(expression)

    case ScLambda(_, body, _) =>
      count(body)

    case ScProgram(expressions, _) =>
      expressions.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))

    case ScDefine(_, expression, _) =>
      count(expression)

    case ScDefineFn(_, _, body, _) =>
      count(body)

    case ScDefineAnnotatedFn(_, _, contract, expression, _) =>
      count(contract).combine(count(expression))

    case ScAssumed(_, _, _) =>
      Counter(numAssumptions = 1)

    case ScTestVerified(_, _, _) =>
      Counter(numVerifiedTests = 1)

    case _: ScTestViolated =>
      Counter(numViolatedTests = 1)

    case ScTest(_, _, _) =>
      Counter(numTests = 1)

    case _: ScIfGuard =>
      Counter()

    case ScProvideContracts(_, contracts, _) =>
      contracts.map(count).foldLeft(Counter())((c1, c2) => c1.combine(c2))

    case ScCar(pai, _) =>
      count(pai)

    case ScCdr(pai, _) =>
      count(pai)

    case ScNil(_) =>
      Counter()
  }
}

trait CollabBenchmark extends Benchmarks {
  import CollabBenchmark._

  private val allAssumptions: Set[String] = Set("pure", "value", "nondetif", "holds", "nonblame")
  def createAnalysis(program: String): CollaborativeAnalysisJVM = {
    val exp = SCExpCompiler.preludedRead(program)
    new CollaborativeAnalysisJVM(exp)
  }

  def testBenchmarks: List[Benchmark]

  def runAll(out: String): Unit = {
    val results = testBenchmarks.map(runBenchmark)
    val finalTable = results.foldRight(Table.empty[String])(_.addToTable(_))
    val writer = Writer.open(s"$out.csv")

    writer.write(finalTable.toCSVString())
    writer.close()
  }

  def runBenchmark(benchmark: Benchmark): CollabBenchmarkResult = {
    println(s"Running benchmark $benchmark")
    val source = Reader.loadFile(benchmark)
    val exp = SCExpCompiler.preludedRead(source)
    val analysis = createAnalysis(source)
    var analysisTimes: List[Long] = List()
    var concolicTimes: List[Long] = List()
    var verifiedOverTime: List[Int] = List()
    def loop(
        static: Boolean,
        state: AnalysisState,
        t1: Long
      ): Unit = state match {
      case s: Suspended =>
        val t2 = System.nanoTime()
        val elapsedTime = t2 - t1
        if (static) {
          analysisTimes = elapsedTime :: analysisTimes
          verifiedOverTime = verifiedOverTime ++ List(analysis.currentAnalysis.get.verifiedContracts)
        } else {
          concolicTimes = elapsedTime :: concolicTimes
        }

        loop(!static, s.k(s.exp, s.tracker), System.nanoTime())
      case Finished =>
        ()
    }

    val allStart = System.nanoTime()

    // do it with assumptions
    analysis.disable("pure")
    loop(true, analysis.sunspendableAnalyze(exp, Timeout.none), System.nanoTime())

    // do it without assumptions
    val analysisWithoutAssumptions = createAnalysis(source)
    allAssumptions.foreach(analysisWithoutAssumptions.disable(_))
    loop(true, analysisWithoutAssumptions.sunspendableAnalyze(exp, Timeout.none), System.nanoTime())
    val allEnd = System.nanoTime()

    val counts = count(analysis.currentExp.get)
    CollabBenchmarkResult(
      benchmarkName = benchmark,
      elapsedTime = allEnd - allStart,
      analysedComponents = analysisWithoutAssumptions.currentAnalysis.get.analysedComponents,
      distinctContracts = analysis.currentAnalysis.get.distinctContracts,
      verifiedContracts = analysisWithoutAssumptions.currentAnalysis.get.verifiedContracts,
      collabIterations = concolicTimes.size,
      elapsedAnalysisTimes = analysisTimes,
      elapsedConcolicTimes = concolicTimes,
      numberOfAssumptions = counts.numAssumptions,
      verifiedContractsOverTime = verifiedOverTime,
      violatedAssumptions = counts.numViolatedguards,
      verifiedAssumptions = counts.numVerifiedGuards
    )
  }
}
