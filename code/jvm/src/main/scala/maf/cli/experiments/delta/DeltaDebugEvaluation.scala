package maf.cli.experiments.delta

import maf.util.benchmarks.Timer
import maf.util.datastructures.ListOps._
import java.nio.file.*
import java.io.{BufferedReader, File, InputStreamReader}
import java.util.concurrent.*
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.*
import maf.bench.scheme.*
import scala.concurrent.duration.Duration
import maf.language.scheme.interpreter.ConcreteValues._
import maf.util.benchmarks.{Clock, Timeout}
import maf.util.*
import maf.language.scheme.*
import maf.core.*
import java.util.concurrent.TimeoutException
import maf.deltaDebugging.treeDD.SchemeReduce
import maf.deltaDebugging.treeDD.LayeredSchemeReduce
import maf.deltaDebugging.treeDD.transformations.TransformationManager
import maf.lattice.MathOps
import scala.util.Random
import maf.deltaDebugging.treeDD.variants.GTR
import maf.deltaDebugging.treeDD.Reducer
import maf.deltaDebugging.treeDD.IntermediateReducer
import maf.deltaDebugging.treeDD.TimedReducer
import maf.deltaDebugging.treeDD.LambdaOracle
import maf.util.benchmarks.Table
import maf.deltaDebugging.treeDD.transformations.traits.Replacing

trait Instrumenter:
    def instrument(program: SchemeExp): SchemeExp

object NoInstrumentation extends Instrumenter:
    def instrument(program: SchemeExp): SchemeExp = program

class ExternalInterpreter(val executableName: String):
    def run(program: SchemeExp, timeoutSeconds: Int): String =
        // Write the file
        val suffix = Random.nextInt.toString
        //println(s"foo$suffix.scm")
        val w = Writer.open(s"/tmp/foo$suffix.scm")
        Writer.write(w, "(define (char->string c) (list->string (list c)))\n(define (assert x) #t)" + program.toString)
        Writer.close(w)
        // Run the executable on the file with a timeout
        val p = Runtime.getRuntime().nn.exec(executableName + s" /tmp/foo$suffix.scm").nn
        val output = new BufferedReader(new InputStreamReader(p.getInputStream()))
        if (!p.waitFor(timeoutSeconds, TimeUnit.SECONDS)) then
            p.destroy()
            throw new TimeoutException("Interpreter ran for too long")
        else if p.exitValue != 0 then
            val errorReader = new BufferedReader(new InputStreamReader(p.getErrorStream()))
            val error = LazyList.continually(errorReader.readLine()).takeWhile(_ != null).mkString("\n")
            throw new Exception(error)
        else
            val result = LazyList.continually(output.readLine()).takeWhile(_ != null).mkString("\n")
            // println(s"Result size: ${result.length}")
            result

trait Disagreement:
    val program: String
    def dump(outDir: String): Unit

case class OutputDisagreement(val program: String, val firstOutput: String, val secondOutput: String) extends Disagreement:
    def dump(outDir: String): Unit =
        //println(s"${program}: different output (see $outDir for details)")
        val programName = program.replaceAll("/", "-").nn
        val w1 = Writer.open(s"$outDir/$programName.first")
        Writer.write(w1, firstOutput)
        Writer.close(w1)
        val w2 = Writer.open(s"$outDir/$programName.second")
        Writer.write(w2, secondOutput)
        Writer.close(w2)
case class TimeoutDisagreement(val program: String, val firstTimesOut: Boolean) extends Disagreement:
    def dump(outDir: String): Unit =
        val desc = if firstTimesOut then "first" else "second"
//println(s"${program}: ${desc} times out")
case class CrashDisagreement(val program: String, val error: String) extends Disagreement:
    def dump(outDir: String): Unit =
        //println(s"${program}: ${error.take(10)} (see $outDir for details)")
        val programName = program.replaceAll("/", "-").nn
        val w = Writer.open(s"$outDir/$programName.error")
        Writer.writeln(w, error)
        Writer.close(w)

trait InterpreterComparison extends Instrumenter:
    def instrument(program: SchemeExp): SchemeExp = program

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement]

    def isTimeout(exc: Throwable): Boolean = exc match
        case _: TimeoutException   => true
        case _: StackOverflowError => true
        case _                     => false

    def compareResults[A](
        name: String,
        first: Either[Throwable, A],
        second: Either[Throwable, A],
        cmp: (A, A) => Option[Disagreement]
      ): Option[Disagreement] =
        (first, second) match
            case (Left(exc1), Left(exc2)) if isTimeout(exc1) && isTimeout(exc2) => None
            case (Right(v1), Right(v2))                                         => cmp(v1, v2)
            // TODO(bram): we should not always ignore timeout disagreements, but here we do
            // so we can implement the bounded execution strategy without satisfying the oracle
            case (Left(exc1), _: Right[_, _]) if isTimeout(exc1) => None // Some(TimeoutDisagreement(name, true))
            case (_: Right[_, _], Left(exc2)) if isTimeout(exc2) => None // Some(TimeoutDisagreement(name, false))
            // TODO(bram): fix: Ignore uninitialized variables for now since these cause spurious errors leading to extremely small programs in Perses (such as (letrec ((_0 _0)) _0)
            case (Left(ProgramError(maf.core.UninitialisedVariableError(_))), Right(_)) => None
            case (Left(exc), _: Right[_, _]) => Some(CrashDisagreement(name, exc.toString() + "\n" + exc.getStackTrace().nn.mkString("\n")))
            case (_: Right[_, _], Left(exc)) => Some(CrashDisagreement(name, exc.toString() + "\n" + exc.getStackTrace().nn.mkString("\n")))
            case (Left(exc1), Left(exc2))    =>
                // println(s"!!! Both crashed, this is likely an invalid benchmark ($name)")
                //exc1.printStackTrace()
                //exc2.printStackTrace()
                val err1 = exc1.getStackTrace().nn.mkString("\n")
                val err2 = exc2.getStackTrace().nn.mkString("\n")
                // Some(CrashDisagreement(name, s"Both crashed! $exc1 and $exc2 \n$err1\n$err2"))
                // TODO: we don't want to keep this as disagreement during DD phase
                None

    /* Remove unique part of the address, to keep only its identity */
    def strip(v: ConcreteValues.Value): ConcreteValues.Value =
        import ConcreteValues.Value._
        v match
            case Clo(lambda, env)          => Clo(lambda, env.map((name, addr) => (name, (-1, addr._2))))
            case Pointer((_, identity))    => Pointer((-1, identity))
            case Cons(car, cdr)            => Cons(strip(car), strip(cdr))
            case Vector(size, elems, init) => Vector(size, elems.map((idx, value) => (idx, strip(value))), strip(init))
            // We represent input and output port by their string representation, because they will never be equal
            case InputPort(port)  => Str(v.toString)
            case OutputPort(port) => Str(v.toString)
            case _                => v

class PrintBasedInterpreterComparison extends InterpreterComparison:
    val io = new PrintIO()
    val interpreter1 = new ExternalInterpreter("guile")
    val interpreter2 = new CountingSchemeInterpreter((_, _) => (), io)
    val timeoutSeconds: Int = 30

    def runInternalInterpreter(program: SchemeExp): Either[Throwable, String] =
        try
            //println("Running internal")
            interpreter2.run(program, Timeout.start(Duration(timeoutSeconds, "seconds")))
            //println("Done running internal")
            val output = io.getAndClearOutput()
            val suffix = Random.nextInt.toString
            Writer.dump(s"/tmp/foo$suffix.scm", program.toString)
            // println(s"Internal output (program in foo${suffix}.scm) length: ${output.length}")
            Right(output)
        catch
            case exc: Throwable =>
                io.getAndClearOutput()
                Left(exc)

    def runExternalInterpreter(program: SchemeExp): Either[Throwable, String] =
        //println("Running external")
        val res =
            try Right(interpreter1.run(program, timeoutSeconds))
            catch case exc: Throwable => Left(exc)
        //println("Done running external")
        res

    def processOutput(v: String): String =
        // We want to get rid of extra newlines (hence we trim)
        // and to unify how procedures are represented.
        // We can't deal with procedures in their .toDisplayedString method properly, so we just replace them wherever possible
        // We print a procedure as e.g., #<procedure:dispatch> while guile prints them as #<procedure dispatch (msg args)>
        v.trim()
            .nn
            .replaceAll("#<procedure \\w+ at .*>", "#<procedure>")
            .nn // from guile, e.g., #<procedure 5602d43a32e8 at <unknown port>:2:0 (x)>
            .replaceAll("#<procedure ([^ ]+) .*\\)>", "#<procedure>")
            .nn // from guile, e.g., #<procedure foo (x)>
            .replaceAll("#<procedure:λ@[0-9:]+ \\(\\)>", "#<procedure>")
            .nn // from MAF, e.g., #<procedure:λ@639:6 ()>
            .replaceAll("#<procedure:([^)]+) \\(\\)>", "#<procedure>")
            .nn // from MAF, e.g., #<procedure:dispatch ()>
            .replaceAll("#<primitive:([^>]+)>", "#<procedure>")
            .nn // from MAF, e.g., #<primitive:cons>
            .replaceAll("#<input-port:file:([^>]+)>", "#<input $1>")
            .nn
            .replaceAll("#<output-port:file:([^>]+)>", "#<output $1>")
            .nn
            .replaceAll("#<input: ([^>]+) [0-9]+>", "#<input $1>")
            .nn
            .replaceAll("#<output: ([^>]+) [0-9]+>", "#<output $1>")
            .nn

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
        compareResults(
          name,
          runInternalInterpreter(program),
          runExternalInterpreter(program),
          (v1: String, v2: String) =>
              println(s"comparing output ${processOutput(v1)} with ${processOutput(v2)}")
              if processOutput(v1) == processOutput(v2) then None else Some(OutputDisagreement(name, processOutput(v1), processOutput(v2)))
        )

class InstrumentationBasedInterpreterComparison extends PrintBasedInterpreterComparison:
    override def instrument(program: SchemeExp): SchemeExp = program match {
        case SchemeLambda(name, args, body, annotation, idn) =>
            SchemeLambda(name, args, body.map(instrument), annotation, idn)
        case SchemeVarArgLambda(name, args, vararg, body, annotation, idn) =>
            SchemeVarArgLambda(name, args, vararg, body.map(instrument), annotation, idn)
        case SchemeFuncall(f, args, idn) =>
            SchemeFuncall(SchemeVar(Identifier("__log", idn)), List(SchemeFuncall(instrument(f), args.map(instrument), idn)), idn)
        case SchemeIf(cond, cons, alt, idn) =>
            SchemeIf(instrument(cond), instrument(cons), instrument(alt), idn)
        case SchemeLet(bindings, body, idn) =>
            SchemeLet(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
        case SchemeLetStar(bindings, body, idn) =>
            SchemeLetStar(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
        case SchemeLetrec(bindings, body, idn) =>
            SchemeLetrec(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
        case SchemeSet(variable, value, idn) =>
            SchemeSet(variable, instrument(value), idn)
        case SchemeSetLex(variable, lexAddr, value, idn) =>
            SchemeSetLex(variable, lexAddr, instrument(value), idn)
        case SchemeBegin(exps, idn) =>
            SchemeBegin(exps.map(instrument), idn)
        case SchemeDefineVariable(name, value, idn) =>
            SchemeDefineVariable(name, instrument(value), idn)
        case SchemeAssert(exp, idn) =>
            SchemeAssert(instrument(exp), idn)
        case _ => program
    }

class ReturnValueInterpreterComparison extends InterpreterComparison:
    val interpreter1: BaseSchemeInterpreter[_] = new CPSSchemeInterpreter();
    val interpreter2: BaseSchemeInterpreter[_] = new SchemeInterpreter();
    val timeout: Duration = Duration(300, "seconds")

    def runInterpreter(interpreter: BaseSchemeInterpreter[_], program: SchemeExp): Either[Throwable, Value] =
        MathOps.randomGenerator = new Random(42)
        try Right(interpreter.run(program, Timeout.start(timeout)))
        catch case exc: Throwable => Left(exc)

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
        compareResults(
          name,
          runInterpreter(interpreter1, program),
          runInterpreter(interpreter2, program),
          (v1: Value, v2: Value) => if (strip(v1) == strip(v2)) then None else Some(OutputDisagreement(name, v1.toString, v2.toString))
        )

class CallbackBasedInterpreterComparison extends ReturnValueInterpreterComparison:

    def generateCallback: ((Identity, ConcreteValues.Value) => Unit, () => Map[Identity, Set[ConcreteValues.Value]]) =
        var seen: Map[Identity, Set[ConcreteValues.Value]] = Map()
        ((id, v) => seen = seen + (id -> (seen.get(id).getOrElse(Set()) + v)), () => seen)

    def findDifference(m1: Map[Identity, Set[Value]], m2: Map[Identity, Set[Value]]): Option[(Identity, String, String)] =
        for (k1, v1) <- m1 do
            val v2: Option[Set[ConcreteValues.Value]] = m2.get(k1)
            if v2.isDefined == false || v2.get.map(strip) != v1.map(strip) then return Some((k1, v1.toString, v2.map(_.toString).getOrElse("absent")))
        None

    override def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
        val callback1 = generateCallback
        val interpreter1 = new CPSSchemeInterpreter(callback1._1)
        val callback2 = generateCallback
        val interpreter2 = new SchemeInterpreter(callback2._1)
        compareResults(
          name,
          runInterpreter(interpreter1, program),
          runInterpreter(interpreter2, program),
          (v1, v2) =>
              findDifference(callback1._2(), callback2._2())
                  .orElse(findDifference(callback2._2(), callback1._2()))
                  .map(diff => OutputDisagreement(name, s"${diff._1}: ${diff._2}", s"${diff._1}: ${diff._3}"))
        )

object ProgramLoader:
    def loadProgram(path: String, instrumenter: Instrumenter, doInstrument: Boolean = true, doUndefine: Boolean = true): SchemeExp =
        val content = Reader.loadFile(path)
        val parsed = SchemeParser.parse(content)
        val instrumented = if doInstrument then parsed.map(instrumenter.instrument) else parsed
        val preluded = SchemePrelude.addPrelude(instrumented, incl = Set("__log"))
        val undefined = SchemeParser.undefine(preluded)
        undefined

case class ExecutionStats(numberOfSteps: Long):
    def asEnvironmentString: String =
        s"""|NUMBER_OF_STEPS=$numberOfSteps
    """.stripMargin

/** This applies differential testing to two interpreters. Used to find programs which have different interpretation between the two interpreters */
class DifferentialTesting(
    comparison: PrintBasedInterpreterComparison,
    reporter: DifferentialTestingReporter,
    benchmarks: Set[String],
    doInstrument: Boolean = true,
    doUndefine: Boolean = true):
    def bounds: ExecutionStats =
        ExecutionStats(comparison.interpreter2.getEvalSteps())

    def onBenchmark(name: String): Unit =
        //println(s"Running on $name")
        val program = ProgramLoader.loadProgram(name, comparison, true, doUndefine)
        println(s"DifferentialTesting onBenchmark: $program")
        // setup max number of steps based on feedback of previously selected program
        println(sys.env)
        if sys.env.contains("NUMBER_OF_STEPS") then
            println("Integrated feedback")
            comparison.interpreter2.maxEvalSteps = sys.env.get("NUMBER_OF_STEPS").get.toLong

        comparison.differenceOn(name, program) match {
            case Some(disagreement) =>
                println(s"Disagreement on $name: $disagreement")
                reporter.addDisagreement(disagreement)
            case _ => ()
        }

    def main(args: Array[String]): Unit =
        benchmarks.foreach(onBenchmark)
        reporter.report()

//object DifferentialTestingExternal extends DifferentialTesting(new InstrumentationBasedInterpreterComparison)
//object DifferentialTestingInternal extends DifferentialTesting(new CallbackBasedInterpreterComparison)

/** Reports disagreements between two interpreters */
class DifferentialTestingReporter:
    protected var disagreements: List[Disagreement] = List()

    /**
     * Add a disagreement to the list of disagreements
     *
     * @param disagreement
     *   the disagreement to add
     */
    def addDisagreement(disagreement: Disagreement): Unit =
        disagreements = disagreement :: disagreements

    /** Returns true if the list of disagreements is non-empty */
    def hasDisagreement: Boolean = disagreements.nonEmpty

    /** Report on the disagreements */
    def report(): Unit = ()

class ConsoleDifferentialTestingReporter extends DifferentialTestingReporter:
    override def report(): Unit =
        // println(s"I ran ${benchmarks.size} benchmarks and found ${disagreements.length} disagreements")
        val outputDisagreements = disagreements.filter(_.isInstanceOf[OutputDisagreement])
        //println(s"Output disagreements: ${outputDisagreements.length} (raw outputs in in /tmp/out)")
        outputDisagreements.foreach(_.dump("/tmp/out/"))
        val timeoutDisagreements = disagreements.filter(_.isInstanceOf[TimeoutDisagreement])
        //println(s"Timeout disagreements: ${timeoutDisagreements.length}")
        timeoutDisagreements.foreach(_.dump("/tmp/out/"))
        val crashDisagreements = disagreements.filter(_.isInstanceOf[CrashDisagreement])
        //println(s"Crash disagreements:: ${crashDisagreements.length}")
        crashDisagreements.foreach(_.dump("/tmp/out/"))

// Black-box delta debugging
abstract class DeltaDebug(comparison: InterpreterComparison):

    val benchmarks: Set[String]

    def deadCodeRemover(newCandidate: SchemeExp): Option[SchemeExp] =
        None // TODO: is there anything we can do here?

    def oracle(program: SchemeExp): Boolean =
        val instrumented = comparison.instrument(program)
        val preluded = SchemePrelude.addPrelude(List(instrumented), incl = Set("assert", "__log", "*seed*", "random"))
        val programToRun = SchemeParser.undefine(preluded)
        comparison.differenceOn("foo", programToRun) match
            case Some(disagreement) =>
                Writer.dump("/tmp/disagreement.scm", program.toString)
                disagreement.dump("/tmp/out/")
                println(s"Disagreement on: ${program.toString().take(100)}: ${disagreement.toString().take(150)}")
                true
            case None =>
                println(s"Agreement on: ${program.toString().take(20)}...")
                false

    def reduce(program: SchemeExp): SchemeExp =
        val reducer = new SchemeReduce(program, identity, TransformationManager.allTransformations, Some(deadCodeRemover)) with LambdaOracle(oracle)
        reducer.reduce()

    def onBenchmark(path: String): Unit =
        val content = Reader.loadFile(path)
        val parsed = SchemeParser.parse(content)
        // val instrumented = parsed.map(instrumenter.instrument)
        // val preluded = SchemePrelude.addPrelude(instrumented, incl = Set("assert", "__log"))
        val program = SchemeParser.undefine(parsed)
        val reduced = reduce(program)
    //println(s"========== ${path}")
    //println(reduced)
    //println("GTR total transformation count: " + TransformationManager.allTransformations.map(_.getHits).fold(0)(_ + _))

    def main(args: Array[String]): Unit =
        benchmarks.foreach(onBenchmark)

object DeltaDebugInternal extends DeltaDebug(new CallbackBasedInterpreterComparison):
    val benchmarks: Set[String] = Set() // No disagreement found!

object DeltaDebugExternal extends DeltaDebug(new InstrumentationBasedInterpreterComparison):
    val benchmarks: Set[String] = Set(
      // These are all the ones that yield differences worth investigating
      // Different order of evaluation of let bindings?
      // "test/R5RS/gabriel/dderiv.scm", // (let ((arg ((lambda unique_args_382 #f) 5 '())) (result ((lambda unique_args_374 '()) 0 '()))) (equal? '() result))
      // "test/R5RS/scp1/cashdesk-counter.scm", // (letrec ((teller ((lambda unique_args_295 #f))) (_0 ((lambda unique_args_287 '()) 'toets)) (_3 teller)) '())
      // "test/R5RS/scp1/twitter.scm", // (letrec ((res1 ((lambda unique_args_463 #f) 'username)) (_0 ((lambda unique_args_455 '()) 'output)) (_6 res1)) '())
      //
      // Bug: (eq?) and (eq? x) are valid in guile, but not in MAF. It's guile that deviates from R5RS
      // "test/R5RS/various/values.scm", // (letrec ((string->number eq?) (_1 (string->number))) '())
      //
      // Bug: letrec can reference later bindings in the same letrec, does not work in MAF
      // It's actually guile that violates R5RS, as it states: "One restriction on letrec is very important: it must be possible to evaluate each <init> without assigning or referring to the value of any <variable>. If this restriction is violated, then it is an error. The restriction is necessary because Scheme passes arguments by value rather than by name. In the most common uses of letrec, all the <init>s are lambda expressions and the restriction is satisfied automatically. "
      "test/R5RS/WeiChenRompf2019/rsa.scm", // (letrec ((is-legal-public-exponent? e) (e 7)) '())
      //
      // Same bug: guile allows circular bindings, e.g., (letrec ((_0 _0)) _0), where _0 will have an unspecified value.
      // "test/R5RS/scp1/parking-counter.scm",
      // "test/R5RS/scp1/tree-with-branches.scm",
      // "test/R5RS/various/eta.scm",
      // "test/R5RS/various/four-in-a-row.scm",
      // "test/R5RS/various/grid.scm",

      // The rest are due to either IO input (cat, wc, tail), or fractions (calc-e-and-cos, simpson-integral, third-root)
      // Note that there are some high variations due to missing fractions in MAF! For example on simpson-integral
      //"test/R5RS/scp1/simpson-integral.scm",
      // "test/R5RS/scp1/third-root.scm",
      //
      // Other bug found in the process: (eq? x) should return #t, but fails in MAF
    )

object Interpreter:

    def main(args: Array[String]): Unit =
        val io = new PrintIO()
        val interpreter = new SchemeInterpreter((_, _) => (), io)
        val timeoutSeconds: Int = 30

        val text =
            "(letrec ((<= (lambda (x y)  (let ((__or_res (< x y))) (if __or_res __or_res (let ((__or_res (= x y))) (if __or_res __or_res #f)))))) (not (lambda (x) (if x #f #t))) (abs (lambda (x)  (if (< x 0) (- 0 x) x))) (string=? (lambda (s1 s2)   (if (= (string-length s1) (string-length s2)) ((letrec ((loop (lambda (i) (if (< i 0) #t (if (char=? (string-ref s1 i) (string-ref s2 i)) (loop (- i 1)) #f))))) loop) (- (string-length s1) 1)) #f))) (> (lambda (x y)  (not (<= x y)))) (__log (lambda (x) (display x) (newline) x))  (equal? (lambda (a b) (let ((__or_res (eq? a b))) (if __or_res __or_res (let ((__or_res (if (null? a) (null? b) #f))) (if __or_res __or_res (let ((__or_res (if (string? a) (if (string? b) (string=? a b) #f) #f))) (if __or_res __or_res (let ((__or_res (if (pair? a) (if (pair? b) (if (equal? (car a) (car b)) (equal? (cdr a) (cdr b)) #f) #f) #f))) (if __or_res __or_res (if (vector? a) (if (vector? b) (let ((n (vector-length a))) (if (= (vector-length b) n) (letrec ((loop (lambda (i) (let ((__or_res (= i n))) (if __or_res __or_res (if (equal? (vector-ref a i) (vector-ref b i)) (loop (+ i 1)) #f)))))) (loop 0)) #f)) #f) #f))))))))))) (random (lambda (n) (let ((rand (lambda () (let* ((hi (quotient *seed* 127773)) (lo (modulo *seed* 127773)) (test (- (* 16807 lo) (* 2836 hi)))) (if (> test 0) (set! *seed* test) (set! *seed* (+ test 2147483647))) *seed*)))) (modulo (abs (rand)) n)))) (*seed* 1) (_0 (let ((arg (__log ((lambda unique_args_382 #f) 5 '()))) (result (__log ((lambda unique_args_374 '()) 0 '())))) (__log (equal? '() result))))) _0)"
        // val text = "(let ((x (display 1)) (y (display 2))) (display 3))"
        val program = SchemeParser.parse(text)(0)
        interpreter.run(program, Timeout.start(Duration(timeoutSeconds, "seconds")))
        val output = io.getAndClearOutput()
///println(output)

case class ReductionData(
    benchmark: String,
    origSize: Int,
    reducedSize: Int,
    reductionPercentage: Double,
    reductionTime: Long,
    oracleInvocations: Int,
    oracleEvolution: List[Long],
    sizeEvolution: List[Int]):
    def dump(): Unit =
        println(
          s"Reduction on ${benchmark} of size ${origSize}, reduced to ${reducedSize} (${reductionPercentage * 100}%) in ${reductionTime / 1e3}s with ${oracleInvocations} invocations"
        )

trait ComparisonReducer extends Reducer[SchemeExp]:
    val comparison: PrintBasedInterpreterComparison
    protected def hasDifferenceOn(programName: String, program: SchemeExp): Option[Disagreement] =
        comparison.differenceOn(programName, program)

    private var cache: Map[SchemeExp, Boolean] = Map()

    def inCache(exp: SchemeExp)(blk: => Boolean): Boolean =
        val r = cache.get(exp).getOrElse(blk)
        cache = cache + (exp -> r)
        r

    def invokeOracle(program: SchemeExp): Boolean = {
        inCache(program) {
            // We don't want the delta debugger to consider the instrumented program,
            // but only use instrumentation for comparison, hence we need to instrument now and not earlier.
            // (We could instrument earlier, but we could then remove parts of the instrumentation and have odd results, possibly
            val instrumented = comparison.instrument(program)
            val preluded = SchemePrelude.addPrelude(List(instrumented), incl = Set("assert", "__log", "*seed*", "random"))
            val programToRun = SchemeParser.undefine(preluded)
            // If we introduced any undefined variables (e.g., by removing a def), this will not work so we skip this one
            // TODO if !programToRun.findUndefinedVariables().isEmpty then return false
            //println("Computing difference")
            this.hasDifferenceOn("foo", programToRun).isDefined
        }
    }

trait EvalStrategy(val comparison: PrintBasedInterpreterComparison)
    extends Reducer[SchemeExp],
      ComparisonReducer,
      TimedReducer[SchemeExp],
      IntermediateReducer[SchemeExp]:

    def eval(program: SchemeExp, name: String): ReductionData =
        val startTime = System.currentTimeMillis()

        val reduced = reduce()
        println(reduced)
        val endTime = System.currentTimeMillis()
        val totalReductionTime = endTime - startTime

        ReductionData(
          benchmark = name,
          origSize = program.size,
          reducedSize = reduced.size,
          reductionTime = totalReductionTime,
          reductionPercentage = 1 - (reduced.size.toDouble / program.size),
          oracleInvocations = oracleEvolution.size,
          oracleEvolution = oracleEvolution.reverse,
          sizeEvolution = expressionEvolution.map(_.size).reverse
        )

class GTREval(program: SchemeExp, comparison: PrintBasedInterpreterComparison)
    extends GTR(program, TransformationManager.genericTransformations)
    with EvalStrategy(comparison)

class SchemeReduceEval(tree: SchemeExp, comparison: PrintBasedInterpreterComparison)
    extends SchemeReduce(tree, identity, Random.shuffle(TransformationManager.allTransformations))
    with EvalStrategy(comparison)

// TODO: transformation order may not be relevant for our set of benchmarks anymore, may need to recompute it
class OrderedSchemeReduceEval(tree: SchemeExp, comparison: PrintBasedInterpreterComparison)
    extends SchemeReduce(tree, identity, TransformationManager.allTransformations)
    with EvalStrategy(comparison)

class LayeredSchemeReduceEval(tree: SchemeExp, comparison: PrintBasedInterpreterComparison)
    extends LayeredSchemeReduce(tree, identity, Random.shuffle(TransformationManager.allTransformations), 7)
    with EvalStrategy(comparison)

trait CountingOracle extends ComparisonReducer:
    override protected def hasDifferenceOn(programName: String, program: SchemeExp) =
        // We ignore timeout disagreements since we deliberately made
        // the interpreter timeout.
        // TODO: still compare outputs if there is a timeout disagreement?
        val disagreement = super.hasDifferenceOn(programName, program)
        disagreement match
            case Some(TimeoutDisagreement(_, _)) => None
            case _                               => disagreement
    override def invokeOracle(program: SchemeExp): Boolean =
        val result = super.invokeOracle(program)
        if result then comparison.interpreter2.maxEvalSteps = comparison.interpreter2.getEvalSteps()
        result

// Uses OrderedSchemeReduce + counting interpreter
class CountingSchemeReduceEval(tree: SchemeExp, comparison: PrintBasedInterpreterComparison)
    extends SchemeReduce(tree, identity, TransformationManager.allTransformations)
    with CountingOracle
    with EvalStrategy(comparison)

class RemoveExpensiveFunctionsEval(tree: SchemeExp, comparison: PrintBasedInterpreterComparison) extends OrderedSchemeReduceEval(tree, comparison):
    val timeoutSeconds = 30

    /** Number of expensive functions to remove (max) */
    private val numberToRemove = 5

    /** Number of candidates to consider for each function (max) */
    private val numberOfCandidates = 3

    def run(comparison: PrintBasedInterpreterComparison, program: SchemeExp): Unit =
        val instrumented = comparison.instrument(program)
        val preluded = SchemePrelude.addPrelude(List(instrumented), incl = Set("assert", "__log", "*seed*", "random"))
        val programToRun = SchemeParser.undefine(preluded)
        comparison.interpreter2.run(programToRun, Timeout.start(Duration(timeoutSeconds, "seconds")))

    override def reduce(program: SchemeExp) = {
        // TODO: count time spent in preprocessing step
        // println("Removing lambdas...")
        val preprocessed =
            try
                run(comparison, program)
                // println("Program executed successfully")
                preprocess(comparison, program, comparison.interpreter2.stepsSpent)
            // println("-----> Done preprocessing")
            catch { case _ => program }

        super.reduce(preprocessed)
    }

    def preprocess(comparison: PrintBasedInterpreterComparison, program: SchemeExp, stepsSpent: Map[SchemeLambda, Int]): SchemeExp = {
        val toRemove = stepsSpent.toList.sortBy(kv => -kv._2).take(numberToRemove)
        // println(program)
        //println(s"To remove: ${toRemove.size}")
        var reducedProgram = program
        for (lambda <- toRemove) {
            // println(s"Removing ${lambda._1.name.get.toString().take(100)}")
            removeLambda(comparison, reducedProgram, lambda._1) match
                case Some(p) => reducedProgram = p
                case _       => ()
        }
        println(s"[expensive-functions] Program original size: ${program.size}, reduced size ${reducedProgram.size}")
        reducedProgram
    }

    def removeLambda(
        comparison: PrintBasedInterpreterComparison,
        program: SchemeExp,
        lambda: SchemeLambda
      ): Option[SchemeExp] = {
        try
            // Try removing the lambda, this will also removing any bindings
            // in let expressions for those lambda's
            val programWithoutLambda = program.deleteChildren {
                case exp @ SchemeLambda(_, _, _, _, idn) =>
                    exp.idn == lambda.idn
                case _ => false
            }.get

            // Now try to delete all calls to the now undefined function
            // TODO: does this transformation take scoping into account?
            val candidates = Replacing
                .replaceWithAllValues(programWithoutLambda,
                                      {
                                          case SchemeFuncall(f: SchemeVarExp, _, _) =>
                                              lambda.name.map(_ == f.id.name).getOrElse(false)
                                          case _ => false
                                      }
                )

            // use only those programs that have no undefined variagbles
            // and invoke the oracle on them to find a suitable candidate
            candidates
                .filter(c => (c.findUndefinedVariables().map(_.name).toSet -- SchemePrelude.primDefs.keySet).isEmpty)
                .take(numberOfCandidates)
                .find(invokeOracle)

        catch _ =>
            println("Unable to remove it")
            None // Execution failed, this one can't be removed
    }

/**
 * Entrypoint for testing the property, used by Perses.
 *
 * Perses calls the property script with the filename of the file originally reduced. It does not provide the filename as an argument to the property
 * script. As such we assume that the filename is always `program.rkt` in the current directory.
 */
object PersesProperty:
    def runProperty(filename: String, instrument: Boolean = true, undefine: Boolean = true): Boolean =
        val benchmarks = Set(filename)

        val reporter = new ConsoleDifferentialTestingReporter()
        val tester = new DifferentialTesting(new InstrumentationBasedInterpreterComparison(), reporter, benchmarks, instrument, undefine)
        tester.main(Array())
        // Output bounds
        System.err.nn.println(tester.bounds.asEnvironmentString)

        // output the results of differential testing
        reporter.hasDisagreement

    def main(args: Array[String]): Unit =
        if !File("program.rkt").exists() then
            println("No file named 'program.rkt' found in the current directory")
            sys.exit(1)

        if runProperty("program.rkt", instrument = false, undefine = false) then sys.exit(0)
        else sys.exit(1)

/** Entrypoint for executing the Perses program reducer, parses its output for statistics that we use during the evaluation */
object Perses:
    private val PERSES_PATH_JAR = sys.env("PERSES_PATH")
    private val SCHEME_LANG_PATH_JAR = sys.env("PERSES_LANGUAGE_PATH")
    private val TEST_SCRIPT_JAR = sys.env("PERSES_PROPERTY_JAR")

    private val testScript = s"""|#!/bin/bash
    |java -jar ${TEST_SCRIPT_JAR}
    """.stripMargin

    /** Parses the file, runs the undefined over it and outputs the resulting tree as a string */
    def parseUndefine(path: String): SchemeExp =
        val content = Reader.loadFile(path)
        val parsed = SchemeParser.parse(content)
        SchemeParser.undefine(parsed)

    def testFile(filename: String, nth: Int): Option[Evaluation.EvaluationResult] =
        import scala.sys.process._
        val persesInput =
            // first test whether there is a disagreement on the file
            // to begin with
            if !PersesProperty.runProperty(filename) then
                println(s"No disagreement for $filename found, skipping...")
                return None

        // output path for perses
        val outputPath = "out/output-perses-" + Clock.nowStr()
        Files.createDirectories(Paths.get(outputPath))
        // temp path is used for storing files needed for the reduction,
        val tempPath = "out/workdir-" + Clock.nowStr()
        Files.createDirectories(Paths.get(tempPath))
        val propPath = tempPath + "/r.sh"
        // Run the undefiner on the file and write to tempPath
        val contents = parseUndefine(filename)
        var w = Writer.open(tempPath + "/program.rkt")
        Writer.write(w, contents.toString)
        Writer.close(w)

        // copy the test script to the working directory
        w = Writer.open(tempPath + "/r.sh")
        Writer.write(w, testScript)
        Writer.close(w)

        // mark it as executable
        FileOps.markExecutable(propPath)

        val cmd = Seq(
          "java",
          "-jar",
          PERSES_PATH_JAR,
          "--input-file",
          File(tempPath + "/program.rkt").getAbsolutePath().nn,
          "--test-script",
          File(propPath).getAbsolutePath().nn,
          "--language-ext-jars",
          SCHEME_LANG_PATH_JAR,
          "--output-dir",
          File(outputPath).getAbsolutePath().nn,
          "--progress-dump-file",
          "output.dump",
          "--threads",
          "1",
          "--maf-dump-file",
          File(outputPath + "/stats.csv").getAbsolutePath().nn,
          "--whitebox"
        )
        println(cmd)

        val output = Process(cmd, new File(tempPath)).!!

        // read and parse program from output directory
        val outputProgram = parseUndefine(outputPath + "/program.rkt")

        // parse the output statistics
        val outstats: List[String] = Reader.loadFile(outputPath + "/stats.csv").strip.nn.split(";").nn.map(_.nn).toList
        val oracleInvocations = outstats(1).toInt
        val reductionTime = outstats(2).toLong
        val beforeProgramSize = outstats(3).toInt
        val afterProgramSize = outstats(4).toInt
        val oracleEvolution = outstats(5).split(":").nn.toList.map(_.nn.toLong)

        val d = ReductionData(
          benchmark = filename,
          origSize = beforeProgramSize,
          reducedSize = afterProgramSize,
          reductionPercentage = beforeProgramSize.toDouble / afterProgramSize.toDouble,
          reductionTime = reductionTime,
          oracleInvocations = oracleInvocations,
          oracleEvolution = oracleEvolution,
          sizeEvolution = List()
        )

        Some(Evaluation.EvaluationResult("perses", filename, d, nth))

    def main(args: Array[String]): Unit =
        val results: List[Evaluation.EvaluationResult] = Evaluation.benchmarks
            //.take(1)
            .toList
            .flatMap(benchmark => {
                try
                    println(s"Running perses on $benchmark")
                    val r = testFile(benchmark, 0)
                    println(s"Perses execution on $benchmark successful")
                    r
                catch {
                    case e =>
                        println(s"Failed execution on $benchmark with exception $e")
                        e.printStackTrace()
                        None
                }
            })

        val t = results.foldLeft(Table.empty[String])((table, o) => o.addToTable(table))
        val w = Writer.openTimeStamped("output/perses-output.csv")
        Writer.write(w, t.toCSVString())
        Writer.close(w)

/** The evaluation combines strategies with benchmark programs and writes the results ot a single CSV file */
object Evaluation:
    val REPEAT_BENCHMARK_TIMES = 0

    case class EvaluationResult(strategyName: String, benchmarkName: String, result: ReductionData, nth: Int):
        private val rowName: String = strategyName + ":" + benchmarkName + ":" + nth
        def addToTable(table: Table[String]): Table[String] =
            table
                .add(rowName, "origSize", result.origSize.toString)
                .add(rowName, "reducedSize", result.reducedSize.toString)
                .add(rowName, "reductionPercentage", result.reductionPercentage.toString)
                .add(rowName, "reductionTime", result.reductionTime.toString)
                .add(rowName, "oracleInvocations", result.oracleInvocations.toString)
                .add(rowName, "oracleEvolution", result.oracleEvolution.map(_.toString).mkString(":"))
                .add(rowName, "sizeEvolution", result.sizeEvolution.map(_.toString).mkString(":"))

    val strategies: List[(SchemeExp, InstrumentationBasedInterpreterComparison) => EvalStrategy] = List(
      OrderedSchemeReduceEval.apply,
      CountingSchemeReduceEval.apply,
      RemoveExpensiveFunctionsEval.apply
    )

    val benchmarks: Set[String] = Set(
      // These are all the ones that yield differences worth investigating
      // Different order of evaluation of let bindings?
      "test/R5RS/gabriel/dderiv.scm", // (let ((arg ((lambda unique_args_382 #f) 5 '())) (result ((lambda unique_args_374 '()) 0 '()))) (equal? '() result))
      //"test/R5RS/scp1/cashdesk-counter.scm", // (letrec ((teller ((lambda unique_args_295 #f))) (_0 ((lambda unique_args_287 '()) 'toets)) (_3 teller)) '())
      //"test/R5RS/scp1/twitter.scm", // (letrec ((res1 ((lambda unique_args_463 #f) 'username)) (_0 ((lambda unique_args_455 '()) 'output)) (_6 res1)) '())
      ////
      //// Bug: (eq?) and (eq? x) are valid in guile, but not in MAF. It's guile that deviates from R5RS
      //"test/R5RS/various/values.scm", // (letrec ((string->number eq?) (_1 (string->number))) '())
      ////
      //// Bug: letrec can reference later bindings in the same letrec, does not work in MAF
      //// It's actually guile that violates R5RS, as it states: "One restriction on letrec is very important: it must be possible to evaluate each <init> without assigning or referring to the value of any <variable>. If this restriction is violated, then it is an error. The restriction is necessary because Scheme passes arguments by value rather than by name. In the most common uses of letrec, all the <init>s are lambda expressions and the restriction is satisfied automatically. "
      //"test/R5RS/WeiChenRompf2019/rsa.scm", // (letrec ((is-legal-public-exponent? e) (e 7)) '())
      ////
      //// Same bug: guile allows circular bindings, e.g., (letrec ((_0 _0)) _0), where _0 will have an unspecified value.
      //"test/R5RS/scp1/parking-counter.scm",
      //"test/R5RS/scp1/tree-with-branches.scm",
      //"test/R5RS/various/eta.scm",
      //"test/R5RS/various/four-in-a-row.scm",
      //"test/R5RS/various/grid.scm",

      //// The rest are due to either IO input (cat, wc, tail), or fractions (calc-e-and-cos, simpson-integral, third-root)
      //// Note that there are some high variations due to missing fractions in MAF! For example on simpson-integral
      //"test/R5RS/scp1/simpson-integral.scm",
      //"test/R5RS/scp1/third-root.scm",
      //
    )

    def onBenchmark(path: String, strategy: (SchemeExp, InstrumentationBasedInterpreterComparison) => EvalStrategy): List[EvaluationResult] =
        (0 to REPEAT_BENCHMARK_TIMES)
            .map((nth) => {
                val content = Reader.loadFile(path)
                val parsed = SchemeParser.parse(content)
                val program = SchemeParser.undefine(parsed)
                val comparison = new InstrumentationBasedInterpreterComparison
                val s = strategy(program, comparison)
                val strategyName = s.getClass.nn.getName.nn
                println(s"[$nth][$path] running with strategy $strategyName")
                val (time, result) = Timer.time(s.eval(program, path))
                println(s"[$nth][$path] took ${time / (1000 * 1000)} ms")
                EvaluationResult(strategyName, path, result, nth)
            })
            .toList

    // TODO: useful from Turgut's code: check that there are no undefined variables in a program (but maybe before running it rather than after!)
    // p.findUndefinedVariables().isEmpty
    // TODO: extend countingDD to also count steps spent in each function (mimic call stack)

    def main(args: Array[String]): Unit =
        val benchmarks = List("test/R5RS/various/grid.scm")
        val results = benchmarks.toList.cartesian(strategies).flatMap(onBenchmark.tupled)
        val table = results.foldLeft(Table.empty[String])((table, result) => result.addToTable(table))
        val w = Writer.openTimeStamped("output/results.csv")
        Writer.write(w, table.toCSVString())
