package maf.cli

import java.io.File

import maf.language.CScheme._
import maf.language.scheme._
import maf.language.scheme.primitives._
import maf.modular._
import maf.modular.scheme._
import maf.modular.scheme.modf._
import maf.modular.scheme.ssmodconc._
import maf.util._
import maf.util.benchmarks._
import maf.language.change.CodeVersion._
import maf.modular.incremental.scheme.AnalysisBuilder._

import scala.concurrent.duration._
import maf.cli.experiments.SchemeAnalyses

object Main {

  def main(args: Array[String]): Unit = test()

  def test(): Unit = {
    val txt = Reader.loadFile("test/R5RS/callcc.scm")
    val prg = CSchemeParser.parse(txt)
    val analysis = new ModAnalysis(prg) with SchemeModFSemantics
                                        with BigStepModFSemantics
                                        with StandardSchemeModFComponents
                                        with SchemePowersetDomain
                                        with SchemeModFNoSensitivity
                                        with LIFOWorklistAlgorithm[SchemeExp] {
      override def intraAnalysis(cmp: Component) = new IntraAnalysis(cmp) with BigStepModFIntra
      override def step(t: Timeout.T) = {
        val cmp = workList.head
        println(cmp)
        super.step(t)
      }
    }
    analysis.analyze()
    //debugClosures(analysis)
    debugResults(analysis, true)
  }

  type SchemeAnalysis = ModAnalysis[SchemeExp] with GlobalStore[SchemeExp]
  def debugResults(machine: SchemeAnalysis, printMore: Boolean = false): Unit =
    machine.store.foreach {
      case (ReturnAddr(cmp, _), result) if cmp == machine.initialComponent || printMore =>
        println(s"$cmp => $result")
      case _ => ()
    }
}

object Run extends App {
  val text = Reader.loadFile("test/R5RS/VUB-projects/railway-control-system.scm")
  val interpreter = new SchemeInterpreter((_, _) => (), true, true)
  val res = interpreter.run(CSchemeUndefiner.undefine(List(SchemePrelude.addPrelude(CSchemeParser.parse(text), Set("newline", "display")))), Timeout.none, New)
  println(res)
}

object Analyze extends App {
  def one(bench: String, timeout: () => Timeout.T): Unit = {
    val text = CSchemeParser.parse(Reader.loadFile(bench))
    val a = new ModAnalysis(text)
      with KKallocModConc
      with SchemeConstantPropagationDomain
      with LIFOWorklistAlgorithm[SchemeExp] {
      val k = 1

      override def intraAnalysis(component: SmallStepModConcComponent) = new IntraAnalysis(component) with KCFAIntra
    }
    val b = new SimpleSchemeModFAnalysis(text)
      with SchemeConstantPropagationDomain
      with SchemeModFCallSiteSensitivity
      with LIFOWorklistAlgorithm[SchemeExp]

    val c = b
    c.analyze(timeout())
    val r = c.finalResult
    c.visited.foreach(println)
    c.deps.foreach(println)
    println(r)
  }

  val bench: List[String] = List(
    //"test/R5RS/SETL/setl-benchmarks/arithmetic.scm"
    "test/DEBUG2.scm"
  )

  bench.foreach({b =>
    try {
      print(b + " => ")
      val t0 = System.currentTimeMillis()
      one(b, () => Timeout.start(Duration(2, MINUTES)))
      val t1 = System.currentTimeMillis()
      println(s"    in ${(t1 - t0)}ms")
    } catch {
      case t: Throwable => println(s"Raised exception.")
        System.err.println(t.getMessage)
        t.printStackTrace()//t.getStackTrace.take(10).foreach(System.err.println)
        System.err.flush()
    }
  })

}

object IncrementalRun extends App {

  def modconcAnalysis(bench: String, timeout: () => Timeout.T): Unit = {
    println(s"***** $bench *****")
    val text = CSchemeParser.parse(Reader.loadFile(bench))
    val a = new IncrementalModConcAnalysis(text)
    a.analyze(timeout())
    val store1 = a.store
    a.updateAnalysis(timeout())
    val store2 = a.store
    store2.keySet.foreach { k =>
      val v1 = store1.getOrElse(k, a.lattice.bottom)
      if (store2(k) != v1)
        println(s"$k: $v1 -> ${store2(k)}")

    }
  }

  def modfAnalysis(bench: String, timeout: () => Timeout.T): Unit = {
    println(s"***** $bench *****")
    val text = CSchemeParser.parse(Reader.loadFile(bench))
    val a = new IncrementalSchemeModFAnalysis(text)
    a.analyze(timeout())
    val store1 = a.store
    a.visited.foreach(println)
    a.deps.foreach(println)
    /*
    a.updateAnalysis(timeout())
    val store2 = a.store
    store2.keySet.foreach { k =>
      val v1 = store1.getOrElse(k, a.lattice.bottom)
      if (store2(k) != v1)
        println(s"$k: $v1 -> ${store2(k)}")
    }
     */
  }

  val modConcbenchmarks: List[String] = List(
   // "test/changes/cscheme/threads/mcarlo2.scm"
    //  "test/changes/cscheme/threads/lastzero.scm"
    //"test/changes/cscheme/threads/sudoku.scm",
    //"test/changes/cscheme/threads/pc.scm",
    //"test/changes/cscheme/threads/stm.scm"
   )
  val    modFbenchmarks: List[String] = List("test/DEBUG.scm")
  val standardTimeout: () => Timeout.T = () => Timeout.start(Duration(2, MINUTES))

  modConcbenchmarks.foreach { bench =>
   // println(bench)
    //for (i <- 1 to 15) {
     // print(Timer.timeOnly({
        modconcAnalysis(bench, standardTimeout)
      //}) + " ")
    //}
  }
  modFbenchmarks.foreach { bench =>
    //println(bench)
    //for (i <- 1 to 15) {
     // print(Timer.timeOnly({
        modfAnalysis(bench, standardTimeout)
     // }) + " ")
    //}
  }
}

object SimpleTimingTest extends App {

  type Analysis = ModAnalysis[SchemeExp] with GlobalStore[SchemeExp]

  def analysis(program: SchemeExp): Analysis = new ModAnalysis(program)
    with KKallocModConc
    with SchemeConstantPropagationDomain
    with LIFOWorklistAlgorithm[SchemeExp] {
    val k = 1
    override def intraAnalysis(component: SmallStepModConcComponent) = new IntraAnalysis(component) with SmallStepIntra with KCFAIntra
  }

  def run(benchmark: String): Unit = {
    System.out.print(benchmark + " ")
    System.out.flush()
    val text = CSchemeParser.parse(Reader.loadFile(benchmark))
    val a = analysis(text)
    val to = Timeout.start(Duration(1, MINUTES))
    val time = Timer.timeOnly(a.analyze(to))
    if (to.reached) {
      System.out.println("timed out.")
    } else {
      System.out.println(s"finished in ${time / 1000000}ms.")
    }
  }

  // Kind of warm-up.
  System.err.println("Warm-up")
  System.err.flush()
  SchemeBenchmarks.other.foreach(run)

  // Actual tests.
 // System.err.println("Run")
 // System.err.flush()
 // SchemeBenchmarks.threads.foreach(run)

  // Just copy-paste for this
  object SchemeBenchmarks {

    def files(dir: File): Array[File] = {
      val lst = dir.listFiles()
      if (lst == null) Array()
      else lst
    }

    def fromFolder(directory: String, exclude: String*): Set[String] = {
      val root = new File(directory)
      val base = root.getAbsolutePath.length - directory.length
      files(root).filter(!_.isDirectory).map(_.getAbsolutePath.substring(base)).toSet -- exclude.map(file => s"$directory/$file")
    }

    lazy val other: Set[String] = Set(
      "test/R5RS/gambit/peval.scm",
      "test/R5RS/gambit/earley.scm", // list->vector
      "test/R5RS/gambit/scheme.scm",
      "test/R5RS/gambit/sboyer.scm",
      "test/R5RS/gambit/nboyer.scm",
    )

    lazy val threads: Set[String] = fromFolder("test/concurrentScheme/threads",
      "abp.scm", // Unbound reference: display-recorded.
      "lastzero2.scm", // Uses let*, but should use something like letrec*?
      "phild.scm", // Unbound reference: bool-top
    )
  }
}
