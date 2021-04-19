package maf.cli.runnables

import scala.io.StdIn.readLine
import maf.modular.contracts.CollaborativeAnalysisJVM
import maf.language.contracts.SCExpCompiler
import maf.concolicbridge.AnalysisState
import maf.concolicbridge.Finished
import maf.language.contracts.Printer
import maf.concolicbridge.Suspended
import maf.util.benchmarks.Timeout
object CollaborativeAnalysis {
  def main(args: Array[String]): Unit = {
    println("Type your code and type :end on a seperate line to start the analysis")
    var code = ""
    var input = readLine()
    while (input != ":end") {
      code += input
      input = readLine()
    }

    val exp = SCExpCompiler.read(code)
    val analysis = new CollaborativeAnalysisJVM(exp)

    val allAssumptions = List("pure", "value", "nondetif", "holds", "nonblame")
    println("Which assumptions would you like to enable? ")
    for ((idx, assumption) <- LazyList.from(0).zip(allAssumptions)) {
      println(s"$idx) $assumption")
    }

    print("Give all numbers seperated by a comma: ")
    val enabled = readLine().split(",").map(_.trim).map(_.toInt).map(allAssumptions(_))
    val disabled = allAssumptions.toSet -- enabled
    disabled.foreach(analysis.disable(_))

    def loop(state: AnalysisState): Unit = {
      state match {
        case s @ Suspended(exp, tracker) =>
          new Printer().display(exp)
          println()
          println("========================")
          println("Press enter to continue")
          readLine()
          loop(s.k(exp, tracker))

        case Finished =>
          println(analysis.currentAnalysis.get.finalResult)
      }
    }

    loop(analysis.sunspendableAnalyze(exp, Timeout.none))
  }
}
