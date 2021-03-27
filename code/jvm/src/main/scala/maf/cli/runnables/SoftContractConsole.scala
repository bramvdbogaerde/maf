package maf.cli.runnables

import maf.modular.contracts._
import maf.modular.contracts.analyses._
import maf.modular.contracts.domain._
import maf.modular.contracts.ScMain
import maf.language.contracts.ScExp

/** A tiny REPL for testing soft contract verification on smaller programs */
object SoftContractConsole extends App {
  import TinyRepl.repl

  object Evaluator extends TinyRepl.Evaluator {
    def eval(exp: ScExp): Any = {
      val analyser = new SimpleScSemantics(exp)
        with ScSchemeConstantPropagationDomain
        with ScCallInsensitivity
        with ScJVMAnalysis
        with ScGlobalStoreAnalysis
        with ScAnalysisWithPrelude

      analyser.analyze()
      println("Analysis terminated")
      println("Summary")
      println(s"Parsed expression $exp")
      println(s"Blames map ${analyser.summary.blames}")

      analyser.summary.returnValues.get(ScMain) match {
        case Some(value) => value
        case None =>
          throw new Exception("The program did not have a return value")
      }
    }
  }

  repl(Evaluator)
}
