package maf.cli.runnables

import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues

object ConcolicTesting {
  object Evaluator extends TinyRepl.Evaluator {

    override def eval(sc: ScExp): Any = {
      val analysis = new maf.modular.contracts.ConcolicTesting(sc) {
        override def isSat(exp: ScExp): List[ConcreteValues.Value] = ???
      }

      analysis.analyze()
      analysis.results
    }

  }

  def main(args: Array[String]): Unit = {
    val debug = args.contains("-debug")
    TinyRepl.repl(Evaluator, debug)
  }
}
