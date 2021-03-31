package maf.cli.runnables

import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues

object ConcolicTesting {
  object Evaluator extends TinyRepl.Evaluator {

    override def eval(sc: ScExp): Any = {
      val analysis = new maf.modular.contracts.ConcolicTesting(sc) {

        def isSat(exp: ScExp): Option[Map[String, Val]] = ???
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
