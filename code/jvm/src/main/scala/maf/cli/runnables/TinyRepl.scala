package maf.cli.runnables

import scala.io.StdIn.readLine
import maf.language.contracts.ScExp
import maf.language.contracts.SCExpCompiler

object TinyRepl {
  trait Evaluator {
    def eval(sc: ScExp): Any
  }

  def repl(evaluator: Evaluator, debug: Boolean = false): Unit = {
    print("> ")
    val input = readLine().trim()
    if (input != ":q") {
      val exp: ScExp =
        try SCExpCompiler.read(input)
        catch {
          case e: Exception =>
            println(s"error while parsing expression ${e.getMessage()}")
            return repl(evaluator)
        }

      println(s"Analysing ${exp}")
      try {
        println(s">>> ${evaluator.eval(exp)}")
      } catch {
        case e: Exception =>
          println(s"E: ${e.getMessage()}")
          if (debug) {
            e.printStackTrace()
          }
      }

      repl(evaluator, debug)
    }

  }
}
