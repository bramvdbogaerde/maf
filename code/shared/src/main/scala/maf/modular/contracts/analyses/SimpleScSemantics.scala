package maf.modular.contracts.analyses

import maf.core.Identity
import maf.language.contracts.{ScExp, ScIdentifier, ScLattice, ScSchemeLattice}
import maf.modular.ModAnalysis
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.util.benchmarks.Timeout
import maf.modular.contracts.semantics._
import maf.modular.contracts.domain._
import maf.modular.contracts._

object SimpleScSemantics {
  val primitivesMap = Map(
    ">" -> ">/c",
    "=" -> "=/c",
    "<" -> "</c",
    "-" -> "-/c",
    "+" -> "+/c",
    "*" -> "*/c",
    "/" -> "//c",
    "string=?" -> "string=?/c",
    "number?" -> "int?/c",
    "string?" -> "string?/c",
    "nonzero?" -> "nonzero?/c",
    "any?" -> "any?/c",
    "true?" -> "true?/c",
    "false?" -> "false?/c",
    "procedure?" -> "proc?/c",
    "bool?" -> "bool?/c",
    "and" -> "and/c",
    "or" -> "or/c",
    "not" -> "not/c",
    "number?" -> "int?/c",
    "char?" -> "char?/c",
    "pair?" -> "pair?/c",
    "string-length" -> "string-length",
    "null?" -> "null?/c",
    "dependent-contract?" -> "dependent-contract/c"
  )
}

case class NoOpMonad[X]()
abstract class SimpleScSemantics(prg: ScExp)
    extends ModAnalysis(prg)
       with ScBigStepSemanticsScheme
       with ScBigStepSemanticsMonitored
       with ScStandardComponents
       with ScSchemePrimitives
       with FIFOWorklistAlgorithm[ScExp] { outer =>

  val primitivesMap: Map[String, String] = SimpleScSemantics.primitivesMap
  override def analyzeWithTimeout(timeout: Timeout.T): Unit = {
    setup()
    super.analyzeWithTimeout(timeout)
  }

  override def intraAnalysis(component: Component) =
    new IntraAnalysis(component) with IntraScBigStepSemantics with IntraScBigStepSemanticsMonitored {}
}
