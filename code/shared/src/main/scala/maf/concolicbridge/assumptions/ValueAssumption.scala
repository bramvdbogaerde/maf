package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp

/**
 * A value assumption uses the value it has been given, and ignores the value
 * from the actual expression.
 *
 * Example:
 *
 * (assumed value #t #f) --> #f
 */
trait ValueAssumption extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): ValueAssumptionIntra

  trait ValueAssumptionIntra extends AnalysisWithAssumptionsIntra {
    object ValueAssumption extends Assumption {
      override def run(
          exp: ScExp,
          arg: List[ScExp],
          idn: Identity
        ): ScEvalM[PS] = {
        assert(arg.size == 1)
        eval(arg(0))
      }
    }

    registerAssumption("value", ValueAssumption)
  }
}
