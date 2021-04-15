package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp

/**
 * The hold assumption, which can be used to encapsulate a value and make
 * sure that it satisfies any contract
 */
trait HoldsAssumptionAnalysis extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): HoldsAssumptionAnalysisIntra

  trait HoldsAssumptionAnalysisIntra extends AnalysisWithAssumptionsIntra {
    case object HoldsAssumption extends TaggedAssumption("holds")

    // eventually a value that needs to be checked whether it satisfies
    // a contract reaches the monFlat method
    override def monFlat(
        contract: PostValue,
        expressionValue: PostValue,
        blamedIdentity: Identity,
        blamingIdentity: Identity,
        doBlame: Boolean,
        syntacticExpression: Option[ScExp]
      ): ScEvalM[PostValue] = {
      if (
        lattice.isDefinitivelyAssumedValue(expressionValue) &&
        Assumption.checkTag(expressionValue, "holds")
      ) {
        // we assume that the contract holds, nothing to check
        pure(expressionValue)
      } else {
        super.monFlat(contract, expressionValue, blamedIdentity, blamingIdentity, doBlame, syntacticExpression)
      }

    }
  }
}
