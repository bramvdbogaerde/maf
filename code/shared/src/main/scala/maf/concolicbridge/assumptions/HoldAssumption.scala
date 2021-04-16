package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp
import maf.core.Address
import maf.language.contracts.ScLattice

/**
 * The hold assumption, which can be used to encapsulate a value and make
 * sure that it satisfies any contract
 */
trait HoldsAssumptionAnalysis extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): HoldsAssumptionAnalysisIntra

  trait HoldsAssumptionAnalysisIntra extends AnalysisWithAssumptionsIntra {
    object HoldsAssumption extends TaggedAssumption("holds")
    registerAssumption("holds", HoldsAssumption)

    override protected def call(
        clo: ScLattice.Clo[Address],
        operands: List[PS],
        syntacticOperands: List[ScExp],
        evict: Boolean
      ): ScEvalM[PS] = {
      // filter out all the tagged assumption values (i.e. resolve them to their actual values)
      sequence(operands.flatMap(ps => {
        println(ps)
        if (lattice.isDefinitivelyAssumedValue(ps.pure)) {
          lattice.getAssumedValues(ps.pure).map(assumed => read(assumed.value))
        } else if (lattice.getAssumedValues(ps.pure).size == 0) {
          List(pure(ps))
        } else {
          throw new Exception("Either the value is a singleton assumption, or just another type of value, nothing in between")
        }
      })).flatMap(operands => super.call(clo, operands, syntacticOperands, evict))
    }

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

      Assumption.checkTag(expressionValue, "holds") >>= { checked =>
        if (lattice.isDefinitivelyAssumedValue(expressionValue.pure) && checked) {
          // we assume that the contract holds, nothing to check, TODO: but we will extend the path condition
          pure(expressionValue)
        } else {
          super.monFlat(contract, expressionValue, blamedIdentity, blamingIdentity, doBlame, syntacticExpression)
        }
      }
    }
  }
}
