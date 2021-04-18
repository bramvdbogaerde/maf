package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp
import maf.language.contracts.ScBegin
import maf.modular.contracts.semantics.ScModSemantics
import maf.language.contracts.{ScFunctionAp, ScIdentifier, ScValue}
import maf.language.contracts.ScTest
import maf.language.contracts.AssumptionBuilder
import maf.language.contracts.ScAssumed

/**
 * An assumption that withholds a blame if proven to be safe by the concolic tester.
 *
 * If applied consistently, it allows the concolic tester to disable contract checking enterirely, making it more efficient in general.
 */
trait NonBlameAssumption extends AnalysisWithAssumptions with HoldsAssumptionAnalysis {

  override def intraAnalysis(component: Component): NonBlameAssumptionIntra

  trait NonBlameAssumptionIntra extends AnalysisWithAssumptionsIntra with HoldsAssumptionAnalysisIntra {
    case object NonBlameAssumption extends TransformationAssumption("nonblame")
    registerAssumption("nonblame", NonBlameAssumption)

    override def monFlatHook(
        value: PostValue,
        conditional: ScEvalM[PostValue],
        blamedIdentity: Identity,
        blamingIdentity: Identity,
        syntacticOperator: Option[ScExp],
        domainContract: Option[Int]
      ): ScEvalM[PostValue] = {
      withPc { pc =>
        val t = feasible(primTrue, value)(pc)
        val f = feasible(primFalse, value)(pc)
        t.isRight && f.isRight
      } >>= { checked =>
        if (domainContract.isDefined && checked && !tracker.contains("nonblame", blamedIdentity) && Assumption.enabled("nonblame")) {
          tracker.add("nonblame", blamedIdentity)
          // if it cannot be determined whether the contract is valid or not, then we try to assume it is
          effectful {
            withInstrumenter { instrumenter =>
              instrumenter.replaceAt(
                blamedIdentity,
                (gen, exp) => {
                  val builder = new AssumptionBuilder(gen)
                  val contract = ScFunctionAp.primitive(
                    "domain-contract",
                    List(syntacticOperator.get, ScValue.num(domainContract.get, gen.nextIdentity)),
                    gen.nextIdentity
                  )
                  builder.addPreTest(ScFunctionAp(contract, List(exp), gen.nextIdentity))
                  builder.guarded(HoldsAssumption.applyTo(exp)(gen), List(), exp)
                }
              )
            }
          } >> conditional
        } else {
          // traditional case
          conditional
        }
      }
    }

  }
}
