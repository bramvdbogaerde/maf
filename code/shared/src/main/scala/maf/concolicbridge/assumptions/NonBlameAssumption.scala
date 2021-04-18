package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp
import maf.language.contracts.ScBegin
import maf.modular.contracts.semantics.ScModSemantics
import maf.language.contracts.{ScFunctionAp, ScIdentifier, ScValue}
import maf.language.contracts.ScTest

/**
 * An assumption that withholds a blame if proven to be safe by the concolic tester.
 *
 * If applied consistently, it allows the concolic tester to disable contract checking enterirely, making it more efficient in general.
 */
trait NonBlameAssumption extends AnalysisWithAssumptions {

  override def intraAnalysis(component: Component): NonBlameAssumptionIntra

  trait NonBlameAssumptionIntra extends AnalysisWithAssumptionsIntra {
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
                  val assName = ScModSemantics.genSym
                  val assIdentifier = () => ScIdentifier(assName, gen.nextIdentity)

                  ScBegin(
                    List(
                      ScTest(
                        assIdentifier(),
                        ScFunctionAp(
                          ScFunctionAp.primitive(
                            "domain-contract",
                            List(syntacticOperator.get, ScValue.num(domainContract.get, gen.nextIdentity)),
                            gen.nextIdentity
                          ),
                          List(exp),
                          gen.nextIdentity
                        ),
                        gen.nextIdentity
                      ),
                      exp
                    ),
                    gen.nextIdentity
                  )
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
