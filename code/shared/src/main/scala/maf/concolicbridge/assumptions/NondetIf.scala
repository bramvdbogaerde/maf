package maf.concolicbridge.assumptions

import maf.language.contracts.ScExp
import maf.core.Identity
import maf.language.contracts.ScAssumed
import maf.modular.contracts.semantics.ScModSemantics
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScBegin
import maf.language.contracts.ScTest
import maf.language.contracts.AssumptionBuilder

/**
 * This injects a "value" assumption into the code,
 * to assume that the result of an branch is a certain value.
 */
trait NondetIf extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): NondetIfIntra

  trait NondetIfIntra extends AnalysisWithAssumptionsIntra {
    case object NondetAssumption extends TransformationAssumption("nondetif")
    registerAssumption("nondetif", NondetAssumption)

    private def assumeConditional(
        condition: ScExp,
        consequent: ScExp,
        alternative: ScExp,
        idn: Identity
      ): Unit = {
      tracker.add("value", idn)
      withInstrumenter { instrumenter =>
        val name = ScModSemantics.genSym
        instrumenter.replaceAt(
          idn,
          (generator, exp) => {
            val builder = new AssumptionBuilder(generator)
            builder.addPreTest(condition)
            builder.body(
              builder.guarded(ScAssumed(ScIdentifier("value", generator.nextIdentity), List(consequent), generator.nextIdentity), List(), exp)
            )
            builder.build
          }
        )
      }
    }

    override def evalIf(
        condition: ScExp,
        consequent: ScExp,
        alternative: ScExp,
        idn: Identity
      ): ScEvalM[PostValue] = {
      eval(condition)
        .flatMap { value =>
          withPc { pc =>
            val t = feasible(primTrue, value)(pc)
            val f = feasible(primFalse, value)(pc)
            (t, f)
          }.flatMap {
            case (Right(_), Right(_)) if !tracker.contains("value", idn) && Assumption.enabled("nondetif") =>
              // both branches are "possible" source of non determinism
              effectful { assumeConditional(condition, consequent, alternative, idn) } >> unit
            case (_, _) => unit // all other cases
          } >> conditional(value, condition, consequent, alternative)
        }
    }
  }
}
