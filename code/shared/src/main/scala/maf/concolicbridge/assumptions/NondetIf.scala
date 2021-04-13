package maf.concolicbridge.assumptions

import maf.language.contracts.ScExp
import maf.core.Identity
import maf.language.contracts.ScAssumed
import maf.modular.contracts.semantics.ScModSemantics
import maf.language.contracts.ScGiven
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScBegin

/**
 * This injects a "value" assumption into the code,
 * to assume that the result of an branch is a certain value.
 */
trait NondetIf extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): NondetIfIntra

  trait NondetIfIntra extends AnalysisWithAssumptionsIntra {
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
            val nameIdent = () => ScIdentifier(name, generator.nextIdentity)
            val assumption = ScAssumed(
              nameIdent(),
              ScIdentifier("value", generator.nextIdentity),
              exp,
              List(consequent, alternative),
              generator.nextIdentity
            )

            val assertion = ScGiven(
              nameIdent(),
              condition,
              generator.nextIdentity
            )

            ScBegin(List(assertion, assumption), generator.nextIdentity)
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
            case (Right(_), Right(_)) if !tracker.contains("value", idn) =>
              // both branches are "possible" source of non determinism
              effectful { assumeConditional(condition, consequent, alternative, idn) } >> unit
            case (_, _) => unit // all other cases
          } >> conditional(value, condition, consequent, alternative)
        }
    }
  }
}
