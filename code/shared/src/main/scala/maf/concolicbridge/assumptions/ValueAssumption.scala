package maf.concolicbridge.assumptions

import maf.core.Identity
import maf.language.contracts.ScExp
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScAssumed
import maf.language.contracts.ScFunctionAp
import maf.language.contracts.ScTest

/**
 * A value assumption uses the value it has been given, and ignores the value
 * from the actual expression.
 *
 * Example:
 *
 * (assumed value expr replacement alternative) --> replacement
 *
 * The alternatives can be syntactically used to use a different alternative value
 * in a next run.
 */
trait ValueAssumption extends AnalysisWithAssumptions { outer =>
  override def intraAnalysis(component: Component): ValueAssumptionIntra

  /** A set of names of given assertions that need to be negated */
  private var givensToNegate: Set[String] = Set()

  trait ValueAssumptionIntra extends AnalysisWithAssumptionsIntra {
    object ValueAssumption extends Assumption {
      def name: String = "value"
      override def run(
          name: String,
          exp: ScExp,
          arg: List[ScExp],
          idn: Identity
        ): ScEvalM[PS] = {
        assert(arg.size >= 1)
        println(exp)
        if (outer.isViolated(name)) {
          effectful {
            givensToNegate += name
            withInstrumenter { instrumenter =>
              instrumenter.replaceAt(
                idn,
                (generator, exp) => {
                  // replace the assumption with the alternative
                  ScAssumed(
                    ScIdentifier(name, generator.nextIdentity),
                    ScIdentifier("value", generator.nextIdentity),
                    exp,
                    arg.tail,
                    idn
                  )
                }
              )
            }
          } >>
            eval(exp)
        } else {
          eval(arg(0))
        }
      }

      // we override this behaviour because we want our
      // assumption to be evaluated if there are alternative
      override def isViolated(
          name: String,
          _exp: ScExp,
          _args: List[ScExp]
        ): Boolean =
        outer.isViolated(name) && _args.size == 1

    }

    //override def evalGiven(
    //    name: ScIdentifier,
    //    expr: ScExp,
    //    idn: Identity
    //  ): ScEvalM[PS] =
    //  effectful {
    //    if (givensToNegate.contains(name.name)) {
    //      withInstrumenter { instrumenter =>
    //        instrumenter.replaceAt(
    //          idn,
    //          (generator, exp) => {
    //            ScTest(name, ScFunctionAp.primitive("not", List(expr), generator.nextIdentity), idn)
    //          }
    //        )
    //      }
    //    }
    //  } >> result(lattice.schemeLattice.nil)

    registerAssumption("value", ValueAssumption)
  }
}
