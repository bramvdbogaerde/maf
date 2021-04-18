package maf.concolicbridge.assumptions

import maf.modular.contracts.semantics._
import maf.language.contracts._
import maf.core.Identity

trait PurityAssumption extends AnalysisWithAssumptions {
  override def intraAnalysis(component: Component): PurityAssumptionIntra

  trait PurityAssumptionIntra extends AnalysisWithAssumptionsIntra {
    object Purity extends TaggedAssumption("pure")
    registerAssumption("pure", Purity)

    override def applyFnHook(
        operator: PostValue,
        operands: List[PostValue],
        syntactixOperator: ScExp,
        syntacticOperands: List[ScExp]
      ): Set[ScEvalM[PostValue]] =
      Assumption
        .hasTag(operator, "pure")
        .map(result => {
          result.flatMap(value =>
            nondets(lattice.getClosure(value.pure).map { closure =>
              call(closure, operands, syntacticOperands, false)
            })
          )
        }) ++ super.applyFnHook(operator, operands, syntactixOperator, syntacticOperands)

    override def evalFunctionApHook(
        operator: PostValue,
        operand: List[PostValue],
        synOperator: ScExp,
        synOperands: List[ScExp],
        idn: Identity
      ): ScEvalM[Unit] = {
      super.evalFunctionApHook(operator, operand, synOperator, synOperands, idn) >> {
        // first check whether the operator is an assumed value
        // if it is we will not assume anything else. TODO: check only for purity here
        if (
          lattice.isDefinitivelyAssumedValue(operator.pure) ||
          lattice.getClosure(operator.pure).size < 1 ||
          tracker.contains("pure", idn) ||
          !Assumption.enabled("pure")
        ) {
          unit
        } else {
          effectful {
            tracker.add("pure", idn)
            withInstrumenter { instrumenter =>
              // generate the name of the assumption
              val assumptionName = ScModSemantics.genSym
              assume(assumptionName)
              instrumenter.replaceAt(
                idn,
                (gen, expr) => {
                  val builder = new AssumptionBuilder(gen)

                  // generate the set of impacted variables
                  // TODO: this set of variables can be made smaller by checking which ones are actually used for the
                  // path condition
                  val variables = impactVariablesNames

                  // generate identifiers for the variables we care about
                  val identifiers = variables.map(v => () => ScIdentifier(v, gen.nextIdentity))

                  // generate names such as old-y and old-x
                  val oldNames = variables.map(_ => ScModSemantics.genSym)
                  val oldIdentifiers = oldNames.map(name => () => ScIdentifier(name, gen.nextIdentity))

                  // generate the assumption itself
                  val assumption =
                    builder.guarded(ScAssumed(ScIdentifier("pure", gen.nextIdentity), List(synOperator), gen.nextIdentity), List(), synOperator)

                  val operator = ScModSemantics.genSym

                  // keep track of the function we are going to apply
                  builder.localVar(operator, assumption)

                  // execute the function itself
                  builder.body(ScFunctionAp(ScIdentifier(operator, gen.nextIdentity), synOperands, gen.nextIdentity))

                  // remember the values of the variables before the call, and check if they are still the same after the call
                  identifiers.zip(oldIdentifiers).foreach { case (newIdent, oldIdent) =>
                    builder
                      .localVar(oldIdent().name, newIdent())
                      .addPostTest(ScFunctionAp.primitive("equal?", List(newIdent.apply(), oldIdent.apply()), gen.nextIdentity))
                  }

                  builder.build
                }
              )
            }
          } >>
            unit
        }

      }
    }
  }
}
