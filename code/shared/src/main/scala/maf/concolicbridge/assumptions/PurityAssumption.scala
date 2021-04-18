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
                  val assumptionIdent = () => ScIdentifier(assumptionName, gen.nextIdentity)
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
                  val assumption = ScAssumed(ScIdentifier("pure", gen.nextIdentity), List(), gen.nextIdentity)

                  val operator = ScModSemantics.freshIdent

                  val resVar = ScModSemantics.genSym
                  val resVarIdent = () => ScIdentifier(resVar, gen.nextIdentity)
                  val functionAp = ScLetRec(
                    List(resVarIdent()),
                    List(ScFunctionAp(operator, synOperands, gen.nextIdentity)),
                    ScBegin(
                      identifiers.zip(oldIdentifiers).map { case (newIdent, oldIdent) =>
                        ScTest(assumptionIdent(),
                               ScFunctionAp.primitive("equal?", List(newIdent.apply(), oldIdent.apply()), gen.nextIdentity),
                               gen.nextIdentity
                        )
                      } ++ List(resVarIdent()),
                      gen.nextIdentity
                    ),
                    gen.nextIdentity
                  )

                  /* (f x) -->
                   * (letrec
                   *   ((f (assumed purity pure f))
                   *    (y old-y))
                   *
                   *   (f x)
                   *   (given purity (= y old-y)))
                   */
                  ScLetRec(
                    List(operator.asInstanceOf[ScIdentifier]) ++ oldIdentifiers.map(_.apply()),
                    List(assumption) ++ identifiers.map(_.apply()),
                    functionAp,
                    gen.nextIdentity
                  )
                }
              );
            }
          } >>
            unit
        }

      }
    }
  }
}
