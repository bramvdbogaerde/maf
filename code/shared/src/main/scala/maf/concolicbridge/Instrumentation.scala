package maf.concolicbridge

import maf.core.Identity
import maf.core.InstrumentedIdentity
import maf.language.contracts._

/**
 * Generate an identity based on the identity of the the node
 * that is getting replaced
 *
 * @param idn the identity to use as a base identity
 */
class IdentityGenerator(idn: Identity) {
  private var sequenceNumber = 0
  def nextIdentity: Identity = {
    sequenceNumber += 1
    InstrumentedIdentity(idn.idn, sequenceNumber)
  }
}

case class Instrumenter(replacementNodes: Map[Identity, (IdentityGenerator, ScExp) => ScExp]) {

  /**
   * Register an AST node to be replaced at the AST node with the
   * given identifier.
   */
  def replaceAt(idn: Identity, node: (IdentityGenerator, ScExp) => ScExp): Instrumenter = {
    this.copy(replacementNodes = replacementNodes.updated(idn, node))
  }

  /**
   * Applies the instrumentation instructions on the given
   * AST tree. This assumes that each node in the AST has a unique
   * identity.
   */
  def run(e: ScExp): ScExp = {
    val f = replacementNodes.get(e.idn).getOrElse((_: IdentityGenerator, e: ScExp) => e)
    f(
      new IdentityGenerator(e.idn),
      e match {
        case ScBegin(expressions, _) =>
          val instrumentedExpressions = expressions.map(run)
          ScBegin(instrumentedExpressions, e.idn)
        case ScIf(condition, consequent, alternative, idn) =>
          val instrumentedCondition = run(condition)
          val instrumentedConsequent = run(consequent)
          val instrumentedAlternative = run(alternative)
          ScIf(instrumentedCondition, instrumentedConsequent, instrumentedAlternative, idn)

        case ScLetRec(idents, bindings, body, idn) =>
          val instrumentendBindings = bindings.map(run)
          val instrumentedBody = run(body)
          ScLetRec(idents, instrumentendBindings, instrumentedBody, idn)

        case ScSet(variable, value, idn) =>
          val instrumentedValue = run(value)
          ScSet(variable, instrumentedValue, idn)

        case ScFunctionAp(operator, operands, idn, _) =>
          val instrumentedOperator = run(operator)
          val instrumentedOperands = operands.map(run)
          ScFunctionAp(instrumentedOperator, instrumentedOperands, idn)

        case v: ScValue =>
          v
        case exp: ScIdentifier =>
          exp

        case ScMon(contract, expression, idn, annotations) =>
          val instrumentedContract = run(contract)
          val instrumentedExpression = run(expression)
          ScMon(instrumentedContract, instrumentedExpression, idn, annotations)

        case v: ScOpaque =>
          v

        case ScDependentContract(domains, rangeMaker, idn) =>
          val instrumentedDomains = domains.map(run)
          val instrumentedRangeMaker = run(rangeMaker)
          ScDependentContract(instrumentedDomains, instrumentedRangeMaker, idn)

        case ScFlatContract(expression, idn) =>
          val instrumentedExpression = run(expression)
          ScFlatContract(instrumentedExpression, idn)

        case ScLambda(params, body, idn) =>
          val instrumentedBody = run(body)
          ScLambda(params, instrumentedBody, idn)

        case ScProgram(expressions, idn) =>
          val instrumentedExpressions = expressions.map(run)
          ScProgram(instrumentedExpressions, idn)

        case ScDefine(variable, expression, idn) =>
          val instrumentedExpression = run(expression)
          ScDefine(variable, instrumentedExpression, idn)

        case ScDefineFn(name, parameters, body, idn) =>
          val instrumentedBody = ScBegin(body.expressions.map(run), body.idn)
          ScDefineFn(name, parameters, instrumentedBody, idn)

        case ScDefineAnnotatedFn(name, parameters, contract, expression, idn) =>
          val instrumentedContract = run(contract)
          val instrumentedExpression = ScBegin(expression.expressions.map(run), expression.idn)
          ScDefineAnnotatedFn(name, parameters, instrumentedContract, instrumentedExpression, idn)

        case ScAssumed(name, simpleContract, expression, arguments, idn) =>
          val instrumentedSimpleContract = run(simpleContract).asInstanceOf[ScIdentifier]
          val instrumentedExpression = run(expression)
          val instrumentedArguments = arguments.map(run)
          ScAssumed(name, instrumentedSimpleContract, instrumentedExpression, instrumentedArguments, idn)

        case ScProvideContracts(variables, contracts, idn) =>
          val instrumentedContracts = contracts.map(run)
          ScProvideContracts(variables, instrumentedContracts, idn)

        case ScGiven(name, exp, idn) =>
          val instrumentedExp = run(exp)
          ScGiven(name, instrumentedExp, idn)

        case ScCar(pai, idn) =>
          val instrumentedPai = run(pai)
          ScCar(instrumentedPai, idn)

        case ScCdr(pai, idn) =>
          val instrumentedPai = run(pai)
          ScCdr(instrumentedPai, idn)

        case ScNil(idn) => ScNil(idn)
      }
    )
  }
}
