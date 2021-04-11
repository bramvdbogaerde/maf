package maf.language.contracts

import maf.core.Identity

/**
 * The renamer makes sure that all variables are unique.
 * This is enabled by keeping track of an environment which
 * maps original variables names to unique variable names
 * and replaces them where appropriate
 */
class ScVariableRenamer {
  private var ctr = 0

  // This generates an identifier which cannot be parsed
  private def genSym: String = {
    ctr += 1
    s""""$ctr"""
  }

  private def variableNotFound[X](variable: String, idn: Identity): X = {
    throw new Exception(s"Variable not found ${variable} at ${idn}")
  }

  private def lookup(
      variable: String,
      env: Map[String, String],
      idn: Identity
    ): String = {
    env.get(variable).getOrElse(variableNotFound(variable, idn))
  }

  private def lookupIdentifier(
      identifier: ScIdentifier,
      env: Map[String, String]
    ): ScIdentifier = {
    ScIdentifier(lookup(identifier.name, env, identifier.idn), identifier.idn)
  }

  def transform(exp: ScExp): ScExp =
    transform(exp, Map())

  def transform(exp: ScExp, env: Map[String, String]): ScExp = exp match {
    case ScBegin(expressions, idn) =>
      val transformedExprs = expressions.map(e => transform(e, env))
      ScBegin(transformedExprs, idn)

    case ScIf(condition, consequent, alternative, idn) =>
      val transformedCond = transform(condition, env)
      val transformedConsequent = transform(consequent, env)
      val transformedAlternative = transform(alternative, env)
      ScIf(transformedCond, transformedConsequent, transformedAlternative, idn)

    case ScLetRec(idents, bindings, body, idn) =>
      val extended = env ++ idents.map(ident => (ident.name -> genSym))
      val transformedIdents = idents.map(ident => transform(ident, extended).asInstanceOf[ScIdentifier])
      val transformedBindings = bindings.map(binding => transform(binding, extended))
      val transformedBody = transform(body, extended)
      ScLetRec(transformedIdents, transformedBindings, transformedBody, idn)

    case ScSet(variable, value, idn) =>
      val transformedVariable = lookupIdentifier(variable, env)
      val transformedValue = transform(value, env)
      ScSet(transformedVariable, transformedValue, idn)

    case ScFunctionAp(operator, operands, idn, toplevel) =>
      val transformedOperator = transform(operator, env)
      val transformedOperands = operands.map(operand => transform(operand, env))
      ScFunctionAp(transformedOperator, transformedOperands, idn, toplevel)

    case v: ScValue => v
    case exp: ScIdentifier =>
      env.get(exp.name).map(n => ScIdentifier(n, exp.idn)).getOrElse(exp)

    case ScMon(contract, expression, idn, annotation) =>
      val transformedContract = transform(contract, env)
      val transformedExpression = transform(expression, env)
      ScMon(transformedContract, transformedExpression, idn, annotation)

    case o: ScOpaque => o
    case ScDependentContract(domains, rangeMaker, idn) =>
      val transformedDomains = domains.map(d => transform(d, env))
      val transformedRangeMaker = transform(rangeMaker, env)
      ScDependentContract(transformedDomains, transformedRangeMaker, idn)

    case ScFlatContract(expression, idn) =>
      val transformedExpression = transform(expression, env)
      ScFlatContract(transformedExpression, idn)

    case ScLambda(params, body, idn) =>
      val extended = env ++ params.map(p => (p.name -> genSym))
      val transformedParams = params.map {
        case id: ScIdentifier =>
          lookupIdentifier(id, env)
        case varArg: ScVarArgIdentifier =>
          ScVarArgIdentifier(lookup(varArg.name, env, varArg.idn), varArg.idn)
      }
      val transformedBody = transform(body, extended)
      ScLambda(transformedParams, transformedBody, idn)

    case ScProgram(expressions, _)                                        => ???
    case ScDefine(variable, expression, _)                                => ???
    case ScDefineFn(name, parameters, body, idn)                          => ???
    case ScDefineAnnotatedFn(name, parameters, contract, expression, idn) => ???

    case ScAssumed(name, simpleContract, expression, idn) =>
      val transformedExpression = transform(expression, env)
      ScAssumed(name, simpleContract, transformedExpression, idn)

    case ScGiven(name, expr, idn) =>
      val transformedExpr = transform(expr, env)
      ScGiven(name, transformedExpr, idn)

    case ScProvideContracts(variables, contracts, _) => ???
    case ScCar(pai, idn) =>
      val transformed = transform(pai, env)
      ScCar(transformed, idn)
    case ScCdr(pai, idn) =>
      val transformed = transform(pai, env)
      ScCdr(transformed, idn)
    case n: ScNil   => n
    case e: ScRaise => e
  }
}
