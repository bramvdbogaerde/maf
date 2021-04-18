package maf.language.contracts.transformations

import maf.core.Identity
import maf.language.contracts._

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
    transform(exp, Map())._1

  def transform(exp: ScExp, env: Map[String, String]): (ScExp, Map[String, String]) = exp match {
    case ScBegin(expressions, idn) =>
      val (transformedExprs, newEnv) = expressions
        .foldRight((List[ScExp](), env))((exp, res) => {
          val (transExp, updatedEnv) = transform(exp, res._2)
          (transExp :: res._1, updatedEnv)
        })

      (ScBegin(transformedExprs, idn), newEnv)

    case ScIf(condition, consequent, alternative, idn) =>
      val transformedCond = transform(condition, env)._1
      val transformedConsequent = transform(consequent, env)._1
      val transformedAlternative = transform(alternative, env)._1
      (ScIf(transformedCond, transformedConsequent, transformedAlternative, idn), env)

    case ScLetRec(idents, bindings, body, idn) =>
      val extended = env ++ idents.map(ident => (ident.name -> genSym))
      val transformedIdents = idents.map(ident => transform(ident, extended)._1.asInstanceOf[ScIdentifier])
      val transformedBindings = bindings.map(binding => transform(binding, extended)._1)
      val transformedBody = transform(body, extended)._1
      (ScLetRec(transformedIdents, transformedBindings, transformedBody, idn), env)

    case ScSet(variable, value, idn) =>
      val transformedVariable = lookupIdentifier(variable, env)
      val transformedValue = transform(value, env)._1
      (ScSet(transformedVariable, transformedValue, idn), env)

    case ScFunctionAp(operator, operands, idn, toplevel) =>
      val transformedOperator = transform(operator, env)._1
      val transformedOperands = operands.map(operand => transform(operand, env)._1)
      (ScFunctionAp(transformedOperator, transformedOperands, idn, toplevel), env)

    case v: ScValue => (v, env)
    case exp: ScIdentifier =>
      (env.get(exp.name).map(n => ScIdentifier(n, exp.idn)).getOrElse(exp), env)

    case ScMon(contract, expression, idn, annotation) =>
      val transformedContract = transform(contract, env)._1
      val transformedExpression = transform(expression, env)._1
      (ScMon(transformedContract, transformedExpression, idn, annotation), env)

    case o: ScOpaque => (o, env)
    case ScDependentContract(domains, rangeMaker, idn) =>
      val transformedDomains = domains.map(d => transform(d, env)._1)
      val transformedRangeMaker = transform(rangeMaker, env)._1
      (ScDependentContract(transformedDomains, transformedRangeMaker, idn), env)

    case ScFlatContract(expression, idn) =>
      val transformedExpression = transform(expression, env)._1
      (ScFlatContract(transformedExpression, idn), env)

    case ScLambda(params, body, idn) =>
      val extended = env ++ params.map(p => (p.name -> genSym))
      val transformedParams = params.map {
        case id: ScIdentifier =>
          lookupIdentifier(id, extended)
        case varArg: ScVarArgIdentifier =>
          ScVarArgIdentifier(lookup(varArg.name, extended, varArg.idn), varArg.idn)
      }
      val transformedBody = transform(body, extended)._1
      (ScLambda(transformedParams, transformedBody, idn), env)

    case ScProgram(expressions, idn) =>
      val (transformedExprs, newEnv) = expressions
        .foldRight((List[ScExp](), env))((exp, res) => {
          val (transExp, updatedEnv) = transform(exp, res._2)
          (transExp :: res._1, updatedEnv)
        })

      (ScProgram(transformedExprs, idn), newEnv)

    case ScDefine(variable, expression, idn) =>
      val extended = env + (variable.name -> genSym)
      val transformedVariable = lookupIdentifier(variable, extended)
      val transformedExpression = transform(expression, env)._1
      (ScDefine(transformedVariable, transformedExpression, idn), extended)

    case ScDefineFn(name, params, body, idn) =>
      val extended = env + (name.name -> genSym)
      val transformedName = lookupIdentifier(name, extended)
      val extended2 = env ++ params.map(p => (p.name -> genSym))
      val transformedParams = params.map {
        case id: ScIdentifier =>
          lookupIdentifier(id, extended2)
        case varArg: ScVarArgIdentifier =>
          ScVarArgIdentifier(lookup(varArg.name, extended2, varArg.idn), varArg.idn)
      }
      val (transformedBody, _) = transform(body, extended2)
      (ScDefineFn(transformedName, transformedParams, transformedBody.asInstanceOf[ScBegin], idn), extended)

    case ScDefineAnnotatedFn(name, params, contract, expression, idn) =>
      val extended = env + (name.name -> genSym)
      val transformedName = lookupIdentifier(name, extended)
      val extended2 = env ++ params.map(p => (p.name -> genSym))
      val transformedParams = params.map {
        case id: ScIdentifier =>
          lookupIdentifier(id, extended2)
        case varArg: ScVarArgIdentifier =>
          ScVarArgIdentifier(lookup(varArg.name, extended2, varArg.idn), varArg.idn)
      }
      val (transformedBody, _) = transform(expression, extended2)
      val (transformedContract, _) = transform(contract, extended)
      (ScDefineAnnotatedFn(transformedName, transformedParams, transformedContract, transformedBody.asInstanceOf[ScBegin], idn), extended)

    case ScAssumed(simpleContract, arguments, idn) =>
      val transformedArguments = arguments.map(arg => transform(arg, env)._1)
      (ScAssumed(simpleContract, transformedArguments, idn), env)

    case ScTest(name, expr, idn) =>
      val transformedExpr = transform(expr, env)._1
      (ScTest(name, transformedExpr, idn), env)

    case ScTestVerified(name, expr, idn) =>
      val transformedExpr = transform(expr, env)._1
      (ScTestVerified(name, transformedExpr, idn), env)

    case ScTestViolated(name, expr, idn) =>
      val transformedExpr = transform(expr, env)._1
      (ScTestViolated(name, transformedExpr, idn), env)

    case ScProvideContracts(variables, contracts, idn) =>
      val transformedVariables = variables.map(v => lookupIdentifier(v, env))
      val transformedContracts = contracts.map(c => transform(c, env)._1)
      (ScProvideContracts(transformedVariables, transformedContracts, idn), env)

    case ScCar(pai, idn) =>
      val transformed = transform(pai, env)._1
      (ScCar(transformed, idn), env)
    case ScCdr(pai, idn) =>
      val transformed = transform(pai, env)._1
      (ScCdr(transformed, idn), env)
    case n: ScNil   => (n, env)
    case e: ScRaise => (e, env)
  }
}
