package maf.language.contracts.transformations

import maf.language.contracts._
import maf.core.Identity
import maf.concolicbridge.IdentityGenerator

/**
 * Transforms the given function definition into a function definition that has been inlined (a few times).
 *  The transformation assumes that all variable names are unique and that no variable names shadow
 *  other variable names.
 *
 *  @param functionName the name of the recursive function
 *  @param depth the maximum inlining depth of the recursive function
 *  @param replaceWith a function that given the last recursive function call expression generates a new expression that will
 *  be used to replace the last recursive function call. In order to preserve the semantics this should be the identity function
 *  but it can also do replace it with something that does not preserve the semantics.
 */
class RecursiveFunctionInlinining(
    functionName: String,
    depth: Int,
    replaceWith: (ScExp, IdentityGenerator) => ScExp) { outer =>
  class Transformer(
      parameters: List[ScParam],
      body: ScBegin,
      idn: Identity) {

    private var ctr = 0

    // This generates an identifier which cannot be parsed
    private def genSym: String = {
      ctr += 1
      s""""inlining$ctr"""
    }

    private val generator: IdentityGenerator = new IdentityGenerator(idn)
    private var depth: Int = outer.depth

    def transform(exp: ScExp): ScExp = exp match {
      case ScBegin(expressions, idn) =>
        val tExpr = expressions.map(transform)
        ScBegin(tExpr, idn)

      case ScIf(condition, consequent, alternative, idn) =>
        val tCnd = transform(condition)
        val tCns = transform(consequent)
        val tAlt = transform(alternative)
        ScIf(tCnd, tCns, tAlt, idn)

      case ScLetRec(idents, bindings, body, idn) =>
        val tBindings = bindings.map(transform)
        val tBody = transform(body)
        ScLetRec(idents, tBindings, tBody, idn)

      case s: ScRaise => s
      case ScSet(variable, value, idn) =>
        val tVal = transform(value)
        ScSet(variable, tVal, idn)

      case ScFunctionAp(ScIdentifier(`functionName`, _), operands, _, _) if depth > 0 =>
        val tmpVars = operands.map(_ => genSym)
        depth -= 1
        val exprs = transform(body)
        val letrec = ScLetRec(
          names = parameters.map(name => ScIdentifier(name.name, generator.nextIdentity)),
          bindings = tmpVars.map(name => ScIdentifier(name, generator.nextIdentity)),
          body = exprs,
          idn = generator.nextIdentity
        )

        val outerletrec = ScLetRec(
          names = tmpVars.map(name => ScIdentifier(name, generator.nextIdentity)),
          bindings = operands,
          body = letrec,
          idn = generator.nextIdentity
        )

        outerletrec

      case f @ ScFunctionAp(ScIdentifier(`functionName`, _), _, _, _) if depth == 0 =>
        replaceWith(f, generator)

      case ScFunctionAp(operator, operands, idn, annotations) =>
        val tOp = transform(operator)
        val tOps = operands.map(transform)
        ScFunctionAp(tOp, tOps, idn, annotations)

      case v: ScValue        => v
      case exp: ScIdentifier => exp
      case ScMon(contract, expression, idn, annotation) =>
        val tCon = transform(contract)
        val tExp = transform(expression)
        ScMon(tCon, tExp, idn, annotation)

      case o: ScOpaque => o
      case ScDependentContract(domains, rangeMaker, idn) =>
        val tDoms = domains.map(transform)
        val tRange = transform(rangeMaker)
        ScDependentContract(tDoms, tRange, idn)

      case ScFlatContract(expression, idn) =>
        val tExpr = transform(expression)
        ScFlatContract(tExpr, idn)

      case ScLambda(params, body, idn) =>
        // we will not go deep into lambda's
        ScLambda(params, body, idn)

      case ScProgram(expressions, idn) =>
        val tExpr = expressions.map(transform)
        ScProgram(tExpr, idn)

      case ScDefine(variable, expression, idn) =>
        val tExpr = transform(expression)
        ScDefine(variable, tExpr, idn)

      case df: ScDefineFn =>
        // again we will not go into lambda's for inlining
        df

      case df: ScDefineAnnotatedFn =>
        df

      case ScAssumed(name, simpleContract, expression, idn) =>
        val tCon = transform(simpleContract)
        val tExp = transform(expression)
        ScAssumed(name, tCon, tExp, idn)

      case ScGiven(name, expr, idn) =>
        val tExpr = transform(expr)
        ScGiven(name, tExpr, idn)

      case ScProvideContracts(variables, contracts, idn) =>
        val tCon = contracts.map(transform)
        ScProvideContracts(variables, tCon, idn)
      case ScCar(pai, idn) =>
        val tPai = transform(pai)
        ScCar(tPai, idn)

      case ScCdr(pai, idn) =>
        val tPai = transform(pai)
        ScCdr(tPai, idn)

      case n: ScNil => n
    }

  }
  def transform(exp: ScExp): ScExp = exp match {
    case ScDefineFn(name, parameters, expressions, idn) if functionName == name =>
      val transformer = new Transformer(parameters, expressions, idn)
      val newBody = transformer.transform(expressions)
      ScDefineFn(name, parameters, newBody.asInstanceOf[ScBegin], idn)

    case f: ScDefineFn =>
      throw new Exception(s"cannot transform given expression, not a function with name ${functionName}, got ${f.name}")
    case _ =>
      throw new Exception("cannot transform given expression, not a function definition")
  }
}
