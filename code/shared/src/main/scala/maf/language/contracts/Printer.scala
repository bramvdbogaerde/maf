package maf.language.contracts

import java.io.Writer

class Printer {
  private val printer: PrettyPrinter = new PrettyPrinter

  def run(e: ScExp): Unit =
    e match {
      case ScBegin(expressions, _) =>
        printer.print("(begin ")
        printer.newIndent()
        expressions.map(run)
        printer.print(")")
        printer.exitIndent()

      case ScIf(condition, consequent, alternative, idn) =>
        printer.print("(if ")
        run(condition)
        printer.newIndent()
        run(consequent)
        printer.newline()
        run(alternative)
        printer.print(")")
        printer.exitIndent()

      case ScLetRec(idents, bindings, body, idn) =>
        printer.print("(let")
        printer.newIndent()
        printer.print("(")
        val last = idents.last
        idents.zip(bindings).map { case (ident, binding) =>
          printer.print("(")
          printer.print(ident.name)
          printer.print(" ")
          run(binding)
          printer.print(")")
          if (last.idn != ident.idn) {
            printer.newline()
          }
        }

      case ScSet(variable, value, idn) =>
        printer.print("(set! ")
        run(variable)
        printer.print(" ")
        run(value)
        print.print(")")

      case ScFunctionAp(operator, operands, idn, _) =>
        printer.print("(")
        run(operator)
        printer.print(" ")
        operands.init.foreach { operand =>
          run(operand)
          printer.print(" ")
        }

        run(operands.last)
        printer.print(")")

      case v: ScValue =>
        printer.print(v.toString())

      case exp: ScIdentifier =>
        printer.print(exp.toString())

      case ScMon(contract, expression, idn, annotations) =>
        printer.print("(mon ")
        run(contract)
        printer.print(" ")
        run(expression)
        printer.print(")")

      case v: ScOpaque =>
        printer.print(v.toString())

      case ScDependentContract(domains, rangeMaker, idn) =>
        printer.print("(~ ")
        domains.init.foreach {
          domain
          run(domain)
          printer.print(" ")
        }

        run(domains.last)
        printer.print(" ")
        run(rangeMaker)
        printer.print(")")

      case ScFlatContract(expression, idn) =>
        expression.toString()

      case ScLambda(params, body, idn) =>
        printer.print("(lambda (")
        params.init.foreach { param =>
          run(param)
          printer.print(" ")
        }
        run(params.last)
        printer.print(")")
        printer.newIndent()
        run(body)
        printer.exitIndent()

      case ScProgram(expressions, idn) =>
        expressions.foreach { exp =>
          printer.print(exp)
        }

      case ScDefine(variable, expression, idn) =>
        printer.print("(define ")
        run(variable)
        run(expression)
        printer.print(")")

      case ScDefineFn(name, parameters, body, idn) =>
        printer.print("(define ")
        printer.print("(")
        run(name)
        parameters.init.foreach { param =>
          run(param)
          printer.print(" ")
        }
        run(param.last)
        printer.print(")")
        printer.newIndent()
        run(body)
        printer.exitIndent()
        printer.print(")")

      case ScDefineAnnotatedFn(name, parameters, contract, expression, idn) =>
        printer.print("(define/contract ")
        printer.print("(")
        run(name)
        parameters.init.foreach { param =>
          run(param)
          printer.print(" ")
        }
        run(param.last)
        printer.print(")")
        printer.newIndent()
        run(contract)
        printer.newline()
        run(expression)
        printer.exitIndent()
        printer.print(")")

      case ScAssumed(simpleContract, arguments, idn) =>
        printer.print("(assumed ")
        printer.print(simpleContract)
        printer.print(" ")
        arguments.init.foreach { arg =>
          run(arg)
          printer.print(" ")
        }
        run(arg.last)
        printer.print(")")

      case ScTest(name, exp, idn) =>
        printer.print("(test ")
        run(name)
        printer.print(" ")
        run(exp)
        printer.print(")")

      case ScTestVerified(name, exp, idn) =>
        printer.print("(test/verified ")
        run(name)
        printer.print(" ")
        run(exp)
        printer.print(")")

        ScTestVerified(name, run(exp), idn)

      case ScTestViolated(name, exp, idn) =>
        printer.print("(test/violated ")
        run(name)
        printer.print(" ")
        run(exp)
        printer.print(")")

      case ScIfGuard(name, cons, alts, idn) =>
        printer.print("(if/guard ")
        run(name)
        printer.newIndent()
        run(cons)
        printer.newline()
        alts.init.foreach { alt =>
          run(alt)
          printer.newline()
        }

        run(alts.last)
        printer.exitIndent()
        printer.print(")")

      case s @ ScProvideContracts(variables, contracts, idn) =>
        s.toString()

      case ScCar(pai, idn) =>
        printer.print("(car ")
        run(pai)
        printer.print(")")

      case ScCdr(pai, idn) =>
        printer.print("(cdr ")
        run(pai)
        printer.print(")")

      case ScNil(idn) => printer.print("'()")
    }
}
