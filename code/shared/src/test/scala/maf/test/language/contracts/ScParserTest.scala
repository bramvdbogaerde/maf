package maf.test.language.contracts

import maf.language.contracts._
import org.scalatest.flatspec.AnyFlatSpec
import maf.language.sexp.Value
import org.scalatest.matchers.should

class ScParserTest extends AnyFlatSpec with should.Matchers {
  private def compile(exp: String): ScExp =
    SCExpCompiler.read(exp)

  "A number" should "parse to an ScValue" in {
    compile("1") should matchPattern { case ScValue(Value.Integer(i), _) if i == 1 => }
  }

  "A boolean" should "parse to an ScValue" in {
    compile("#t") should matchPattern { case ScValue(Value.Boolean(true), _) => }
    compile("#f") should matchPattern { case ScValue(Value.Boolean(false), _) => }
  }

  "An identifier" should "parse to a ScIdentifier" in {
    compile("x") should matchPattern { case ScIdentifier("x", _) => }
  }

  "A lambda" should "parse to an ScLambda" in {
    compile("(lambda (x) x)") should matchPattern { case ScLambda(_, _, _) => }
  }

  "A lambda" should "have the correct arguments" in {
    val result = compile("(lambda (x) x)")
    result should matchPattern { case ScLambda(List(ScIdentifier("x", _)), _, _) => }
  }

  "A lambda" should "have the correct body" in {
    val result = compile("(lambda (x) x)")
    result should matchPattern { case ScLambda(_, ScBegin(List(ScIdentifier("x", _)), _), _) => }
  }

  "An if" should "parse to an ScIf" in {
    compile("(if x y z)") should matchPattern { case ScIf(ScIdentifier("x", _), ScIdentifier("y", _), ScIdentifier("z", _), _) =>
    }
  }

  "A begin" should "parse to an ScBegin" in {
    compile("(begin x y z)") should matchPattern { case ScBegin(List(ScIdentifier("x", _), ScIdentifier("y", _), ScIdentifier("z", _)), _) =>
    }
  }

  "A mon" should "parse to an ScMon" in {
    compile("(mon x y)") should matchPattern { case ScMon(ScIdentifier("x", _), ScIdentifier("y", _), _, _) =>
    }
  }

  "A higher order contract" should "parse to a ScHigherOrderContract" in {
    compile("(~> x y)") should matchPattern { case ScHigherOrderContract(ScIdentifier("x", _), ScIdentifier("y", _), _) =>
    }
  }

  "A dependent contract" should "parse to a ScDependentContract" in {
    compile("(~ x y)") should matchPattern { case ScDependentContract(List(ScIdentifier("x", _)), ScIdentifier("y", _), _) =>
    }
  }

  "A set!" should "parse to a ScSet" in {
    compile("(set! x 10)") should matchPattern {
      case ScSet(ScIdentifier("x", _), ScValue(Value.Integer(i), _), _) if i == 10 =>
    }
  }

  "A check" should "parse to a ScCheck" in {
    compile("(check int? 5)") should matchPattern { case ScCheck(ScIdentifier("int?", _), _, _) =>
    }
  }

  "An opaque" should "be able to have a refinement set" in {
    compile("(OPQ int?)") should matchPattern {
      case ScOpaque(_, refinements) if refinements.contains("int?") =>
    }
  }

  "An opaque" should "be able to be defined without refinements" in {
    compile("OPQ") should matchPattern {
      case ScOpaque(_, refinements) if refinements.isEmpty =>
    }
  }

  "An assumption" should "be able to be parsed" in {
    compile("(assume (x int?) (+ 1 1))") should matchPattern {
      case ScAssume(
            ScIdentifier("x", _),
            ScIdentifier("int?", _),
            ScFunctionAp(ScIdentifier("+", _), _, _, _),
            _
          ) =>
    }
  }

  "A top level definition with a variable" should "be able to be parsed" in {
    compile("(define x 10)") should matchPattern { case ScDefine(ScIdentifier("x", _), _, _) =>
    }
  }

  "A top level definition with a function" should "be able to be parsed" in {
    compile("(define (f x) x)") should matchPattern {
      case ScDefineFn(
            ScIdentifier("f", _),
            List(ScIdentifier("x", _)),
            ScBegin(List(ScIdentifier("x", _)), _),
            _
          ) =>
    }
  }

  "A top level defintion with a contract" should "be able to be parsed" in {
    compile("(define/contract (f x) (~> int? int?) x)") should matchPattern {
      case ScDefineAnnotatedFn(
            ScIdentifier("f", _),
            List(ScIdentifier("x", _)),
            _,
            ScBegin(List(ScIdentifier("x", _)), _),
            _
          ) =>
    }
  }

  "A conditional" should "be able to be parsed" in {
    compile("(cond (a b) (c d))") should matchPattern {
      case ScIf(
            ScIdentifier("a", _),
            ScBegin(List(ScIdentifier("b", _)), _),
            ScIf(ScIdentifier("c", _), ScBegin(List(ScIdentifier("d", _)), _), ScNil(_), _),
            _
          ) =>
    }
  }

  "A full program" should "be able to be parsed" in {
    compile("(define (f x) x) (define (f y) y) (define (f z) z)") should matchPattern {
      case ScProgram(exps, _) if exps.size == 3 =>
    }
  }

  "Contract" should "be able to be provided for arbitrary identifiers" in {
    compile("(provide/contract (n->f (~> exact-nonnegative-integer? church/c)))") should matchPattern {
      case ScProvideContracts(
            List(ScIdentifier("n->f", _)),
            List((ScHigherOrderContract(_, _, _))),
            _
          ) =>
    }
  }

  "A monitor with annotation" should "be parsed" in {
    compile("(mon @safe int? 10)") should matchPattern { case ScMon(_, _, _, Some("@safe")) =>
    }
  }

  "An application with annotation" should "be parsed" in {
    compile("(@safe f 10)") should matchPattern { case ScFunctionAp(_, _, _, Some("@safe")) =>
    }
  }

  "A cons" should "be parsed to ScCons" in {
    compile("(cons a b)") should matchPattern { case ScCons(ScIdentifier("a", _), ScIdentifier("b", _), _) =>
    }
  }

  "A car" should "be parsed to ScCar" in {
    compile("(car a)") should matchPattern { case ScCar(ScIdentifier("a", _), _) =>
    }
  }

  "A cdr" should "be parsed to ScCdr" in {
    compile("(cdr a)") should matchPattern { case ScCdr(ScIdentifier("a", _), _) =>
    }
  }

  "A contract with mumtiple arrows" should "be parsed into a contract with multiple domains" in {
    compile("(-> x y z)") should matchPattern { case ScDependentContract(List(ScIdentifier("x", _), ScIdentifier("y", _)), _, _) =>
    }
  }

  "A contract with arrow" should "be parsed" in {
    compile("(-> x y)") should matchPattern { case ScHigherOrderContract(ScIdentifier("x", _), ScIdentifier("y", _), _) =>
    }
  }

  "An assumed expression" should "be parsed to ScAssume" in {
    compile("(assumed name pure f)") should matchPattern {
      case ScAssumed(ScIdentifier("name", _), ScIdentifier("pure", _), ScIdentifier("f", _), _) =>
    }
  }

  "A given expression" should "be parsed to ScGiven" in {
    compile("(given name f)") should matchPattern { case ScGiven(ScIdentifier("name", _), ScIdentifier("f", _), _) =>
    }
  }
}
