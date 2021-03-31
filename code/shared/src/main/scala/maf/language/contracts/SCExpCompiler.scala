package maf.language.contracts

import maf.core.Identity
import maf.language.sexp.{SExp, SExpId, SExpPair, SExpParser, SExpValue}
import maf.language.sexp.Value

/** Compiles a program of S-expressions into a program of ScExp */
object SCExpCompiler {
  object :: {
    def unapply(value: SExp): Option[(SExp, SExp)] =
      value match {
        case SExpPair(car, cdr, _) => Some((car, cdr))
        case _                     => None
      }
  }

  object Ident {
    def unapply(value: SExpId): Option[(String)] = Some(value.id.name)
  }

  object IdentWithIdentity {
    def unapply(arg: SExpId): Option[(String, Identity)] =
      Some((arg.id.name, arg.idn))
  }

  object ListNil {
    def unapply(value: SExp): Option[(Identity)] = value match {
      case SExpValue(Value.Nil, idn) => Some((idn))
      case _                         => None
    }
  }

  case class SCExpCompilerException(message: String) extends Exception

  /* Transforms a quoted expression to an expression involving cons */
  def compile_quoted(expr: SExp): ScExp = expr match {
    case IdentWithIdentity(sym, idn) =>
      ScValue(Value.Symbol(sym), idn)

    case SExpValue(value, idn) =>
      ScValue(value, idn)

    case ListNil(idn) => ScNil(idn)
    case SExpPair(car, cdr, idn) =>
      ScFunctionAp.primitive("cons", List(car, cdr).map(compile_quoted), idn)
  }

  def compile_letrec_bindings(bindings: SExp): (List[ScIdentifier], List[ScExp]) =
    bindings match {
      case ListNil(_) => (List(), List())
      case ((IdentWithIdentity(name, idn) :: binding :: ListNil(_)) :: cdr) =>
        val (compiledNames, compiledBindings) = compile_letrec_bindings(cdr)
        (ScIdentifier(name, idn) :: compiledNames, compile(binding) :: compiledBindings)
      case _ => throw new Exception("invalid letrec binding")
    }

  def compile_params(s: SExp): List[ScParam] = s match {
    case IdentWithIdentity(args, args_idn) =>
      List(ScVarArgIdentifier(args, args_idn))

    case SExpPair(IdentWithIdentity(name, idn), cdr, _) =>
      ScIdentifier(name, idn) :: compile_params(cdr)
    case SExpValue(Value.Nil, _) => List()
  }

  def compile_sequence(s: SExp): List[ScExp] = s match {
    case SExpPair(exp, cdr, _) =>
      compile(exp) :: compile_sequence(cdr)
    case SExpValue(Value.Nil, _) => List()
  }

  /** Transforms a conditional-expression to an equivalent if-expression */
  def compile_branches(exp: SExp): ScExp = exp match {
    case ListNil(idn) => ScNil(idn)
    case SExpPair((condition :: expressions), rest, _) =>
      ScIf(compile(condition), ScBegin(compile_sequence(expressions), Identity.none), compile_branches(rest), exp.idn)
  }

  def compile_contracts(exp: SExp): ScExp = exp match {
    case ListNil(_) => ScProvideContracts(List(), List(), exp.idn)
    case SExpPair((IdentWithIdentity(name, idn) :: contract :: ListNil(_)), rest, _) =>
      compile_contracts(rest) match {
        case ScProvideContracts(identifiers, contracts, _) =>
          ScProvideContracts(
            ScIdentifier(name, idn) :: identifiers,
            compile(contract) :: contracts,
            exp.idn
          )
      }
  }

  /**
   * Compiles a named letrec to a normal letrec
   * @param functionName the name of the recursive function
   * @param paramNames the names of the parameters, these will be bound in the environment of the body
   * @param values the values to which to initially bind the parameters (as expressions)
   * @param body the uncompiled body of the letrec
   * @param idn an identity that the translated version of the letrec can assume
   * @return a function application of the recursive function defined by the letrec
   *         Example: (letrec loop ((x 10)) (loop (+ x 1))) becomes
   *         ((letrec (loop (lambda (x) (loop (+ x 1)))) loop) 10)
   */
  def named_letrec_compile(
      functionName: SExpId,
      paramNames: List[SExpId],
      values: List[SExp],
      body: SExp,
      idn: Identity
    ): ScExp = {
    val compiledBindings = values.map(compile)
    val compiledBody = compile(body)
    val fnName = ScIdentifier(functionName.id.name, functionName.idn)
    val compiledParamNames = paramNames.map(n => ScIdentifier(n.id.name, n.idn))
    val lambda = ScLambda(compiledParamNames, compiledBody, idn)
    val letrec = ScLetRec(List(fnName), List(lambda), fnName, idn)
    ScFunctionAp(letrec, compiledBindings, idn)
  }

  def compile_fn_contracts(exp: SExp): List[ScExp] = exp match {
    case ListNil(_) => List()
    case contract :: contracts =>
      val compiledContract = compile(contract)
      val compiledContracts = compile_fn_contracts(contracts)
      compiledContract :: compiledContracts
  }

  def compile(prog: SExp): ScExp = prog match {
    case IdentWithIdentity("OPQ", idn) =>
      ScOpaque(idn, Set())

    case IdentWithIdentity("OPQ", idn) :: IdentWithIdentity(refinement, refinementIdn) :: ListNil(
          _
        ) =>
      ScOpaque(idn, Set(refinement))

    case Ident("set!") :: IdentWithIdentity(name, idn) :: exp :: SExpValue(Value.Nil, _) =>
      ScSet(ScIdentifier(name, idn), compile(exp), prog.idn)

    case Ident("set!") :: _ =>
      throw new Exception(s"invalid set! expression at ${prog.idn}")

    case Ident("flat") :: expr :: ListNil(_) =>
      ScFlatContract(compile(expr), prog.idn)

    case (Ident("~>") | Ident("->")) :: domain :: range :: ListNil(_) =>
      val domainCompiled = compile(domain)
      val rangeCompiled = compile(range)
      ScHigherOrderContract(domainCompiled, rangeCompiled, prog.idn)

    case (Ident("~>") | Ident("->")) :: contracts =>
      val compiledContracts = compile_fn_contracts(contracts)
      val domainContracts = compiledContracts.init
      val rangeContract = compiledContracts.last
      val rangeMaker =
        ScLambda(List(ScVarArgIdentifier("0args", Identity.none)), rangeContract, rangeContract.idn)

      ScDependentContract(domainContracts, rangeMaker, prog.idn)

    case Ident("~") :: domain :: range :: ListNil(_) =>
      val domainCompiled = compile(domain)
      val rangeCompiled = compile(range)
      ScDependentContract(List(domainCompiled), rangeCompiled, prog.idn)

    case SExpId(identifier) => ScIdentifier(identifier.name, prog.idn)
    case (Ident("lambda") | Ident("λ")) :: params :: expressions =>
      val compiledParams = compile_params(params)
      val compiledExpression = compile_sequence(expressions)
      ScLambda(compiledParams, ScBegin(compiledExpression, Identity.none), prog.idn)

    case Ident("lambda") :: _ => throw new Exception(s"invalid syntax lambda at ${prog.idn.pos}")

    case Ident("letrec") :: (IdentWithIdentity(name, idn) :: bindingExpression :: ListNil(_)) :: expression :: ListNil(
          _
        ) =>
      val compiledBindingExpression = compile(bindingExpression)
      val compiledExpression = compile(expression)
      ScLetRec(List(ScIdentifier(name, idn)), List(compiledBindingExpression), compiledExpression, prog.idn)

    case Ident("letrec") :: ((fnName: SExpId) :: (varName: SExpId) :: bindingExpression :: ListNil(
          _
        )) :: expression :: ListNil(_) =>
      named_letrec_compile(fnName, List(varName), List(bindingExpression), expression, prog.idn)

    // this is a form of let/letrec that is the most often found in R5RS
    case (Ident("letrec") | Ident("let")) :: (bindings @ SExpPair(_, _, _)) :: expressions =>
      val (compiledNames, compiledBindings) = compile_letrec_bindings(bindings)
      val compiledExpressions = compile_sequence(expressions)
      ScLetRec(compiledNames, compiledBindings, ScBegin(compiledExpressions, Identity.none), prog.idn)

    case Ident("letrec") :: _ =>
      throw new Exception(s"invalid syntax for letrec at ${prog.idn.pos}")

    case Ident("mon") :: Ident(annotation) :: contract :: expression :: ListNil(_) =>
      val compiledContract = compile(contract)
      val compiledExpression = compile(expression)
      ScMon(compiledContract, compiledExpression, prog.idn, Some(annotation))

    case Ident("mon") :: contract :: expression :: ListNil(_) =>
      val compiledContract = compile(contract)
      val compiledExpression = compile(expression)
      ScMon(compiledContract, compiledExpression, prog.idn)

    case Ident("if") :: condition :: consequent :: alternative :: ListNil(_) =>
      val compiledCondition = compile(condition)
      val compiledConsequent = compile(consequent)
      val compiledAlternative = compile(alternative)
      ScIf(compiledCondition, compiledConsequent, compiledAlternative, prog.idn)

    case Ident("raise") :: SExpValue(Value.String(str), _) =>
      ScRaise(str, prog.idn)

    case Ident("begin") :: expressions =>
      ScBegin(compile_sequence(expressions), prog.idn)

    case Ident("check") :: contract :: expression :: ListNil(_) =>
      val compiledContract = compile(contract)
      val compiledExpression = compile(expression)
      ScCheck(compiledContract, compiledExpression, prog.idn)

    case Ident("assume") :: (IdentWithIdentity(x, idn) :: assumption :: ListNil(_)) :: expression :: ListNil(
          _
        ) =>
      val compiledAssumption = compile(assumption)
      val compiledExpression = compile(expression)
      ScAssume(ScIdentifier(x, idn), compiledAssumption, compiledExpression, prog.idn)

    case Ident("define") :: IdentWithIdentity(x, idn) :: expression :: ListNil(_) =>
      val compiledExpression = compile(expression)
      ScDefine(ScIdentifier(x, idn), compiledExpression, prog.idn)

    case Ident("define") :: (IdentWithIdentity(f, idn) :: params) :: expressions =>
      val compiledSequence = ScBegin(compile_sequence(expressions), expressions.idn)
      val compiledParams = compile_params(params)
      ScDefineFn(ScIdentifier(f, idn), compiledParams, compiledSequence, prog.idn)

    case Ident("define/contract") :: (IdentWithIdentity(f, idn) :: params) :: contract :: expressions =>
      val compiledSequence = ScBegin(compile_sequence(expressions), expressions.idn)
      val compiledParams = compile_params(params)
      val compiledContract = compile(contract)
      ScDefineAnnotatedFn(
        ScIdentifier(f, idn),
        compiledParams,
        compiledContract,
        compiledSequence,
        prog.idn
      )

    case Ident("cons") :: car :: cdr :: ListNil(_) =>
      val compiledCar = compile(car)
      val compiledCdr = compile(cdr)
      ScFunctionAp.primitive(
        "cons",
        List(
          compiledCar,
          compiledCdr
        ),
        prog.idn
      )

    case Ident("car") :: pai :: ListNil(_) =>
      val compiledPai = compile(pai)
      ScCar(compiledPai, prog.idn)

    case Ident("cdr") :: pai :: ListNil(_) =>
      val compiledPai = compile(pai)
      ScCdr(compiledPai, prog.idn)

    case Ident("cond") :: branches =>
      compile_branches(branches)

    case Ident("provide/contract") :: contracts =>
      compile_contracts(contracts)

    // Symbols
    case Ident("quote") :: IdentWithIdentity(s, idn) :: ListNil(_) =>
      ScValue(Value.Symbol(s), idn)

    // Other quoted values
    case Ident("quote") :: expr :: ListNil(_) =>
      compile_quoted(expr)

    case Ident(annotation) :: operator :: arguments if annotation.startsWith("@") =>
      ScFunctionAp(compile(operator), compile_sequence(arguments), prog.idn, Some(annotation))

    case operator :: arguments =>
      ScFunctionAp(compile(operator), compile_sequence(arguments), prog.idn)

    case IdentWithIdentity(name, idn) =>
      ScIdentifier(name, idn)

    case SExpValue(value, _) => ScValue(value, prog.idn)
  }

  def read(s: String): ScExp = {
    val sexprs = SExpParser.parse(s)
    if (sexprs.size > 1) {
      ScProgram(sexprs.map(SCExpCompiler.compile), sexprs.head.idn)
    } else {
      SCExpCompiler.compile(sexprs.head)
    }
  }

  /**
   * Prepends the prelude to the beginning of the program
   * @param s the program to read and compile into the an AST of the contract language
   * @return an AST of the contract language
   */
  def preludedRead(s: String): ScExp = {
    import ScPrelude._
    read(preludeString ++ s"\n$s")
  }
}
