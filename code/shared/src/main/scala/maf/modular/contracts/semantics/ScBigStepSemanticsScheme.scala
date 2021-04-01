package maf.modular.contracts.semantics
import maf.core.Identity
import maf.language.contracts.ScLattice._
import maf.language.contracts.{ScExp, _}
import maf.util.benchmarks.Timeout
import maf.language.sexp.Value
import maf.modular.contracts._

/**
 * This trait provides some methods that are useful for the semantics
 * of the SC language
 */
trait ScSemantics extends ScAbstractSemanticsMonadAnalysis {
  implicit val lattice: ScSchemeLattice[Val, Addr]
  val allocator: Allocator

  trait Allocator {

    /** Generic allocation based on identity */
    def alloc(idn: Identity): Addr

    /** Allocate a pair in the memory of the machine */
    def allocCons(
        car: PostValue,
        cdr: PostValue,
        carIdn: Identity,
        cdrIdn: Identity
      ): ScEvalM[PostValue]

    /** Allocates an address for a variable */
    def allocVar(id: ScIdentifier): Addr

    /** Allocates an address for a primitive */
    def allocPrim(name: String): Addr

    /**
     * Views an address from the abstract ScAddreses class
     * as an address for this semanticds
     */
    def view[Context](addr: ScAddresses[Context]): Addr
  }

  /**
   * Returns the primitive implementation associated with the given name
   *
   * @param v the name of the primitive to lookup
   * @return the implementation of the primitive with the given name
   */
  def primMap(v: String): Prim

  /** Returns a list of available primitives */
  def primitives: List[String]

  /** Returns the name of the given primitive */
  def primName(p: Prim): String

  /** Results in a blaming error */
  def throwBlameError(blame: Blame): ScEvalM[()]

  /**
   * A primitve wrapped with its corresponding
   * source location of its invocation.
   *
   * @param f the primitive function
   * @param e the source node corresponding to invocation location, used for store allocations and debugging purposes
   */
  case class PrimitiveOperator(f: Prim, e: ScExp)

  /**
   * The argument of a primitive application
   *
   * @param v the value of the argument
   * @param e the source node corresponding to the argument, used for store allocations and debugging purposes
   */
  case class Argument(v: PostValue, e: ScExp)

  /**
   * Calls the given primive with the given argument,
   * it requires the original  expression due to store allocation
   * functions that might use the identity of the original expression,
   * for concrete executions this is not used
   *
   * @param p the primitive that needs to be applied
   * @param args a list of arguments that need to be passed to the primitive
   * @return an computation that applies the given primitive and returns a value
   */
  def callPrimitive(p: PrimitiveOperator, args: List[Argument]): ScEvalM[PostValue]

  /** Same as <code>callPrimitive</code> but for singleton arguments */
  def callPrimitive(p: PrimitiveOperator, arg: Argument): ScEvalM[PostValue] = callPrimitive(p, List(arg))

  /** Calls the given closure with the given arguments */
  def call(clo: ScLattice.Clo[Addr], operands: List[PostValue]): ScEvalM[PostValue]

  /**
   * Looks up the given identifier and returns its address if defined, otherwise allocates an address
   *  and returns it
   */
  def lookupOrDefine(identifier: ScIdentifier): ScEvalM[Addr]

  def extended[X](ident: ScIdentifier)(c: Addr => ScEvalM[X]): ScEvalM[X] =
    extended(List(ident))(addrs => c(addrs.head))

  /** Extends the environment with the given list of identifiers and allocates memory slots for them */
  def extended[X](idents: List[ScIdentifier])(c: List[Addr] => ScEvalM[X]): ScEvalM[X] = {
    val addrs = idents.map(ident => allocator.allocVar(ident))
    val extended = sequence(idents.zip(addrs).map((addBindingToEnv(_, _)).tupled))
    local(extended, c(addrs))
  }

  /**
   * Auxilary function which serves as a way to identify
   * fully evaluated values used by the intepreter
   */
  def evaluatedValue(v: PostValue): ScEvalM[PostValue]

  /**
   * Returns true if the given path condition is satisfiable
   *
   * @param pc the path condition to solve for
   * @return true if the path condition is satisfiable otherwise false
   */
  def solve(pc: PC): Boolean
}

trait ScSharedSemantics extends ScSemantics {
  private lazy val primTrue = primMap("true?")
  private lazy val primFalse = primMap("false?")
  private lazy val primProc = primMap("procedure?")
  private lazy val primDep = primMap("dependent-contract?")
  private lazy val primCar = primMap("car")
  private lazy val primCdr = primMap("cdr")

  private var totalRuns = 0
  def eval(expr: ScExp): ScEvalM[PostValue] = (expr match {
    case ScBegin(expressions, _)                              => evalSequence(expressions)
    case ScIf(condition, consequent, alternative, _)          => evalIf(condition, consequent, alternative)
    case ScLetRec(idents, bindings, body, _)                  => evalLetRec(idents, bindings, body)
    case ScRaise(_, _)                                        => ???
    case ScSet(variable, value, _)                            => evalSet(variable, value)
    case ScFunctionAp(ScIdentifier("and", _), operands, _, _) => evalAnd(operands)
    case ScFunctionAp(operator, operands, _, _)               => evalFunctionAp(operator, operands)
    case v: ScValue                                           => evalValue(v)
    case exp: ScIdentifier                                    => evalIdentifier(exp)
    case ScMon(contract, expression, idn, _)                  => evalMon(contract, expression, idn)
    case ScOpaque(_, refinements)                             => evalOpaque(refinements)
    //case ScHigherOrderContract(domain, range, idn)            => eval(higherOrderToDependentContract(domain, range, idn))
    case ScDependentContract(domains, rangeMaker, _)     => evalDependentContract(domains, rangeMaker)
    case ScFlatContract(expression, _)                   => evalFlatContract(expression)
    case ScLambda(params, body, idn)                     => evalLambda(params, body, idn)
    case ScAssume(identifier, assumption, expression, _) => evalAssume(identifier, assumption, expression)
    case ScProgram(expressions, _)                       => evalProgram(expressions)
    case ScDefine(variable, expression, _)               => evalDefine(variable, expression)
    case ScDefineFn(name, parameters, body, idn)         => evalDefineFn(name, parameters, body, idn)
    case ScDefineAnnotatedFn(name, parameters, contract, expression, idn) =>
      evalDefineAnnotatedFn(name, parameters, contract, expression, idn)
    case ScProvideContracts(variables, contracts, _) => evalProvideContracts(variables, contracts)
    case exp @ ScCar(pai, _)                         => evalCar(pai, exp)
    case exp @ ScCdr(pai, _)                         => evalCdr(pai, exp)
    case ScNil(_)                                    => result(lattice.schemeLattice.nil)
  })

  def blame[X](blamedIdentity: Identity, blamingIdentity: Identity = Identity.none): ScEvalM[X] =
    withIgnoredIdentities { ignored =>
      if (!ignored.contains(blamedIdentity)) {
        throwBlameError(Blame(blamedIdentity, blamingIdentity))
      } else {
        unit
      }
    } >> void

  /** Creates a fresh identifier for the given opaque value */
  def fresh(v: Val): PostValue = if (lattice.isDefinitelyOpq(v)) value(v, ScModSemantics.freshIdent) else value(v, ScNil())

  def writeLocalForce(addr: Addr, value: PostValue): ScEvalM[()] =
    addToCache(addr -> value)

  def readPure(addr: Addr, storeCache: StoreCache): Val =
    storeCache.lookup(addr).map(_.pure).getOrElse(lattice.bottom)

  def evalAnd(operands: List[ScExp]): ScEvalM[PostValue] =
    operands match {
      case List(expr) =>
        eval(expr)
      case expr :: exprs =>
        eval(expr).flatMap { value =>
          cond(value, enrichOpaqueInStore(expr, evalAnd(exprs)), result(lattice.schemeLattice.bool(false)))
        }
    }

  def allocCons(
      car: PostValue,
      cdr: PostValue,
      carIdn: Identity,
      cdrIdn: Identity
    ): ScEvalM[PostValue] =
    ??? // TODO: use scheme primitives here

  def evalCar(pai: ScExp, carExp: ScExp): ScEvalM[PostValue] =
    eval(pai).flatMap(v => callPrimitive(PrimitiveOperator(primCar, carExp), Argument(v, pai)))

  def evalCdr(pai: ScExp, cdrExp: ScExp): ScEvalM[PostValue] =
    eval(pai).flatMap(v => callPrimitive(PrimitiveOperator(primCdr, cdrExp), Argument(v, pai)))

  def evalProvideContracts(variables: List[ScIdentifier], contracts: List[ScExp]): ScEvalM[PostValue] =
    sequenceLast(variables.zip(contracts).map { case (variable, contract) =>
      for {
        addr <- lookup(variable.name)
        value <- read(addr)
        // FIXME: this is possibly unsound. It serves as a hack to fix issues with flow insensitivity  and writeForce
        annotatedFn <-
          if (lattice.isDefinitelyArrow(value.pure)) pure(value)
          else
            for {
              evaluatedContract <- eval(contract)
              annotatedFn <- applyMon(evaluatedContract, value, contract.idn, variable.idn)
              _ <- writeForce(addr, annotatedFn)
            } yield annotatedFn
      } yield annotatedFn
    })

  def evalDefine(variable: ScIdentifier, expression: ScExp): ScEvalM[PostValue] = for {
    addr <- lookupOrDefine(variable)
    value <- eval(expression)
    _ <- write(addr, value)
  } yield value

  def evalDefineFn(
      name: ScIdentifier,
      parameters: List[ScParam],
      body: ScExp,
      idn: Identity
    ): ScEvalM[PostValue] =
    for {
      addr <- lookupOrDefine(name)
      lambda <- eval(ScLambda(parameters, body, idn))

      // The logic below for writing the lambda to the store is rather complicated.
      // The reason for this is that the value can be overwritten by a provide/contract,
      // in that case we would like to keep the contract if it points to the lambda,
      // otherwise we use a join.
      v <- readSafe(addr)
      _ <-
        if (lattice.isDefinitelyArrow(v.pure) && lattice.getArr(v.pure).size == 1) {
          // the address we try to write to contains a contract
          read(lattice.getArr(v.pure).head.e).flatMap { (wrappedValue) =>
            if (wrappedValue.pure == lambda.pure)
              // the contract wraps us, we don't overwrite (or join)
              unit
            else
              // the contract does not point to us, use a normal join
              write(addr, value(lambda.pure, name))
          }
        } else
          // the value on the adress is not a contract, use a normal join
          write(addr, value(lambda.pure, name))

    } yield lambda

  def evalDefineAnnotatedFn(
      name: ScIdentifier,
      parameters: List[ScParam],
      contract: ScExp,
      body: ScExp,
      idn: Identity
    ): ScEvalM[PostValue] =
    for {
      addr <- lookupOrDefine(name)
      lambda <- eval(ScLambda(parameters, body, idn))
      evaluatedContract <- eval(contract)
      monitoredFunction <- applyMon(evaluatedContract, lambda, contract.idn, idn)
      _ <- write(addr, value(monitoredFunction.pure, name))
    } yield monitoredFunction

  def evalProgram(expressions: List[ScExp]): ScEvalM[PostValue] = {
    def addBinding(name: ScIdentifier): ScEvalM[()] =
      lookupOrDefine(name) >> unit

    for {
      // extend the environment first
      _ <- sequence(expressions.map {
        case ScDefineAnnotatedFn(name, _, _, _, _) =>
          addBinding(name)

        case ScDefine(name, _, _) =>
          addBinding(name)

        case ScDefineFn(name, _, _, _) =>
          addBinding(name)

        case _ => unit
      })
      // evaluate all expressions in the program
      result <- sequenceLast(expressions.map(eval))
    } yield result
  }

  def evalSet(variable: ScIdentifier, value: ScExp): ScEvalM[PostValue] = for {
    addr <- lookup(variable.name)
    evaluatedValue <- eval(value) // TODO: check if we should not merge states here
    _ <- write(addr, evaluatedValue)
  } yield evaluatedValue

  def evalAssume(
      identifier: ScIdentifier,
      assumption: ScExp,
      expression: ScExp
    ): ScEvalM[PostValue] = ???

  def evalDependentContract(domains: List[ScExp], rangeMaker: ScExp): ScEvalM[PostValue] = {
    val domainAddrs = domains.map(domain => allocator.alloc(domain.idn))
    val rangeAddr = allocator.alloc(rangeMaker.idn)
    for {
      evaluatedDomains <- sequence(domains.zip(domainAddrs).map { case (domain, addr) =>
        for {
          evaluated <- eval(domain)
          _ <- write(addr, evaluated)
        } yield addr
      })
      evaluatedRangeMaker <- eval(rangeMaker)
      _ <- write(rangeAddr, evaluatedRangeMaker)
    } yield value(lattice.grd(Grd(evaluatedDomains, rangeAddr)), ScNil())
  }

  def evalMon(
      contract: ScExp,
      expression: ScExp,
      identity: Identity
    ): ScEvalM[PostValue] =
    // `mon` has two functions: wrapping a function to monitor it, and checking a flat contract
    for {
      evaluatedContract <- eval(contract)
      evaluatedExpression <- eval(expression)
      res <- applyMon(evaluatedContract, evaluatedExpression, contract.idn, expression.idn)
    } yield res

  def evalLambda(
      params: List[ScParam],
      body: ScExp,
      idn: Identity
    ): ScEvalM[PostValue] = withEnv { env =>
    val clo = Clo(idn, env, params.map(_.toScIdentifier), ScLambda(params, body, idn))
    result(lattice.closure(clo))
  }

  def evalFlatContract(exp: ScExp): ScEvalM[PostValue] = for {
    evaluatedExp <- eval(exp)
    res <- {
      val addr = allocator.alloc(exp.idn)
      write(addr, evaluatedExp).flatMap(_ => result(lattice.flat(Flat(addr))))
    }
  } yield res

  def evalLetRec(
      idents: List[ScIdentifier],
      bindings: List[ScExp],
      body: ScExp
    ): ScEvalM[PostValue] =
    for {
      // first evaluate the bindings
      _ <- sequence(idents.lazyZip(bindings).map { (ident, binding) =>
        extended(ident) { addr =>
          for {
            evaluatedBinding <- eval(binding)
            _ <- write(addr, evaluatedBinding)
          } yield ()
        }
      })

      // then evaluate the body in an extended environment
      evaluatedBody <- extended(idents)(_ => eval(body))
    } yield evaluatedBody

  def evalOpaque(refinements: Set[String]): ScEvalM[PostValue] =
    pure(value(lattice.opq(Opq(refinements)), ScIdentifier(ScModSemantics.genSym, Identity.none)))

  def evalValue(v: ScValue): ScEvalM[PostValue] = v.value match {
    case Value.Integer(i)   => pure(value(lattice.schemeLattice.number(i), v))
    case Value.Boolean(b)   => pure(value(lattice.schemeLattice.bool(b), v))
    case Value.Symbol(s)    => pure(value(lattice.schemeLattice.symbol(s), ScNil()))
    case Value.Real(r)      => pure(value(lattice.schemeLattice.real(r), v))
    case Value.Character(c) => pure(value(lattice.schemeLattice.char(c), v))
    case Value.Nil          => result(lattice.schemeLattice.nil)
    case Value.String(s)    => pure(value(lattice.schemeLattice.string(s), ScNil()))
  }

  def evalIdentifier(identifier: ScIdentifier): ScEvalM[PostValue] =
    lookup(identifier.name).flatMap(read)

  def evalSequence(expressions: List[ScExp]): ScEvalM[PostValue] =
    sequence(expressions.map(eval)).map(_.reverse.head)

  def evalFunctionAp(operator: ScExp, operands: List[ScExp]): ScEvalM[PostValue] = for {
    evaluatedOperator <- eval(operator)
    evaluatedOperands <- sequence(operands.map(eval))
    res <- applyFn(evaluatedOperator, evaluatedOperands, operator, operands)
  } yield res

  def evalIf(
      condition: ScExp,
      consequent: ScExp,
      alternative: ScExp
    ): ScEvalM[PostValue] =
    eval(condition).flatMap((value) => conditional(value, condition, consequent, alternative))

  def allocList(values: List[PostValue], idns: List[Identity]): ScEvalM[PostValue] = values match {
    case List() => result(lattice.schemeLattice.nil)
    case v :: values =>
      for {
        cdr <- allocList(values, idns.tail)
        carAddr = allocator.alloc(idns.head)
        cdrAddr = ScCdrAddr(carAddr)
        _ <- write(carAddr, v)
        _ <- write(allocator.view(cdrAddr), cdr)
      } yield ??? // TODO: use SchemeCons value(lattice.injectCons(Cons(carAddr, cdrAddr)))
  }

  var counter = 0
  def applyFn(
      operator: PostValue,
      operands: List[PostValue],
      syntacticOperator: ScExp,
      syntacticOperands: List[ScExp]
    ): ScEvalM[PostValue] = {

    // we have five distinct cases
    // 1. Primitive application
    // 2. User-defined function application
    // 3. Monitored function (Arr) application
    // 4. Flat contract application
    // 5. Application of an OPQ value

    // 1. Primitive application
    val primitiveAp = lattice.schemeLattice.getPrimitives(operator.pure).map { prim =>
      val schemePrim = primMap(prim)
      val actualOperator = PrimitiveOperator(schemePrim, syntacticOperator)
      val actualOperands = operands.zip(syntacticOperands).map(arg => (Argument.apply _).tupled(arg))
      callPrimitive(actualOperator, actualOperands)
    }

    // 2. Closure application
    val cloAp =
      lattice
        .getClosure(operator.pure)
        .map { clo => call(clo, operands) }

    // 3. Application of a monitored function (arrow)
    val arrAp = lattice.getArr(operator.pure).map { arr =>
      for {
        contract <- options(read(arr.contract).map((c) => lattice.getGrd(c.pure)))
        _ <- effectful {
          if (contract.domain.length != operands.length) {
            // TODO: maybe use a blame here instead of crashing the analysis
            throw new Exception("Arity of contract does not match arity of operands in application")
          }
        }

        values <- sequence {
          contract.domain.map(read).zip(operands.zip(syntacticOperands)).map { case (domain, (value, syn)) =>
            domain.flatMap(d => applyMon(d, value, arr.contract.idn, syn.idn))
          }
        }

        rangeMaker <- read(contract.rangeMaker)
        rangeContract <- applyFn(rangeMaker, values, ScNil(), syntacticOperands)
        fn <- read(arr.e)
        resultValue <- applyFn(fn, values, syntacticOperator, syntacticOperands)
        checkedResultValue <- applyMon(rangeContract, resultValue, contract.rangeMaker.idn, arr.e.idn)
      } yield checkedResultValue
    }

    // 4. Flat contract application
    val flatAp = lattice.getFlat(operator.pure).map { flat =>
      // TODO: make the flat contract record its results in order for the residuals to be correctly computed
      read(flat.contract).flatMap(value => applyFn(value, operands, syntacticOperator, syntacticOperands))
    }

    // 5. Application of an OPQ value, this yields simply an OPQ value
    val opqAp = lattice.getOpq(operator.pure).map { _ =>
      // TODO: simulate the repeated application of passed lambdas (HAVOC semantics)
      pure(value(lattice.opq(Opq()), ScModSemantics.freshIdent))
    }

    // 6. Application of thunk
    val thunk = lattice.getThunk(operator.pure).map(t => read(t.value))

    for {
      value <- nondets(primitiveAp ++ cloAp ++ arrAp ++ flatAp ++ opqAp ++ thunk)
      // conservatively remove variables from lambdas passed to the called function from the store cache.
      // this is necessary because these lambdas could be applied any number of times by the other functions
      // hence changing the state of the variables stored in the store cache
      _ <- sequence(operands.flatMap((o) => lattice.getClosure(o.pure)).map(c => evict(c.capturedVariables)))
    } yield value
  }

  def applyMon(
      evaluatedContract: PostValue,
      evaluatedExpression: PostValue,
      contractIdn: Identity,
      exprIdn: Identity
    ): ScEvalM[PostValue] = {

    // flat contract
    val flatContract = ifFeasible(primProc, evaluatedContract) {
      monFlat(evaluatedContract, evaluatedExpression, exprIdn, contractIdn)
    }

    // dependent contract
    val dependentContract = ifFeasible(primDep, evaluatedContract) {
      val aContract = allocator.alloc(contractIdn)
      val aExp = allocator.alloc(exprIdn)
      for {
        _ <- write(aContract, evaluatedContract)
        _ <- write(aExp, evaluatedExpression)
      } yield value(lattice.arr(Arr(contractIdn, exprIdn, aContract, aExp, false)))
    }

    nondets(Set(flatContract, dependentContract))
  }

  /** Same as monFlat but doesn't blame */
  def checkFlat(contract: PostValue, expressionvalue: PostValue): ScEvalM[PostValue] =
    monFlat(contract, expressionvalue, Identity.none, Identity.none, false)

  /**
   * Applies a flat contract to the given value, blames when the value violates
   * the contract, except when doBlame is false, it that case it simply generates
   * no successor states
   */
  def monFlat(
      contract: PostValue,
      expressionValue: PostValue,
      blamedIdentity: Identity,
      blamingIdentity: Identity = Identity.none,
      doBlame: Boolean = true
    ): ScEvalM[PostValue] =
    applyFn(contract,
            List(expressionValue),
            ScNil(),
            List(expressionValue.symbolic)
    ) // TODO: operator is specified to be nil, that might give an issue with store changing flat contracts
      .flatMap { value =>
        cond(
          value,
          pure(enrich(contract, expressionValue)),
          if (doBlame) blame(blamedIdentity, blamingIdentity) else void
        )
      }

  def cond[X](
      condition: PostValue,
      consequent: ScEvalM[X],
      alternative: ScEvalM[X],
      mustReplacePc: Boolean = true
    ): ScEvalM[X] = {
    val t = ifFeasible(primTrue, condition, mustReplacePc)(consequent)
    val f = ifFeasible(primFalse, condition, mustReplacePc)(alternative)
    nondet(t, f)
  }

  def conditional(
      conditionValue: PostValue,
      condition: ScExp,
      consequent: ScExp,
      alternative: ScExp
    ): ScEvalM[PostValue] = {
    val t = enrichOpaqueInStore(condition, eval(consequent))
    cond(conditionValue, t, eval(alternative))
  }

  def enrichOpaqueInStore(condition: ScExp, consequent: => ScEvalM[PostValue]): ScEvalM[PostValue] =
    // enrich the opaque value if it is a simple predicate on an opaque value
    // eg. (mon int? (letrec (y (OPQ int?)) (if (int? x) x y)) is safe
    isPredicateOnVariable(condition) match {
      case Some((operator, variable)) =>
        for {
          opAddr <- lookup(operator)
          varAddr <- lookup(variable)
          opValue <- read(opAddr)
          varValue <- read(varAddr)
          // a writeForce is sound and safe here, because we are either writing the same value to the varAddr, or writing
          // a refined opaque value. Either way, the value on that address still reaches a fixpoint (safety) and is
          // sound because we are not making something more specific which should not be made more specific.
          _ <- writeForce(varAddr, enrich(opValue, varValue))

          // add the constraint symbolicly to the correct variable
          //_ <- effectful {
          //  constrain(varAddr, condition)
          //}

          result <- consequent
        } yield result

      case None => consequent
    }

  def ifFeasible[X](
      op: Prim,
      value: PostValue,
      mustReplacePc: Boolean = true
    )(
      c: => ScEvalM[X]
    ): ScEvalM[X] =
    withPc(feasible(op, value)).flatMap {
      case Right(pc) =>
        if (mustReplacePc) replacePc(pc)(c) else c

      case Left(pc) =>
        if (mustReplacePc) replacePc(pc)(void) else void
    }

  def guardFeasible(op: Prim, value: PostValue): ScEvalM[()] = ifFeasible(op, value)(pure(()))

  /**
   * Checks whether applying the given primitive to the given value is returns possibly true or not.
   *
   * @param op the primitive to apply
   * @param value the value to check using op
   * @return an either value, being Left when the condition is not feasible, otherwise Right. In both cases the
   * value contained within the Either value will be the path condition
   */
  private def feasible(op: Prim, value: PostValue)(pc: PC): Either[PC, PC] = {
    val newPc = pc.and(ScFunctionAp(ScIdentifier(primName(op), Identity.none), List(value.symbolic), Identity.none))
    value.symbolic match {
      case _ if !lattice.schemeLattice.isTrue(run(callPrimitive(PrimitiveOperator(op, ScNil()), Argument(value, ScNil())).map(_.pure))) =>
        Left(newPc)

      case ScNil(_) =>
        Right(newPc)
      case _ =>
        if (solve(newPc)) Right(newPc) else Left(newPc)
    }
  }

  def refined(name: String, v: PostValue): PostValue = {
    val refinedValue = lattice
      .getOpq(v.pure)
      .map(opq => opq.copy(refinementSet = opq.refinementSet + name))
      .map(lattice.opq)
      .foldLeft(lattice.bottom)((acc, v) => lattice.join(acc, v))

    value(refinedValue, v.symbolic)
  }

  def enrich(operator: PostValue, value: PostValue): PostValue = operator.symbolic match {
    // if we have symbolic information we can enrich the opaque value with this symbolic information,
    case ScIdentifier(name, _) if lattice.isDefinitelyOpq(value.pure) && primitives.contains(name) =>
      refined(name, value)

    // if the operator is a primitive, then we can fetch its name from its value
    case _ if lattice.isDefinitelyOpq(value.pure) => lattice.getSymbolic(operator.pure).map(refined(_, value)).getOrElse(value)
    case _                                        => value
  }

  def isPredicateOnVariable(expr: ScExp): Option[(String, String)] = expr match {
    case ScFunctionAp(ScIdentifier(operator, _), List(ScIdentifier(variable, _)), _, _) => Some((operator, variable))
    case _                                                                              => None
  }
}

import maf.modular.contracts.domain.ScSchemePrimitives
trait ScBigStepSemanticsScheme extends ScModSemanticsScheme with ScSchemePrimitives with ScSchemeSemanticsMonad {

  trait IntraScBigStepSemantics extends IntraScAnalysisScheme with ScSharedSemantics {

    /**
     * Compute the context of the current component
     * @return a new context based on the environment of the component under analysis
     */
    def initialContext: Context = {
      //var storeCache: StoreCache = componentStore.view.mapValues(v => (v, ScNil())).toMap

      //primBindings.foreach { case (name, addr) =>
      //  val value = readPure(addr, storeCache)
      //  storeCache = storeCache + (addr -> ((value, ScIdentifier(name, Identity.none))))
      //  storeCache += (ScPrimAddr(name) -> ((lattice.schemeLattice.primitive(name), ScIdentifier(name, Identity.none))))
      //}

      //fnEnv.mapAddrs { (addr) =>
      //  val value = readPure(addr, storeCache)
      //  if (lattice.isDefinitelyOpq(value)) {
      //    storeCache += (addr -> ((value, ScIdentifier(ScModSemantics.genSym, Identity.none))))
      //  }
      //  addr
      //}

      //Context(env = fnEnv, cache = storeCache, pc = ScNil())
      ???
    }

    /**
     * Inject refinements in the store based on the contract of the function being
     * called, this is only possible when the compoennt is a GuardedFunctionCall
     */
    def injectRefinements: ScEvalM[()] = ???
    //view(component) match {
    //  case GuardedFunctionCall(domainContracts, _, _, _, _, _) =>
    //    // retrieve the list of addresses for the parameters of this function
    //    val variables = fnParams
    //    // now we refine these variables, and make their symbolic representation
    //    // equal to the application of its contract (if available)
    //    val refinements = domainContracts.zip(variables).map { case (addr, variable) =>
    //      for {
    //        contract <- read(addr)
    //        param <- read(variable)
    //        // TODO: check whether other type of contracts can also be used for refinements
    //        _ <- ifFeasible(primProc, contract) {
    //          checkFlat(contract, param)
    //        }
    //      } yield ()
    //    }

    //    sequence(refinements) >> unit
    //  case _ => unit
    //}

    /**
     * This function checks that the given value adheres to the range contract of the
     * current function (if it is a guarded function call)
     */
    //def checkRangeContract(v: PostValue): ScEvalM[PostValue] = view(component) match {
    //  case gf: GuardedFunctionCall[_] =>
    //    for {
    //      contract <- read(gf.rangeContract)
    //      _ <- applyMon(contract, v, gf.rangeIdentity, gf.lambda.idn)
    //    } yield v
    //  case _ => pure(v)
    //}

    def analyze(_ignored_timeout: Timeout.T): Unit = ???
    //    totalRuns += 1
    //    if (totalRuns > 100) {
    //      throw new Exception("Timeout exceeded")
    //    }

    //    println("================================")
    //    println(s"Analyzing component $component")

    //    val computation = (injectRefinements >> eval(fnBody) >>= checkRangeContract)
    //    val (value, sstore, _) = compute(computation)(initialContext)
    //    writeReturnStore(sstore)
    //    writeResult(value, component)

    //    println(s"Return value $value")
    //    println("==================================")
    //  }
    //}
  }

}
