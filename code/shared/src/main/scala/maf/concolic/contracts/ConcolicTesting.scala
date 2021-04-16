package maf.concolic.contracts

import maf.concolic.contracts.exploration.{ExplorationStrategy, Nearest}
import maf.core.{BasicEnvironment, Identifier, Identity, Position}
import maf.language.change.CodeVersion
import maf.language.contracts.ScLattice.Opq
import maf.language.contracts._
import maf.language.contracts.lattices.ScConcreteValues.{ClosureValue, GrdValue}
import maf.language.contracts.lattices.{ScConcreteLattice, ScConcreteValues}
import maf.language.scheme.interpreter.ConcreteValues.AddrInfo
import maf.language.scheme.interpreter.ConcreteValues.AddrInfo.VarAddr
import maf.language.scheme.interpreter._
import maf.language.scheme.{SchemeExp, SchemeFuncall}
import maf.modular.contracts.ScAddresses
import maf.modular.contracts.semantics.{ScModSemantics, ScSharedSemantics}
import maf.util.benchmarks.Timeout
import maf.language.contracts.ScLattice.AssumedValue
import maf.language.contracts.lattices.ScConcreteValues.ConsValue
import maf.language.contracts.ScLattice.AssumptionGuard

case class PrimitiveNotFound(name: String) extends Exception {
  override def getMessage(): String =
    s"Primitive $name not found"
}

object ScConcretePrimitives {
  import ConcreteValues._

  import scala.collection.immutable.Nil

  /** Checks whether two objects are equal. */
  object `equal?` extends SimplePrim {
    override val name: String = "equal?"

    override def call(args: List[ConcreteValues.Value], position: Position.Position): ConcreteValues.Value = args match {
      case Value.Undefined(_) :: Value.Undefined(_) :: Nil => Value.Bool(true)
      case (a: Value.Clo) :: (b: Value.Clo) :: Nil         => Value.Bool(a == b)
      case Value.Primitive(a) :: Value.Primitive(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Str(a) :: Value.Str(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Symbol(a) :: Value.Symbol(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Real(a) :: Value.Real(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Bool(a) :: Value.Bool(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Character(a) :: Value.Character(b) :: Nil =>
        Value.Bool(a == b)
      case Value.Nil :: Value.Nil :: Nil                                  => Value.Bool(true)
      case Value.Vector(_, elems, _) :: Value.Vector(_, elems2, _) :: Nil => Value.Bool(elems == elems2)
      case Value.Void :: Value.Void :: Nil =>
        Value.Bool(true)
      case ClosureValue(clo1) :: ClosureValue(clo2) :: Nil =>
        Value.Bool(clo1 == clo2)
      case a :: b :: Nil => throw new Exception(s"unsupported values for equality, $a and $b")
      case _             => throw new Exception(s"expected 2 arguments got ${args.size}")
    }

  }

  object `dependent-contract?` extends SimplePrim {
    override val name: String = "dependent-contract?"

    override def call(args: List[ConcreteValues.Value], position: Position.Position): ConcreteValues.Value = {
      args match {
        case GrdValue(_) :: Nil => {
          Value.Bool(true)
        }
        case _ :: Nil => {
          Value.Bool(false)
        }
        case _ => throw new Exception(s"$name: invalid number of arguments, expected 1 got ${args.size}")
      }
    }
  }

  object `procedure?` extends SimplePrim {
    override val name: String = "procedure?"
    override def call(args: List[ConcreteValues.Value], position: Position.Position): ConcreteValues.Value = args match {
      case ClosureValue(_) :: Nil      => Value.Bool(true)
      case (_: Value.Clo) :: Nil       => Value.Bool(true)
      case (_: Value.Primitive) :: Nil => Value.Bool(true)
      case _ :: Nil                    => Value.Bool(false)
      case _                           => throw new Exception(s"$name: invalid number of arguments, expected 1 got ${args.size}")
    }
  }

  object `true?` extends SimplePrim {

    override val name: String = "true?"

    override def call(args: List[ConcreteValues.Value], position: Position.Position): ConcreteValues.Value = args match {
      case Value.Bool(false) :: Nil            => Value.Bool(false)
      case _ :: scala.collection.immutable.Nil => Value.Bool(true)
      case _                                   => throw new Exception(s"$name: invalid number of arguments, expected 1 got ${args.size}")
    }
  }

  object `false?` extends SimplePrim {

    override val name: String = "false?"

    override def call(args: List[ConcreteValues.Value], position: Position.Position): ConcreteValues.Value = args match {
      case Value.Bool(false) :: Nil            => Value.Bool(true)
      case _ :: scala.collection.immutable.Nil => Value.Bool(false)
      case _                                   => throw new Exception(s"$name: invalid number of arguments, expected 1 got ${args.size}")
    }
  }
}

trait ConcolicAnalysisSemantics extends ScSharedSemantics with ConcolicMonadAnalysis {
  import ScConcreteValues._

  override def evict(addresses: List[ScConcreteValues.ScAddr]): ScEvalM[Unit] = unit

  override type Prim = ConcreteValues.Prim

  implicit override val lattice: ScSchemeLattice[Val, Addr] = new ScConcreteLattice {
    override def assumedValue(v: AssumedValue[Addr]): Val =
      ??? // not supposed to happen

    override def isDefinitivelyAssumedValue(v: Val): Boolean = false

    override def getAssumedValues(v: Val): Set[AssumedValue[Addr]] =
      Set() // not supposed to happen

    override def getAssumptionGuard(v: Val): AssumptionGuard = v match {
      case AssumptionGuardValue(ass) => ass
      case _ =>
        throw new Exception("Value is not an assumption guard")
    }

    override def assumptionGuard(v: AssumptionGuard): Val =
      AssumptionGuardValue(v)
  }

  private var firstFree: Int = 0
  private def addr: Int = {
    val newAddr = firstFree
    firstFree += 1
    newAddr
  }

  override val allocator: Allocator = new Allocator {

    override def alloc(idn: Identity): ScConcreteValues.ScAddr =
      (addr, AddrInfo.IdnAddr(idn))

    override def allocCons(
        car: PS,
        cdr: PS,
        carIdn: Identity,
        cdrIdn: Identity
      ): ScEvalM[PS] = ???

    override def allocVar(id: ScIdentifier): ScConcreteValues.ScAddr =
      (addr, VarAddr(Identifier(id.name, id.idn)))

    override def allocPrim(name: String): ScConcreteValues.ScAddr =
      // addresses to primitives are deterministicly generated
      (0, AddrInfo.PrmAddr(name))

    override def view[Context](addr: ScAddresses[Context]): ScConcreteValues.ScAddr =
      // safety: as our addresses in the store are always ScConcreteAddress'es it is impossible that
      // view will be called with a different type of address, hence the asInstanceOf call never fails at runtime
      addr.asInstanceOf[ScConcreteValues.ScAddr]

  }

  case class MonadicSchemeInterpreter(var lstore: StoreCache) extends BaseSchemeInterpreter[Unit] with ConcreteSchemePrimitives {
    override def run(
        program: SchemeExp,
        timeout: Timeout.T,
        version: CodeVersion.Version
      ): ConcreteValues.Value =
      throw new Exception("Monadic Scheme interpreter is not designed to be run on its own")

    override def newAddr(meta: ConcreteValues.AddrInfo): (Int, ConcreteValues.AddrInfo) = {
      (addr, meta)
    }

    override def extendStore(a: ConcreteValues.Addr, v: ConcreteValues.Value): Unit = {
      // TODO: generate symbolic representation of Scheme value or do a gensym
      lstore = lstore.extend(a, PS(ConcreteSchemeValue(v), ScNil())).asInstanceOf[StoreCache]
    }

    override def lookupStore(a: ConcreteValues.Addr): ConcreteValues.Value = {
      lstore.lookup(a).map(v => v.pure).get
    }

    override val stack: Boolean = false

    override def stackedException[R](msg: String): R = throw new Exception(msg)

    override val io: IO = new EmptyIO()
  }

  import ScConcretePrimitives._
  private def interop = new MonadicSchemeInterpreter(ConcolicStore(Map()))
  private def scPrimitives =
    List(`true?`, `false?`, `dependent-contract?`, `procedure?`, `equal?`)

  private lazy val allPrimitives =
    (interop.Primitives.allPrimitives.map(_._2) ++ scPrimitives).map(p => (p.name, p)).toMap

  override def primMap(v: String): Prim =
    allPrimitives.get(v).getOrElse(throw PrimitiveNotFound(v))

  override def primitives: List[String] =
    allPrimitives.map(_._1).toList

  override def primName(p: Prim): String = p.name

  override def throwBlameError(blame: ScLattice.Blame): ScEvalM[Unit] =
    error(ConcTree.blame(BlameValue(blame)))

  override def eval(expr: ScExp): ScEvalM[PostValue] =
    expr match {
      // this is not implemented as a primitive because the primitives in
      // the concolic tester do not have access to the store
      case ScFunctionAp(ScIdentifier("domain-contract", _), List(contract, n), _, _) =>
        for {
          evaluatedContract <- eval(contract)
          evaluatedN <- eval(n)
          domain <- {
            val n = evaluatedN.pure.asInstanceOf[ConcreteValues.Value.Integer]
            val arr = evaluatedContract.pure.asInstanceOf[ArrValue]
            read(arr.arr.contract)
              .flatMap(grd => read(grd.pure.asInstanceOf[GrdValue].grd.domain(n.n.toInt)))
          }
        } yield domain

      case ScFunctionAp(ScIdentifier("domain-contract", _), args, _, _) =>
        throw new Exception(s"domain-contract: arity mismatch, expected 2 but got ${args.size} arguments")

      case _ => super.eval(expr)
    }

  override def callPrimitive(p: PrimitiveOperator, args: List[Argument]): ScEvalM[PostValue] = for {
    // install the current store
    _ <- withStoreCache { store => interop.lstore = store; unit }
    // call the primitive
    result <- pureWith {
      p.f.call(SchemeFuncall(p.e, args.map(_.e), p.e.idn), args.map(a => (a.e, a.v.pure)))
    }
    // propagate its changes the primitive made back to our monadic store
    _ <- modifyStoreCache { store => store.copy(map = store.map ++ interop.lstore.map) }
  } yield PS(result, ScFunctionAp.primitive(p.f.name, args.map(_.v.symbolic), Identity.none))

  override def call(
      clo: ScLattice.Clo[ScConcreteValues.ScAddr],
      operands: List[PostValue],
      syntacticOperands: List[ScExp]
    ): ScEvalM[PostValue] = {
    val addresses = clo.parameters.map(p => allocator.allocVar(p))
    val names = clo.parameters.map(_.name)
    local(
      (_) => clo.env.extend(names.zip(addresses)).asInstanceOf[Env], {
        sequence(
          addresses.zip(operands).map((write(_, _)).tupled)
        ) >> eval(clo.lambda.body)
      }
    )
  }

  // TODO: check if this is generic enough to be placed higher in the hierachy
  override def lookupOrDefine(identifier: ScIdentifier): ScEvalM[ScConcreteValues.ScAddr] = modifyEnv { env =>
    env.lookup(identifier.name) match {
      case Some(_) => env
      case None =>
        val addr = allocator.allocVar(identifier)
        env.extend(identifier.name, addr)
    }
  } >> withEnv { env => pure(env.lookup(identifier.name).get) }

  /**
   * The evaluation of opaque values differs from the regular evaluation, as in this
   * case an oracle needs to be consulted that is used to generate an initial set of values
   */
  override def evalOpaque(refinements: Set[String]): ScEvalM[PostValue] = {
    val symbolicVariable = ScModSemantics.genSym
    addSymbolicVariable(symbolicVariable) >> withContext { context =>
      val id = ScIdentifier(symbolicVariable, Identity.none)
      val value = context.inputGenerator.generate(Opq(refinements), id)
      pure(PS(context.inputs.get(symbolicVariable).getOrElse(value), id))
    }
  }

  /**
   * Throw an error that the assumption has failed.
   *
   * @param name the name of the assumption that is violated
   * @param idn the identity of the assertion that must have been valid for the assumption
   * to be valid
   */
  protected def throwAssumptionFailure(name: ScIdentifier, idn: Identity): ScEvalM[Unit] =
    error(ConcTree.assumptionViolated(name.name))

  override def evalGiven(
      name: ScIdentifier,
      expr: ScExp,
      idn: Identity
    ): ScEvalM[PostValue] =
    eval(expr).flatMap(value => cond(value, result(lattice.schemeLattice.nil), throwAssumptionFailure(name, idn) >> void))

  /** In the concrete execution, this does not have any effects */
  override def evalAssumed(
      name: ScIdentifier,
      simpleContract: ScIdentifier,
      expr: ScExp,
      arguments: List[ScExp],
      idn: Identity
    ): ScEvalM[PostValue] = eval(expr)

  /**
   * Solves the given path condition and returns true if it is satisfiable, as we only work with concrete values
   * in concolic testing, there is no need to check the path conditions at runtime, hence, we only check them when
   * we explore the state space
   */
  override def solve(pc: ScExp): Boolean = true

}

/**
 *  A convience class to easily instantiate a concolic analysis
 *
 *  @param exp the expression to concolically test
 *  @param maxdepth (optional) the maximum depth of recursion we allow to be used.
 *  It does not result in an error when this maximal depth is reached, rather it records
 *  a stackoverflow error in the exploration tree, and continues the analysis.
 */
abstract class ConcolicTesting(
    exp: ScExp,
    defaultMaxDepth: Int = 100,
    exploration: ExplorationStrategy = Nearest)
    extends ConcolicAnalysisSemantics {
  import ConcreteValues.Value

  private var _results: List[Value] = List()
  private var _tree: ConcTree = ConcTree.empty
  private var maxdepth = defaultMaxDepth

  /** A map from assumption names to location where they were violated */
  private var assumptionViolations: Map[String, Identity] = Map()
  private val root: maf.concolic.contracts.ConcTree = maf.concolic.contracts.ConcTree.empty

  def tree: ConcTree = _tree
  def results: List[Value] = _results.filterNot(_ == Value.Nil)
  def violated: Set[String] = assumptionViolations.keySet

  override protected def throwAssumptionFailure(name: ScIdentifier, idn: Identity): ScEvalM[Unit] = {
    effectful { assumptionViolations += (name.name -> idn) } >>
      super.throwAssumptionFailure(name, idn)
  }

  /** Overrides the original `call` to take the maximum recursion depth into account */
  override def call(
      clo: ScLattice.Clo[ScConcreteValues.ScAddr],
      operands: List[PS],
      syntacticOperands: List[ScExp]
    ): ScEvalM[PS] = unit.flatMap(_ => {
    if (maxdepth > 0) {
      maxdepth = maxdepth - 1
      super.call(clo, operands, syntacticOperands)
    } else {
      error(ConcTree.stackoverflow) >> void
    }
  })

  /**
   * Creates an initial environment with all the necessary primitives
   * mapped to primitive addresses
   */
  private def initialEnv: BasicEnvironment[ScConcreteValues.ScAddr] = {
    BasicEnvironment(primitives.map(p => (p, allocator.allocPrim(p))).toMap)
  }

  /**
   * Creates an initial store where addresses of the primitives are
   * mapped to the actual primitives
   */
  private def initialConcolicStore: ConcolicStore = {
    ConcolicStore(primitives.map(p => (allocator.allocPrim(p), PS(ConcreteValues.Value.Primitive(p), ScNil()))).toMap)
  }

  /**
   * Creates an initial context, starting from the given
   * root element.
   */
  private def initialContext(inputs: Map[String, Value] = Map()): ConcolicContext =
    ConcolicContext(
      env = initialEnv,
      store = initialConcolicStore,
      pc = ScNil(),
      root = root,
      inputGenerator = InputGenerator(Map())
    )

  protected def reset: Unit = {
    // TODO: put counter for gensym in the state of the concolic tester
    maxdepth = defaultMaxDepth
    ScModSemantics.reset
  }

  def analyzeWithTimeout(timeout: Timeout.T): Unit = {
    var next: Option[Map[String, Val]] = Some(Map())
    var ccontext = initialContext()
    var iters = 0
    do {
      reset
      val inputs = next.get
      println(s"Got inputs $inputs")
      val result = analysisIteration(initialContext().copy(root = ccontext.root, inputs = inputs))
      ccontext = result._1
      val value = result._2

      _results = value :: _results

      val nt = nextTarget(ccontext)
      next = nt._2
      ccontext = nt._1

      iters = iters + 1
    } while (next.isDefined && !timeout.reached && iters < 10)

    _tree = ccontext.root
    println(_results)
    println(ccontext.root)
    println(s"done in ${iters} iterations")
  }

  def analyze(): Unit = analyzeWithTimeout(Timeout.none)
  def analyzeOnce(context: ConcolicContext = initialContext()): Value =
    analysisIteration(context)._2

  private def nextTarget(context: ConcolicContext): (ConcolicContext, Option[Map[String, Value]]) = {
    var tree = context.root
    val walker = exploration.start(tree, context.trail)
    def find: Option[Map[String, Val]] = {
      walker.next() match {
        case Some((pc, trail)) =>
          isSat(pc) match {
            case Some(model) =>
              Some(model)
            case _ =>
              tree = tree.replaceAt(trail, ConcTree.unsat(pc))
              find
          }
        case None => None
      }
    }
    val result = find
    (context.copy(root = tree), result)
  }

  private def analysisIteration(context: ConcolicContext = initialContext()): (ConcolicContext, Value) = {
    // evaluate the expression in the given context
    val (finalContext, value) = eval(exp).m.run(context)

    // set the final node to a value node
    val root = if (value.isDefined) {
      finalContext.root.replaceAt(finalContext.trail.reverse, ConcTree.value(value.get.pure, finalContext.pc))
    } else {
      finalContext.root
    }

    (finalContext.copy(root = root), value.map(_.pure).getOrElse(Value.Nil))
  }

  /**
   * Checks whether the given path condition is satisfiable, and
   * returns example outputs
   */
  def isSat(exp: ScExp): Option[Map[String, Val]]
}
