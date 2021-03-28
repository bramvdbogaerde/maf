package maf.modular.contracts

import maf.modular.contracts.semantics.ScSharedSemantics
import maf.language.contracts.ScExp
import maf.language.contracts.ScLattice
import maf.core.Identity
import maf.language.contracts.ScSchemeLattice
import maf.language.contracts.ScIdentifier
import maf.language.contracts.lattices.ScConcreteValues
import maf.language.contracts.lattices.ScConcreteLattice
import maf.core.Identifier
import maf.language.scheme.interpreter.ConcreteValues.AddrInfo.VarAddr
import maf.language.scheme.interpreter.BaseSchemeInterpreter
import maf.language.scheme.interpreter.ConcreteSchemePrimitives
import maf.language.change.CodeVersion
import maf.language.scheme.SchemeExp
import maf.language.scheme.interpreter.ConcreteValues
import maf.util.benchmarks.Timeout
import maf.language.contracts.ScNil
import maf.language.scheme.interpreter.IO
import maf.language.scheme.interpreter.EmptyIO
import maf.language.scheme.SchemeFuncall
import maf.core.BasicEnvironment
import maf.language.scheme.interpreter.ConcreteValues.AddrInfo
import maf.core.Position

case class PrimitiveNotFound(name: String) extends Exception {
  override def getMessage(): String =
    s"Primitive $name not found"
}

object ScConcretePrimitives {
  import ConcreteValues._
  import scala.collection.immutable.Nil

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

  implicit override val lattice: ScSchemeLattice[Val, Addr] = new ScConcreteLattice {}

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

  case class MonadicSchemeInterpreter(var lstore: StoreCache) extends BaseSchemeInterpreter[()] with ConcreteSchemePrimitives {
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
  private lazy val allPrimitives =
    (interop.Primitives.allPrimitives.map(_._2) ++ List(`true?`, `false?`)).map(p => (p.name, p)).toMap

  override def primMap(v: String): Prim =
    allPrimitives.get(v).getOrElse(throw PrimitiveNotFound(v))

  override def primitives: List[String] =
    allPrimitives.map(_._1).toList

  override def primName(p: Prim): String = p.name

  override def throwBlameError(blame: ScLattice.Blame): ScEvalM[Unit] = ???

  override def callPrimitive(p: PrimitiveOperator, args: List[Argument]): ScEvalM[PostValue] = for {
    // install the current store
    _ <- withStoreCache { store => interop.lstore = store; unit }
    // call the primitive
    result <- pureWith {
      p.f.call(SchemeFuncall(p.e, args.map(_.e), p.e.idn), args.map(a => (a.e, a.v.pure)))
    }
    // propagate its changes the primitive made back to our monadic store
    _ <- modifyStoreCache { store => store.copy(map = store.map ++ interop.lstore.map) }
  } yield PS(result, ScNil()) // TODO: return a valid post value after applying the primitive

  override def call(clo: ScLattice.Clo[ScConcreteValues.ScAddr], operands: List[PostValue]): ScEvalM[PostValue] = {
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
  override def evalOpaque(refinements: Set[String]): ScEvalM[PostValue] = ???

  /**
   * Solves the given path condition and returns true if it is satisfiable, as we only work with concrete values
   * in concolic testing, there is no need to check the path conditions at runtime, hence, we only check them when
   * we explore the state space
   */
  override def solve(pc: ScExp): Boolean = true

}

/** A convience class to easily instantiate a concolic analysis */
abstract class ConcolicTesting(exp: ScExp) extends ConcolicAnalysisSemantics {
  import ConcreteValues.Value

  private var _results: List[Value] = List()
  private val root: ConcTree = ConcTree.root
  def results: List[Value] = _results

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
    ConcolicStore(primitives.map(p => (allocator.allocPrim(p), PS(ConcreteValues.Value.Primitive(p), ScIdentifier(p, Identity.none)))).toMap)
  }

  /**
   * Creates an initial context, starting from the given
   * root element.
   */
  private def initialContext(
    ): ConcolicContext =
    ConcolicContext(
      env = initialEnv,
      store = initialConcolicStore,
      pc = ScNil(),
      root = root
    )

  def analyzeWithTimeout(timeout: Timeout.T): Unit = {
    val (_, value) = eval(exp).m.run(initialContext())
    _results = value.get.pure :: _results
  }

  def analyze(): Unit = analyzeWithTimeout(Timeout.none)
  def analyzeOnce(): Value = {
    analyze()
    _results(0)
  }

  /**
   * Checks whether the given path condition is satisfiable, and
   * returns example outputs
   */
  def isSat(exp: ScExp): List[Val]
}
