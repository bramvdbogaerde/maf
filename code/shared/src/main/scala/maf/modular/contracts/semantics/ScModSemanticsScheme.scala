package maf.modular.contracts.semantics

import maf.core.Position.Position
import maf.core.{Address, Environment, Identity}
import maf.language.contracts.ScLattice.Blame
import maf.language.contracts.{ScExp, ScIdentifier, ScLambda, ScLattice, ScParam}
import maf.modular.{DestructiveStore, GlobalStore, LocalStore, LocalStoreMap, ModAnalysis, ReturnAddr, ReturnValue}
import maf.core.Lattice
import maf.lattice.interfaces.BoolLattice
import maf.language.contracts.ScSchemeDomain
import maf.language.scheme.primitives.SchemeInterpreterBridge
import maf.language.scheme.SchemeExp
import maf.language.scheme.SchemeLambdaExp
import maf.language.CScheme.TID
import maf.language.scheme.primitives.SchemePrimitive
import maf.language.contracts.ScNil

import maf.modular.contracts._
import maf.modular.contracts.domain._
import maf.modular.contracts.analyses._
import maf.core.StoreMap
import maf.core.BasicEnvironment

trait ScModAnalysisSemanticsMonad extends ScModSemanticsScheme with ScAbstractSemanticsMonadAnalysis {
  override type Addr = super[ScModSemanticsScheme].Addr;
  override type Env = super[ScModSemanticsScheme].Env;
  override type StoreCache = StoreMap[Addr, PostValue]
  override type M[X] = AnalysisMonad[X]
  override type PostValue = (Val, ScExp)
  override type Val = super[ScModSemanticsScheme].Value;

  case class Context(
      env: BasicEnvironment[Addr],
      pc: PC,
      cache: StoreCache,
      ignoredIdn: List[Identity] = List()) {
    def store: Store = ??? // cache.view.mapValues(_.pure).toMap
  }
  case class AnalysisMonad[X](run: Context => Set[(Context, X)])
  override def abstractMonadInstance: ScAbstractSemanticsMonad[M] = new ScAbstractSemanticsMonad[AnalysisMonad] {

    override def pure[X](v: => X): AnalysisMonad[X] =
      AnalysisMonad((context) => List((context, v)).toSet)

    override def flatMap[X, Y](m: AnalysisMonad[X], f: X => AnalysisMonad[Y]): AnalysisMonad[Y] =
      AnalysisMonad((context) =>
        m.run(context).flatMap { case (updatedContext, value) =>
          f(value).run(updatedContext)
        }
      )

    override def void[X]: M[X] =
      AnalysisMonad((context) => Set[(Context, X)]())
  }

  implicit def fromStoreCache(store: StoreCache): Map[Addr, PostValue] =
    store.map

  implicit def toStoreCache(store: Map[Addr, PostValue]): StoreCache =
    StoreMap(store)

  implicit def toScEvalMonad[X](analysisMonad: AnalysisMonad[X]): ScEvalM[X] =
    ScEvalM(analysisMonad)

  def withIgnoredIdentities(f: List[Identity] => Unit): ScEvalM[()] =
    withContext(context => effectful(f(context.ignoredIdn)))

  def withContext[X](f: Context => ScEvalM[X]): ScEvalM[X] =
    AnalysisMonad((context) => f(context).m.run(context))

  def addIgnored(idns: Iterable[Identity]): ScEvalM[()] = AnalysisMonad { (context) =>
    List((context.copy(ignoredIdn = context.ignoredIdn ++ idns), ())).toSet
  }

  def withEnv[B](f: Environment[Addr] => ScEvalM[B]): ScEvalM[B] =
    AnalysisMonad((context) => f(context.env).m.run(context))

  def modifyEnv(f: BasicEnvironment[Address] => BasicEnvironment[Address]): ScEvalM[Unit] =
    AnalysisMonad[()]((context) => List((context.copy(env = f(context.env)), ())).toSet)

  def nondet[X](t: ScEvalM[X], f: ScEvalM[X]): ScEvalM[X] = AnalysisMonad { (context) =>
    val resF = f.m.run(context)
    val resT = t.m.run(context)
    resF ++ resT
  }

  def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = AnalysisMonad { (context) =>
    s.flatMap(_.m.run(context))
  }

  def withPc[X](f: PC => X): ScEvalM[X] = AnalysisMonad { (context: Context) =>
    Set((context, f(context.pc)))
  }

  def withStoreCache[X](f: StoreCache => ScEvalM[X]): ScEvalM[X] = AnalysisMonad { (context) =>
    f(context.cache).m.run(context)
  }

  /**
   * Returns a computation that applies the given function on the current store cache
   * and expects a tuple of a value and a new store cache
   */
  def withStoreCacheExplicit[X](f: StoreCache => (X, StoreCache)): ScEvalM[X] = ???

  def joinInCache(addr: Addr, value: PostValue): ScEvalM[()] = AnalysisMonad { (context) =>
    Set(
      (
        (context.copy(cache = context.cache.updated(addr, (lattice.join(context.store.getOrElse(addr, lattice.bottom), value._1), value._2)))),
        ()
      )
    )
  }

  /**
   * Given a computation that yields states that contain sets of values, this operator yields a single computation
   * that gives rises to a state for every element in the given set.
   */
  def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = AnalysisMonad((context) =>
    c.m.run(context).flatMap { case (updatedContext, set) =>
      set.map((updatedContext, _))
    }
  )

  /**
   * Action that prints the current store as a table
   * to the screen. Useful for debugging.
   */
  def printStore: ScEvalM[()] = withStoreCache { store =>
    import maf.util.StoreUtil._
    println(store.map.asTable.prettyString())
    unit
  }

  def evict(addresses: List[Addr]): ScEvalM[()] = AnalysisMonad { context =>
    Set((context.copy(cache = context.cache.removedAll(addresses)), ()))
  }

  def readSafe(addr: Addr): ScEvalM[PostValue] = withStoreCache { store =>
    pure(store.get(addr).getOrElse((lattice.bottom, ScNil())))
  }

  /**
   * Writes the given value to the given address
   *
   * @param addr  the address to write the value to
   * @param value the value to write to the given address
   * @return a computation that writes the given value to the address
   */
  override def write(addr: Addr, value: PostValue): ScEvalM[Unit] = ???

  /** Forcefully write to the store */
  override def writeForce(addr: Addr, value: PostValue): ScEvalM[Unit] = ???

  override def evaluatedValue(value: PostValue): ScEvalM[PostValue] = pure(value)

  def compute(c: ScEvalM[PostValue])(context: Context): (Value, Store, List[ScExp]) = {
    // TODO: this looks a lot like mergedPC, see if we can abstract this away a bit

    import maf.lattice.MapLattice._
    val result = c.m.run(context)

    // optimisation: if the number of output states is one, then we don't need to merge anything
    if (result.size == 1) {
      val (context, (v, s)) = result.head
      (v, context.store, List(s))
    } else {
      result.foldLeft[(Value, Store, List[ScExp])]((lattice.bottom, Lattice[Store].bottom, List()))((acc, v) =>
        v match {
          case (context, (l, s)) =>
            (lattice.join(acc._1, l), Lattice[Store].join(acc._2, context.store), s :: acc._3)
        }
      )
    }
  }

  /** Run the given computation without any initial context */
  override def run(c: ScEvalM[PostValue]): PostValue = {
    val (v, _, _) = compute(c)(Context(env = BasicEnvironment(Map()), pc = ScNil(), cache = StoreMap(Map())))
    (v, ScNil())
  }
}
object ScModSemanticsScheme {
  var r = 0
  def genSym: String = {
    r += 1
    s"x$r"
  }

  def freshIdent: ScExp =
    ScIdentifier(genSym, Identity.none)
}

trait ScModSemanticsScheme
    extends ModAnalysis[ScExp]
       with ScSchemeDomain[Address]
       with GlobalStore[ScExp]
       with ReturnValue[ScExp]
       with DestructiveStore[ScExp]
       with LocalStore[ScExp] {

  type ComponentContext
  type AllocationContext
  type VarAllocationContext
  def allocVar(id: ScIdentifier, cmp: ComponentContext): ScVarAddr[VarAllocationContext]
  def allocGeneric(idn: Identity, cmp: Component): ScGenericAddr[AllocationContext]

  /** Returns the context of a component */
  def context(component: Component): ComponentContext

  /** Allocates a new context */
  def allocCtx(
      clo: ScLattice.Clo[Addr],
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext

  /** Creates a new component based on the given concrete component */
  def newComponent(component: Call[ComponentContext]): Component

  def viewStore(component: Component): Store = view(component) match {
    case c: CallWithStore[ComponentContext, Addr, Value] => c.store.v
    case ScMain | Call(_, _, _) =>
      if (GLOBAL_STORE_ENABLED) Map()
      else
        store.view.filterKeys {
          case _: ReturnAddr[_] | _: ExceptionAddr[_] => false
          case _                                      => true
        }.toMap
  }

  def instrument(component: Component, data: LocalStoreMap[Addr, Value]): Component =
    view(component) match {
      // we can only pass the store to calls of other functions
      case c: Call[ComponentContext] => newComponent(CallWithStore(c, data))

      case _ => component
    }

  def deinstrument(component: Component): Component = component match {
    case c: CallWithStore[ComponentContext, Addr, Value] => newComponent(c.call)
    case _                                               => component
  }

  /** The environment in which the analysis is executed */
  type Env = Environment[Address]

  /** The type of a call component creator */
  type CreateCallComponent = (Env, ScLambda, ComponentContext) => Call[ComponentContext]

  /** A base environment which can be defined by implementations of this trait */
  def baseEnv: Env

  /** The components of this analysis are functions */
  type Component <: Serializable

  /** For convience we define the `main` function as the initial component that must be analysed */
  def initialComponent: Component

  /**
   * Retrieves the expression from the given component
   * @param cmp the component to extract the expression from
   * @return an expression from the soft contract language
   */
  def expr(cmp: Component): ScExp

  /**
   * Set to true if the analysis must use a global store, for all its variables.
   * Set to false if the global store should only be used for return values and for parameter passing
   * to top-level functions.
   */
  val GLOBAL_STORE_ENABLED: Boolean

  def view(component: Component): ScComponent

  implicit def toScIdentifier(p: ScParam): ScIdentifier =
    ScIdentifier(p.name, p.idn)

  /** An adapter for the "old" store interface, that actually does nothing */
  case object NoStoreAdapter extends maf.core.Store[Addr, Value] {
    def lookup(addr: Addr): Option[Value] = None
    def extend(addr: Addr, value: Value): maf.core.Store[Addr, Value] = NoStoreAdapter
  }

  trait IntraScAnalysisScheme
      extends IntraAnalysis
         with GlobalStoreIntra
         with ReturnResultIntra
         with DestructiveStoreIntra
         with LocalStoreIntra
         with SchemeInterpreterBridge[Value, Addr] { intra =>

    def pointer(exp: SchemeExp): Addr =
      ScGenericAddr(exp.idn, context(component))

    def callcc(
        clo: (SchemeLambdaExp, Environment[Address]),
        pos: Position
      ): Value =
      throw new Exception("call/cc is not supported by the contract language")

    def currentThread: TID =
      throw new Exception("Threading is not supported by the contract language")

    implicit class CallNoStorePrimitive(prim: SchemePrimitive[Value, Addr]) {
      def callNoStore(args: List[Value]): Value =
        prim
          .call(ScNil(), args.zip(Stream.continually(List(ScNil()).toStream).flatten).map { case (a, b) => (b, a) }, NoStoreAdapter, intra)
          .map(_._1)
          .getOrElse(lattice.bottom)

      def callNoStore(arg: Value): Value =
        callNoStore(List(arg))
    }

    /** Remove a blame of a certain component from the store */
    def removeBlame(component: Component, idn: Identity): Unit =
      intra.store = intra.store
        .map {
          case (ex @ ExceptionAddr(`component`, _), value) =>
            (
              ex,
              lattice
                .getBlames(value)
                .filter(_.blamedPosition != idn)
                .map(lattice.blame(_))
                .foldLeft(lattice.bottom)((a, b) => lattice.join(a, b))
            )
          case v => v
        }
        .filter {
          case (ExceptionAddr(_, _), v) => lattice.getBlames(v).nonEmpty
          case _                        => true
        }

    def writeBlame(blame: Blame) =
      writeAddr(ExceptionAddr(component, expr(component).idn), lattice.blame(blame))

    /**
     * Compute the body of the component under analysis
     * @return the body of the component under analysis
     */
    def fnBody: ScExp = view(component) match {
      case ScMain             => program
      case Call(_, lambda, _) => lambda.body
    }

    /**
     * Returns an address for the given parameter,
     * this is always based on the allocator of the
     * current component
     */
    def fnParam(v: ScParam): Addr =
      allocVar(v, context(component))

    /**
     * Returns the list of all the addresses
     * of the function under analysis
     */
    def fnParams: List[Addr] = view(component) match {
      case ScMain => List()
      case Call(_, lambda, _) =>
        lambda.variables.map(fnParam)
    }

    /**
     * Compute the environment of the component under analysis
     * @return the body of the component under analysis
     */
    def fnEnv: Env = view(component) match {
      case ScMain => baseEnv
      case Call(env, lambda, _) =>
        env.extend(lambda.variables.map(v => (v.name, allocVar(v, context(component)))))
    }

    /** Computes the list of free variables of this component */
    def fv: Set[String] = expr(component).fv
  }

  override def intraAnalysis(component: Component): IntraScAnalysisScheme

  def summary: ScAnalysisSummary[Value] = {
    var returnValues = Map[Any, Value]()
    var blames = Map[Any, Set[Blame]]()

    store.foreach {
      case (ReturnAddr(cmp, _), value)    => returnValues = returnValues.updated(cmp, value)
      case (ExceptionAddr(cmp, _), value) => blames = blames.updated(cmp, lattice.getBlames(value))
      case _                              => ()
    }

    ScAnalysisSummary(returnValues, blames)
  }

  def getReturnValue(component: Component): Option[Value] =
    summary.getReturnValue(component)

  sealed trait SingleVerificationResult
  object SingleVerificationResult {
    def join(
        a: SingleVerificationResult,
        b: => SingleVerificationResult
      ): SingleVerificationResult = (a, b) match {
      case (a, b) if a == b => a
      case (Top, _)         => Top
      case (_, Top)         => Top
      case (Bottom, _)      => b
      case (_, Bottom)      => a
      case (_, _)           => Top
    }
  }

  implicit def singleVerificationResultLattice = new Lattice[SingleVerificationResult] {
    type L = SingleVerificationResult

    /** A lattice has a bottom element */
    def bottom: L = Bottom

    /** A lattice has a top element (might be undefined) */
    def top: L = Top

    /** Elements of the lattice can be joined together */
    def join(x: L, y: => L): L = SingleVerificationResult.join(x, y)

    /** Subsumption between two elements can be checked */
    def subsumes(x: L, y: => L): Boolean = ???

    /** Equality check, returning an abstract result */
    def eql[B: BoolLattice](x: L, y: L): B = ???

    def show(v: SingleVerificationResult): String = v match {
      case Top           => "top"
      case Bottom        => "bottom"
      case VerifiedFalse => "#f"
      case VerifiedTrue  => "#t"
    }
  }

  case object Bottom extends SingleVerificationResult
  case object VerifiedFalse extends SingleVerificationResult
  case object VerifiedTrue extends SingleVerificationResult
  case object Top extends SingleVerificationResult

  type VerifyIdentity = (Identity, Identity)
  var verificationResults: Map[Identity, Map[VerifyIdentity, SingleVerificationResult]] =
    Map().withDefaultValue(Map().withDefaultValue(Bottom))

  def addSingleVerificationResult(
      monIdn: Identity,
      contractIdn: VerifyIdentity,
      value: SingleVerificationResult
    ): Unit = {
    val monEntry = verificationResults(monIdn)
    val contractEntry = monEntry(contractIdn)
    verificationResults += (monIdn -> (monEntry + (contractIdn ->
      SingleVerificationResult
        .join(contractEntry, value))))
  }

  def addVerified(monIdn: Identity, contractIdn: VerifyIdentity): Unit =
    addSingleVerificationResult(monIdn, contractIdn, VerifiedTrue)

  def addUnverified(monIdn: Identity, contractIdn: VerifyIdentity): Unit =
    addSingleVerificationResult(monIdn, contractIdn, VerifiedFalse)

  def getVerificationResults(
      result: SingleVerificationResult,
      context: Option[Identity] = None
    ): List[VerifyIdentity] = {
    val results = if (context.isEmpty) {
      verificationResults.values.flatten
    } else {
      verificationResults(context.get)
    }

    results
      .filter {
        case (_, `result`) => true
        case _             => false
      }
      .map { case (idn, _) =>
        idn
      }
      .toList
  }

  type SMTSolver <: ScSmtSolver
  def newSmtSolver(program: ScExp): SMTSolver
}
