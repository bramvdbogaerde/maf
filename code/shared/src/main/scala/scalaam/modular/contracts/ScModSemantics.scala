package scalaam.modular.contracts

import scalaam.core.Position.Position
import scalaam.core.{Address, Environment, Identity}
import scalaam.language.contracts.ScLattice.Blame
import scalaam.language.contracts.{ScExp, ScIdentifier, ScLambda, ScLattice}
import scalaam.modular.{GlobalStore, ModAnalysis, ReturnAddr, ReturnValue}

trait ScModSemantics
    extends ModAnalysis[ScExp]
    with ScDomain
    with GlobalStore[ScExp]
    with ReturnValue[ScExp] {

  /**
    * This method can be overrided to implement a different strategy for allocating addresses for variables
    */
  type AllocationContext
  def allocVar(id: ScIdentifier, cmp: Component): ScVarAddr[AllocationContext]
  def allocGeneric(idn: Identity, cmp: Component): ScGenericAddr[AllocationContext]

  type ComponentContext
  def allocCtx(
      clo: ScLattice.Clo[Addr],
      args: List[Value],
      call: Position,
      caller: Component
  ): ComponentContext

  def newComponent(component: Call[ComponentContext]): Component

  /**
    * The environment in which the analysis is executed
    */
  type Env = Environment[Address]

  /**
    * The type of a call component creator
    */
  type CreateCallComponent = (Env, ScLambda, ComponentContext) => Call[ComponentContext]

  /**
    * A base environment which can be defined by implementations of this trait
    */
  def baseEnv: Env

  /**
    * The components of this analysis are functions
    */
  type Component

  /**
    * For convience we define the `main` function as the initial component that must be analysed
    */
  def initialComponent: Component

  /**
    * Retrieves the expression from the given component
    * @param cmp the component to extract the expression from
    * @return an expression from the soft contract language
    */
  def expr(cmp: Component): ScExp

  def view(component: Component): ScComponent

  trait IntraScAnalysis extends IntraAnalysis with GlobalStoreIntra with ReturnResultIntra {

    /**
      * Compute the body of the component under analysis
      * @return the body of the component under analysis
      */
    def fnBody: ScExp = view(component) match {
      case ScMain             => program
      case Call(_, lambda, _) => lambda.body
    }

    /**
      * Compute the environment of the component under analysis
      * @return the body of the component under analysis
      */
    def fnEnv: Env = view(component) match {
      case ScMain => baseEnv
      case Call(env, lambda, _) =>
        env.extend(lambda.variables.map(v => (v.name, allocVar(v, component))))
    }
  }

  override def intraAnalysis(component: Component): IntraScAnalysis

  def summary: ScAnalysisSummary[Value] = {
    var returnValues = Map[Any, Value]()
    var blames       = Map[Any, Set[Blame]]()

    store.foreach {
      case (ReturnAddr(cmp, _), value)    => returnValues = returnValues.updated(cmp, value)
      case (ExceptionAddr(cmp, _), value) => blames = blames.updated(cmp, lattice.getBlames(value))
      case _                              => ()
    }

    ScAnalysisSummary(returnValues, blames)
  }

  def getReturnValue(component: Component): Option[Value] = {
    summary.getReturnValue(component)
  }

  object VerificationResult {
    def join(a: VerificationResult, b: => VerificationResult): VerificationResult = (a, b) match {
      case (Unverified, _)              => Unverified
      case (_, Unverified)              => Unverified
      case (Partially(a), Partially(b)) => Partially(a ++ b)
      case (Partially(_), _)            => a
      case (_, Partially(_))            => b
      case (Verified, _)                => Verified
      case (_, Verified)                => Verified
    }
  }
  sealed trait VerificationResult
  case object Unverified                       extends VerificationResult
  case class Partially(unverified: Set[Value]) extends VerificationResult
  case object Verified                         extends VerificationResult
  var unverified: Map[Identity, VerificationResult] = Map().withDefaultValue(Verified)
  def unverify(idn: Identity): Unit                 = unverified += (idn -> Unverified)
  def verify(idn: Identity): Unit                   = unverified += (idn -> Verified)
  def partial(idn: Identity, unverifiedValues: Set[Value]): Unit =
    unverified += (idn -> VerificationResult.join(unverified(idn), Partially(unverifiedValues)))
}
