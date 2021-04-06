package maf.modular.contracts

import maf.core.{Address, BasicEnvironment, Environment, Identity}
import maf.language.contracts.{ScExp, ScLambda}
import maf.modular.LocalStoreMap
import maf.modular.contracts.semantics._

sealed trait ScComponent extends Serializable

/** The main entry point of the program */
case object ScMain extends ScComponent

trait Call[Context] extends ScComponent {
  val env: BasicEnvironment[Address]
  val lambda: ScLambda
  val context: Context

  override def toString: String = lambda.toString
}

object Call {
  def apply[Context](
      env: BasicEnvironment[Address],
      lambda: ScLambda,
      context: Context
    ): Call[Context] =
    RegularCall(env, lambda, context)

  def unapply[Context](any: Any): Option[(BasicEnvironment[Address], ScLambda, Context)] = any match {
    case c: Call[Context] => Some((c.env, c.lambda, c.context))
    case _                => None
  }
}

/**
 * A call to another function
 * @param env the lexical environment of the lambda
 * @param lambda the body of the lambda
 * @tparam Context the context of the call
 */
case class RegularCall[Context](
    env: BasicEnvironment[Address],
    lambda: ScLambda,
    context: Context)
    extends Call[Context]

/**
 * A call to a function that is guarded by a contract.
 *
 * This is used in the big step semantics to refine the path
 * condition of the component and to check the result of the
 * function for each final state
 */
case class GuardedFunctionCall[Context](
    domainContracts: List[Address],
    rangeContract: Address,
    rangeIdentity: Identity,
    env: BasicEnvironment[Address],
    lambda: ScLambda,
    context: Context)
    extends Call[Context]

case class ContractCall[Context](
    monIdentity: Identity,
    blamedParty: Identity,
    env: BasicEnvironment[Address],
    lambda: ScLambda,
    context: Context)
    extends Call[Context]

case class CallWithStore[Context, Addr, Value](
    call: Call[Context],
    store: LocalStoreMap[Addr, Value])
    extends Call[Context] {
  override val env: BasicEnvironment[Address] = call.env
  override val lambda: ScLambda = call.lambda
  override val context: Context = call.context

  override def toString: String = s"with_store${call.lambda}"
}

trait ScStandardComponents extends ScModSemanticsScheme {
  type Component = ScComponent

  def expr(component: Component): ScExp = view(component) match {
    case ScMain             => program
    case Call(_, lambda, _) => lambda
  }

  def view(component: Component): ScComponent = component

  def newComponent(component: Call[ComponentContext]): Component =
    component

  def initialComponent: ScComponent = ScMain
}
