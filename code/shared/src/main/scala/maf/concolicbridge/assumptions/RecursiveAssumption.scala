package maf.concolicbridge.assumptions

import maf.modular.contracts.semantics.ScBigStepSemanticsScheme
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.language.contracts.ScExp
import maf.modular.DependencyTracking
import maf.core.Environment
import maf.language.contracts.ScLambda
import maf.modular.contracts.Call
import maf.core.Identity
import maf.language.contracts.ScAssumed
import maf.language.contracts.ScFunctionAp
import maf.modular.contracts.semantics.ScModSemantics
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScLattice.Clo

/**
 * This trait encodes an assumption about recursive functions. For example:
 *
 * <code>
 * (define (fac x)
 *   (if (= x 0) 1 (* x (fac (- x 1)))))
 * (mon positive? (fac 5))
 * </code>
 *
 * The above is not verifiable by the analysis, because at some point the analysis
 * will join the numbers of the arguments to fac together, so that both branches of the
 * if condition can be true, which means that both 1 and the result of (* x (fac (- x 1))) will  * be possible, which results in an overapproximation resulting in the value NumTop. Unfortunately, NumTop does not provide any information about the sign, which means that the analysis must conclude that the contract of `positive?` can be violated at runtime.
 *
 * This use case makes use of two assumptions:
 * - inlined: to indicate that the function must be called from the same component
 * - value: to indicate within the inlined recursive function what the value needs to be that
 *   gets returned
 */
trait RecursiveAssumption extends ScBigStepSemanticsScheme with ScModSemanticsCollaborativeTesting with DependencyTracking[ScExp] {
  override def intraAnalysis(component: Component): RecursiveAssumptionIntra

  /** Returns the set of closures that are called from the current component */
  protected def calls(component: Component): Set[(Environment[Addr], ScLambda)] = {
    dependencies(component).flatMap {
      case Call(env, lambda, _) => Set((env, lambda))
      case _                    => Set()
    }
  }

  protected def isRecursive(component: Component): Boolean = {
    val callSet = calls(component)
    // a component is recursive when its callset contains
    // itself
    component match {
      case Call(env, lambda, _) =>
        callSet.contains((env, lambda))
      case _ => false
    }
  }

  trait RecursiveAssumptionIntra extends ScIntraAnalysisInstrumented with IntraScBigStepSemantics with DependencyTrackingIntra {
    case class InliningCandidate(operator: Clo[Addr], syntactic: ScExp)
    protected var inlineCandidates: Map[Identity, InliningCandidate] = Map()

    override def monFlatHook(
        value: PostValue,
        conditional: ScEvalM[PostValue],
        blamedIdentity: Identity,
        blamingIdentity: Identity
      ): ScEvalM[PostValue] = withPc { pc =>
      val t = feasible(primTrue, value)(pc)
      val f = feasible(primFalse, value)(pc)
      if (t.isRight && f.isRight && inlineCandidates.contains(blamedIdentity)) {
        // if it the result of the flat contract is imprecise and if we are calling
        // a recursive function we can try to make it more precise by inlining the function
        val recursiveCall = inlineCandidates(blamedIdentity)
        // keep track of which lambda was being selected, so that in the next run we can
        // select a different lambda if necessary
        val lambdaBeingCalled = recursiveCall.operator.lambda
        val inlinedLambda = lambdaBeingCalled // TODO
        withInstrumenter { instrumenter =>
          val name = ScModSemantics.genSym
          instrumenter.replaceAt(
            blamedIdentity,
            (generator, exp) => {
              val nameIdn = () => ScIdentifier(name, generator.nextIdentity)
              ScAssumed(
                nameIdn(),
                ScIdentifier("inline", generator.nextIdentity),
                recursiveCall.syntactic,
                List(inlinedLambda),
                generator.nextIdentity
              )
            }
          );
        }
      }
    } >> conditional

    /**
     *  Overriding this function has two purposes:
     *  (1) determine heuristically whether we can apply this function (i.e., we are calling a recursive function but we are not ourselves a recursive function)
     *  (2) Call the inlined recursive function (this is indicated with the inlined assumption) without creating a new component
     */
    override def applyFnHook(
        operator: PostValue,
        operands: List[PostValue],
        syntacticOperator: ScExp,
        syntacticOperands: List[ScExp]
      ): Set[ScEvalM[PostValue]] = {
      // first detect whether we are calling a recursive function, but are not
      // recursive ourselves
      val isSelfRecursive = isRecursive(component)

      lattice.getClosure(operator.pure).foreach { clo =>
        val calledComponent = createCalledComponent(clo, operands)
        if (!isSelfRecursive && isRecursive(calledComponent)) {
          inlineCandidates += (syntacticOperator.idn -> InliningCandidate(clo, syntacticOperator))
        }
      }

      // TODO: call the inlined function without creating a new component
      Set()
    }
  }
}
