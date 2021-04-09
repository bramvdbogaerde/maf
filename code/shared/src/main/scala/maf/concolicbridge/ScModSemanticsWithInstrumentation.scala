package maf.concolicbridge

import maf.modular.contracts.semantics.ScModSemanticsScheme

trait ScModSemanticsWithInstrumentation extends ScModSemanticsScheme {
  override def intraAnalysis(component: Component): ScIntraAnalysisInstrumented
  var instrumenter: Instrumenter = Instrumenter(Map())

  private var violatedAssumptions: Set[String] = Set()
  private var verifiedAssumptions: Set[String] = Set()
  private var assumptions: Set[String] = Set()

  def withInstrumenter(f: Instrumenter => Instrumenter): Unit = {
    instrumenter = f(instrumenter)
  }

  /** Register the given assumption as being violated */
  def violated(name: String): Unit = {
    violatedAssumptions += name
  }

  /** Registers the given assumption as being verified */
  def verified(name: String): Unit = {
    verifiedAssumptions += name
  }

  /** Registers an assumption with the given name */
  def assume(name: String): Unit = {
    // TODO: check whether the assumption already exists and consider throwing an error
    assumptions += name
  }

  /** Returns true if the given assumption is violated */
  def isViolated(name: String): Boolean =
    violatedAssumptions.contains(name)

  /** Returns true if the given assumption is verified */
  def isVerified(name: String): Boolean =
    verifiedAssumptions.contains(name)

  /** Returns the set of verified assumptions */
  def verified: Set[String] = verifiedAssumptions

  /** Returns the set of violated assumptions */
  def violated: Set[String] = violatedAssumptions

  /** Returns the set of made assumptions */
  def assumed: Set[String] = assumptions

  trait ScIntraAnalysisInstrumented extends IntraScAnalysisScheme
}
