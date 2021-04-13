package maf.concolicbridge

import maf.modular.contracts.semantics.ScModSemanticsScheme
import maf.util.benchmarks.Timeout
import maf.concolicbridge.assumptions.Tracker

trait ScModSemanticsCollaborativeTesting extends ScModSemanticsScheme {
  protected var enabledAssumptions: Map[String, Boolean] = Map(
    "pure" -> true,
    "value" -> true,
    "inline" -> true,
    "nondetif" -> true
  )

  def disableAssumption(name: String): Unit = {
    enabledAssumptions = enabledAssumptions.updated(name, false)
  }

  override def intraAnalysis(component: Component): ScIntraAnalysisInstrumented
  var instrumenter: Instrumenter = Instrumenter(Map())

  protected var violatedAssumptions: Set[String] = Set()
  private var verifiedAssumptions: Set[String] = Set()
  private var assumptions: Set[String] = Set()
  private var retry: Set[String] = Set()
  protected var _tracker: Tracker = Tracker()

  def withInstrumenter(f: Instrumenter => Instrumenter): Unit = {
    instrumenter = f(instrumenter)
  }

  /** Register the given assumption as being violated */
  def registerViolated(name: String): Unit = {
    violatedAssumptions += name
  }

  /** Registers the given assumption as being verified */
  def registerVerified(name: String): Unit = {
    verifiedAssumptions += name
  }

  /** Registers an assumption with the given name */
  def assume(name: String): Unit = {
    // TODO: check whether the assumption already exists and consider throwing an error
    assumptions += name
  }

  /** Set the tracker */
  def tracker_=(tracker: Tracker): Unit =
    this._tracker = tracker

  /** Retrieve the current tracker */
  def tracker: Tracker = this._tracker

  /** Get a copy of the current tracker */
  def copyTracker: Tracker = tracker.copy

  /** Retries an assumption with the given name */
  def retry(name: String): Unit = {
    retry += name
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

  protected def commit(): Unit = {
    violatedAssumptions = violated -- retry
    assumptions = assumptions ++ retry
    retry = Set()
  }

  abstract override def analyzeWithTimeout(timeout: Timeout.T): Unit = {
    super.analyzeWithTimeout(timeout)
    commit()
  }

  trait ScIntraAnalysisInstrumented extends IntraScAnalysisScheme
}
