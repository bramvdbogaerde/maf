package maf.concolicbridge.assumptions

import maf.core.Identity

/**
 * A tracker keeps track of which assumptions have been made
 * on which identities.
 *
 * This can be used to prevent that the same assumption
 * is made a second time, in which case the analysis might
 * never complete.
 *
 * Example:
 * <code>
 *  val tracker = Tracker()
 *  tracker.add("pure", idn)
 *  assert(tracker.contains("pure", idn))
 * </code>
 */
class Tracker(private var assumptions: Map[String, List[Identity]] = Map()) {

  /**
   * Add a new assumption to be tracked
   *
   * @param assumption the assumption to track (e.g, pure, value, ...)
   * @param identity the identity of the value for which we generated the assumption
   */
  def add(assumption: String, identity: Identity): Unit =
    assumptions = assumptions.updatedWith(assumption) { values =>
      values.orElse(Some(List())).map(identity :: _)
    }

  /** Checks whether we track an assumption for the given identity */
  def contains(assumption: String, identity: Identity): Boolean =
    assumptions.get(assumption).getOrElse(List()).contains(identity)

  /**
   * Create a clone of the current tracker
   *
   * @return a cloned version of the current tracker
   */
  def copy: Tracker =
    new Tracker(assumptions)
}

object Tracker {
  def apply(): Tracker = {
    new Tracker(Map())
  }
}