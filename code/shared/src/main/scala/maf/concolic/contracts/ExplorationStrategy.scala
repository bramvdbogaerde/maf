package maf.concolic.contracts

import maf.language.contracts.ScExp

trait ExplorationStrategy {

  /**
   * Generates the next path condition that needs to be solved,
   * if any.
   */
  def next(tree: ConcTree, trail: List[Boolean]): Option[ScExp]
}

/**
 * Ends up doing something similar as a DFS, but tries to exlore the
 * next state that is closest to the previously visited state.
 */
object Nearest extends ExplorationStrategy {
  override def next(tree: ConcTree, trail: List[Boolean]): Option[ScExp] = {
    def aux(trail: List[Boolean]): Option[ScExp] = {
      if (trail.isEmpty) {
        None
      } else {
        val node = tree.followTrail((!trail.head :: trail.tail).reverse)
        val rest = trail.tail
        node match {
          case UnexploredNode(pc) =>
            // we found a node that we need to explore
            Some(pc)
          case _ =>
            // no node found lets try the rest
            aux(rest)
        }
      }
    }

    // we will start from the leaf node in the trail and work our way up to the root
    aux(trail.reverse)
  }
}
