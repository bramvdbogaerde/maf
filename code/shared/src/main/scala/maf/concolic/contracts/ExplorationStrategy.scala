package maf.concolic.contracts

import maf.language.contracts.ScExp

trait IsWalker {

  /** Finds the next possible path condition if any */
  def next(): Option[(ScExp, List[Boolean])]
}

trait ExplorationStrategy {
  type Walker <: IsWalker

  /**
   * Start returns a walker that uses the given tree and tree
   * to generate the next path condition
   *
   * @param tree
   * @param trail
   * @return
   */
  def start(tree: ConcTree, trail: List[Boolean]): Walker
}

class NearestWalker(tree: ConcTree, private var trail: List[Boolean]) extends IsWalker {
  def next(): Option[(ScExp, List[Boolean])] = {
    def aux(currentTrail: List[Boolean]): Option[(ScExp, List[Boolean])] = {
      if (currentTrail.isEmpty) {
        trail = currentTrail
        None
      } else {
        val choice = (!currentTrail.head :: currentTrail.tail).reverse
        val node = tree.followTrail(choice)
        val rest = currentTrail.tail
        node match {
          case UnexploredNode(pc) =>
            trail = rest
            Some((pc, choice))
          case _ =>
            aux(rest)
        }
      }
    }

    aux(trail)
  }
}

/**
 * Ends up doing something similar as a DFS, but tries to exlore the
 * next state that is closest to the previously visited state.
 */
object Nearest extends ExplorationStrategy {
  type Walker = NearestWalker

  override def start(tree: ConcTree, trail: List[Boolean]): Walker = {
    new NearestWalker(tree, trail)
  }
}
