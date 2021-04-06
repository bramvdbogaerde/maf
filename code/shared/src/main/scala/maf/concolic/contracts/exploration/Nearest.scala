package maf.concolic.contracts.exploration

import maf.concolic.contracts.{ConcTree, UnexploredNode}
import maf.language.contracts.ScExp

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
