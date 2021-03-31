package maf.concolic.contracts

import maf.language.contracts.ScExp
import maf.language.scheme.interpreter.ConcreteValues

trait ExplorationStrategy {
  case class ExplorationTarget(model: Map[String, ConcreteValues.Value], modifiedTree: ConcTree)

  /**
   * Generates the next path condition that needs to be solved,
   * if any.
   */
  def next(
      tree: ConcTree,
      trail: List[Boolean],
      isSat: ScExp => Option[Map[String, ConcreteValues.Value]]
    ): Option[ExplorationTarget]
}

/**
 * Ends up doing something similar as a DFS, but tries to exlore the
 * next state that is closest to the previously visited state.
 */
object Nearest extends ExplorationStrategy {
  override def next(
      tree: ConcTree,
      trail: List[Boolean],
      isSat: ScExp => Option[Map[String, ConcreteValues.Value]]
    ): Option[ExplorationTarget] = {
    def aux(trail: List[Boolean], tree: ConcTree): Option[ExplorationTarget] = {
      if (trail.isEmpty) {
        None
      } else {
        val choice = (!trail.head :: trail.tail).reverse
        val node = tree.followTrail(choice)
        val rest = trail.tail
        node match {
          case UnexploredNode(pc) =>
            val model = isSat(pc)
            if (model.isDefined) {
              Some(ExplorationTarget(model.get, tree))
            } else {
              aux(rest, tree.replaceAt(choice, ConcTree.unsat(pc)))
            }
          case _ =>
            // no node found lets try the rest
            aux(rest, tree)
        }
      }
    }

    // we will start from the leaf node in the trail and work our way up to the root
    aux(trail.reverse, tree)
  }
}
