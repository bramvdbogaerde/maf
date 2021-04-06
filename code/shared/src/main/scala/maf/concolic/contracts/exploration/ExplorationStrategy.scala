package maf.concolic.contracts.exploration

import maf.concolic.contracts.{ConcTree, UnexploredNode}
import maf.language.contracts.ScExp

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
