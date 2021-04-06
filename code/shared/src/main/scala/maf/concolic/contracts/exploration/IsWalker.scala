package maf.concolic.contracts.exploration

import maf.language.contracts.ScExp

trait IsWalker {

  /** Finds the next possible path condition if any */
  def next(): Option[(ScExp, List[Boolean])]
}
