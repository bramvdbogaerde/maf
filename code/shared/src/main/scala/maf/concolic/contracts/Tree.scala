package maf.concolic.contracts

import maf.language.contracts.ScExp
import maf.language.contracts.ScNil
import maf.language.scheme.interpreter.ConcreteValues

sealed trait ConcTree {
  val pc: ScExp
  def modifyPc(pc: ScExp): ConcTree
  def replaceAt(trail: List[Boolean], t: ConcTree): ConcTree
  def followTrail(trail: List[Boolean]): ConcTree
  def isLeaf: Boolean
}

sealed trait LeafNode extends ConcTree {
  def isLeaf: Boolean = true
  def replaceAt(trail: List[Boolean], t: ConcTree): ConcTree =
    if (trail.size > 0) { throw new Exception("at leaf node but trail is not empty") }
    else { t }

  def followTrail(trail: List[Boolean]): ConcTree =
    if (trail.size > 0) { throw new Exception("at leaf node but trail is not empty") }
    else { this }
}

sealed trait FinalNode extends LeafNode {
  abstract override def replaceAt(trail: List[Boolean], t: ConcTree): ConcTree = {
    super.replaceAt(trail, t)
    if (ConcTree.debug) { println("warn: final node not replacing data") }
    this
  }
}
case class ErrorNode(error: String, pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)

}
case class TreeNode(
    left: ConcTree,
    right: ConcTree,
    pc: ScExp)
    extends ConcTree {

  def isLeaf: Boolean = false
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
  def replaceAt(trail: List[Boolean], t: ConcTree): ConcTree =
    if (trail.isEmpty) {
      if (ConcTree.debug) { println("warn: ignoring request, as we will not replace entire subtree") }
      this
    } else if (trail.head) {
      this.copy(left = left.replaceAt(trail.tail, t))
    } else {
      this.copy(right = right.replaceAt(trail.tail, t))
    }

  def followTrail(trail: List[Boolean]): ConcTree =
    if (trail.isEmpty) {
      if (ConcTree.debug) {
        println("warn: not a leaf node but trail is empty")
      }
      this
    } else if (trail.head) {
      left.followTrail(trail.tail)
    } else {
      right.followTrail(trail.tail)
    }
}

case object NilNode extends LeafNode {
  val pc: ScExp = ScNil()

  def modifyPc(pc: ScExp): ConcTree = NilNode

}

case class UnsatNode(pc: ScExp) extends LeafNode with FinalNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

case class ValueNode(value: ConcreteValues.Value, pc: ScExp) extends LeafNode with FinalNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

case class UnexploredNode(pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

object ConcTree {
  def debug: Boolean = false
  def noSetter(c: ConcTree): Unit = ()
  def empty: ConcTree = UnexploredNode(pc = ScNil())
  def unsat(pc: ScExp): ConcTree = UnsatNode(pc)
  def value(v: ConcreteValues.Value, pc: ScExp = ScNil()): ConcTree = ValueNode(v, pc)

  def stackoverflow(pc: ScExp): ConcTree = ErrorNode(
    error = "Stack overflow",
    pc
  )
}