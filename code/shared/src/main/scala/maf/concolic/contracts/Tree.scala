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
    else { t.modifyPc(pc) }

  def followTrail(trail: List[Boolean]): ConcTree =
    if (trail.size > 0) { throw new Exception("at leaf node but trail is not empty") }
    else { this }
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
    if (trail.isEmpty) { throw new Exception("not a leaf node but trail is empty") }
    else if (trail.head) {
      this.copy(left = left.replaceAt(trail.tail, t))
    } else {
      this.copy(right = right.replaceAt(trail.tail, t))
    }

  def followTrail(trail: List[Boolean]): ConcTree =
    if (trail.isEmpty) { throw new Exception("not a leaf node but trail is empty") }
    else if (trail.head) {
      left.followTrail(trail.tail)
    } else {
      right.followTrail(trail.tail)
    }
}

case object NilNode extends LeafNode {
  val pc: ScExp = ScNil()

  def modifyPc(pc: ScExp): ConcTree = NilNode

}

case class UnsatNode(pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

case class ValueNode(value: ConcreteValues.Value, pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

case class UnexploredNode(pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
}

object ConcTree {
  def noSetter(c: ConcTree): Unit = ()
  def empty: ConcTree = UnexploredNode(pc = ScNil())
  def value(v: ConcreteValues.Value): ConcTree = ValueNode(v, ScNil())

  def stackoverflow(pc: ScExp): ConcTree = ErrorNode(
    error = "Stack overflow",
    pc
  )
}
