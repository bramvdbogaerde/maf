package maf.concolic.contracts

import maf.language.contracts.ScExp
import maf.language.contracts.ScNil
import maf.language.scheme.interpreter.ConcreteValues
import java.io.PrintWriter

trait RenderToDot {
  def toDot(writer: PrintWriter): Unit
}

sealed trait ConcTree extends RenderToDot {
  val pc: ScExp
  def modifyPc(pc: ScExp): ConcTree
  def replaceAt(trail: List[Boolean], t: ConcTree): ConcTree
  def followTrail(trail: List[Boolean]): ConcTree
  def isLeaf: Boolean
  def name: String = hashCode().toString().replace("-", "m")
}

sealed trait LeafNode extends ConcTree with RenderToDot {
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
  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Error: ${error}\n ${pc}\"];""")
  }
}
case class TreeNode(
    left: ConcTree,
    right: ConcTree,
    pc: ScExp)
    extends ConcTree
       with RenderToDot {

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

  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Branch ${pc}"];\n""")
    writer.write(s"node_${name} -> node_${left.name};\n")
    writer.write(s"node_${name} -> node_${right.name};\n")
    left.toDot(writer)
    right.toDot(writer)
  }
}

case object NilNode extends LeafNode {
  val pc: ScExp = ScNil()

  def modifyPc(pc: ScExp): ConcTree = NilNode

  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Nil ${pc}"];""")
  }
}

case class UnsatNode(pc: ScExp) extends LeafNode with FinalNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Unsat ${pc}"];""")
  }
}

case class ValueNode(value: ConcreteValues.Value, pc: ScExp) extends LeafNode with FinalNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Value ${value}\n ${pc}"];""")
  }
}

case class UnexploredNode(pc: ScExp) extends LeafNode {
  def modifyPc(pc: ScExp): ConcTree = this.copy(pc = pc)
  def toDot(writer: PrintWriter): Unit = {
    writer.write(s"""node_${name} [shape=box, label="Unexplored ${pc}"];""")
  }
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

  def toDot(tree: ConcTree, writer: PrintWriter): Unit = {
    writer.write("digraph G {\n")
    //writer.write("rankdir = \"LR\"\n")
    tree.toDot(writer)
    writer.write("}")
  }
}
