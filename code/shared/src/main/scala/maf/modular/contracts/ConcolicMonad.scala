package maf.modular.contracts

import maf.modular.contracts.semantics._
import maf.core.{Address, Environment}
import maf.language.contracts.ScExp
import maf.core.Store

trait ConcreteValue // TODO: move to other file

/** A tree structure to keep track of the space we need to explore. */
trait ConcTree {
  val pc: ScExp
  def unsat(branch: Boolean): Unit
  def take(branch: Boolean, pc: ScExp): ConcTree
}

case class TreeNode(
    var left: ConcTree,
    var right: ConcTree,
    pc: ScExp)
    extends ConcTree {

  /** Marks either the left or right branch as unsatisfiable */
  def unsat(branch: Boolean): Unit = if (branch) left = UnsatNode(left.pc) else right = UnsatNode(right.pc)

  def take(branch: Boolean, pc: ScExp): ConcTree =
    if (branch) {
      if (left != NilNode) left else { left = TreeNode(NilNode, NilNode, pc); left }
    } else {
      if (right != NilNode) right else { right = TreeNode(NilNode, NilNode, pc); right }
    }
}

/** A temporary placeholder node, only used during the concolic execution */
case object NilNode extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Cannot mark nil node as unsatisfiable")
  def take(branch: Boolean, pc: ScExp): ConcTree = throw new Exception(s"Cannot take branch on ${this.getClass}")
}

/** A node that was discovered during execution but whose subtree is not yet explored by the analysis */
case class UnexploredNode(pc: ScExp) extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Cannot mark an unexplored node as unsatisfiable")
  def take(branch: Boolean, pc: ScExp): ConcTree = throw new Exception(s"Cannot take branch on ${this.getClass}")
}

/** A node that was proven to be unreachable at runtime (using the constraints discovered during the analysis) */
case class UnsatNode(pc: ScExp) extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Node already marked unsatisfiable")
  def take(branch: Boolean, pc: ScExp): ConcTree = throw new Exception(s"Cannot take branch on ${this.getClass}")
}

/** The execution resulted in an error in this node */
case class ErrorNode(error: String, pc: ScExp) extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Cannot mark an error node as unsatisfiable")
  def take(branch: Boolean, pc: ScExp): ConcTree = throw new Exception(s"Cannot take branch on ${this.getClass}")
}

/** The execution resulted in a value in this node */
case class ValueNode(value: ConcreteValue, pc: ScExp) extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Cannot mark an branch node as unsatisfiable")
}

case class ConcolicContext(
    env: Environment[Address],
    store: Map[Address, ConcreteValue],
    pc: ScExp,
    root: ConcTree)

case class ConcolicMonad[X](run: ConcolicContext => (ConcolicContext, Option[X]))
object ConcolicMonadInstance extends ScAbstractSemanticsMonad[ConcolicMonad] {

  /** Injects a value in the Monad */
  override def pure[X](v: => X): ConcolicMonad[X] = {
    ConcolicMonad(context => (context, Some(v)))
  }

  /**
   * The semantics of this monad are that it behaves as a state monad, retrieving a state and returning
   * an updated state together with a value, except that when running the composition operator and the
   * first computation returns None as a value, then the second computation is not run, and the result
   * is the updated state with None as a result
   */
  override def flatMap[X, Y](m: ConcolicMonad[X], f: X => ConcolicMonad[Y]): ConcolicMonad[Y] = ConcolicMonad { context =>
    val (newContext, valueOpt) = m.run(context)
    valueOpt match {
      case Some(v) => f(v).run(newContext)
      case None    => (newContext, None)
    }
  }

  /** A computation composed with void will not be run */
  override def void[X]: ConcolicMonad[X] = ConcolicMonad { context => (context, None) }
}

trait ConcolicMonadAnalysis extends ScAbstractSemanticsMonadAnalysis {
  case class PS(pure: Val, symbolic: ScExp) extends IsPostValue
  //case class ConcolicStore(map: Map[Addr, PostValue]) extends Store[Addr, PostValue]

  override type M[X] = ConcolicMonad[X]
  override type PostValue = PS
  //override type StoreCache = ConcolicStore
}
