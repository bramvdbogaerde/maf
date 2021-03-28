package maf.modular.contracts

import maf.modular.contracts.semantics._
import maf.language.contracts.ScExp
import maf.core.Store
import maf.core.BasicEnvironment
import maf.language.contracts.ScNil
import maf.core.Identity
import maf.language.contracts.lattices.ScConcreteValues
import maf.language.scheme.interpreter.ConcreteValues

/** A tree structure to keep track of the space we need to explore. */
trait ConcTree {
  val pc: ScExp
  def unsat(branch: Boolean): Unit
  def take(branch: Boolean, pc: ScExp): ConcTree
}

object ConcTree {
  def root: ConcTree = TreeNode(
    left = NilNode,
    right = NilNode,
    pc = ScNil()
  )
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
  val pc: ScExp = ScNil()
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
case class ValueNode(value: ScConcreteValues.ScValue, pc: ScExp) extends ConcTree {
  def unsat(branch: Boolean): Unit = throw new Exception("Cannot mark an branch node as unsatisfiable")
  def take(branch: Boolean, pc: ScExp): ConcTree =
    throw new Exception("cannot take a branch on a value node")

}

trait ConcolicMonadAnalysis extends ScAbstractSemanticsMonadAnalysis {
  case class ConcolicStore(map: Map[Addr, PostValue]) extends Store[Addr, PostValue] {
    def lookup(a: Addr): Option[PostValue] = map.get(a)
    def extend(a: Addr, v: PostValue): Store[Addr, PostValue] = ConcolicStore(map + (a -> v))
  }

  case class ConcolicContext(
      env: BasicEnvironment[ScConcreteValues.ScAddr],
      store: ConcolicStore,
      pc: ScExp,
      root: ConcTree,
      oracle: ConcolicOracle,
      ignoredIdentities: Set[Identity] = Set())

  case class ConcolicMonad[X](run: ConcolicContext => (ConcolicContext, Option[X]))
  def abstractMonadInstance: ScAbstractSemanticsMonad[ConcolicMonad] = new ScAbstractSemanticsMonad[ConcolicMonad] {

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

  case class PS(pure: Val, symbolic: ScExp) extends IsPostValue

  def modifyTree(f: ConcTree => ConcTree): ScEvalM[()] = ConcolicMonad { context =>
    (context.copy(root = f(context.root)), Some(()))
  }

  override type M[X] = ConcolicMonad[X]
  override type PostValue = PS
  override type StoreCache = ConcolicStore
  override type Val = ConcreteValues.Value
  override type ConcreteStore = StoreCache
  override type Env = BasicEnvironment[Addr]
  override type Addr = ScConcreteValues.ScAddr

  override def modifyPC(f: PC => PC): ScEvalM[()] = ConcolicMonad { context =>
    (context.copy(pc = f(context.pc)), Some(()))
  }

  override def modifyEnv(f: Env => Env): ScEvalM[()] = ConcolicMonad { context =>
    (context.copy(env = f(context.env)), Some(()))
  }

  override def withEnv[B](f: Env => ScEvalM[B]): ScEvalM[B] = ConcolicMonad { context =>
    f(context.env).m.run(context)
  }

  override def withIgnoredIdentities[X](f: List[Identity] => X): ScEvalM[X] = ConcolicMonad { context =>
    val res = f(context.ignoredIdentities.toList)
    (context, Some(res))
  }

  override def addIgnored(idns: Iterable[Identity]): ScEvalM[Unit] = ConcolicMonad { context =>
    (context.copy(ignoredIdentities = context.ignoredIdentities ++ idns), Some(()))
  }

  override def value(v: Val, s: ScExp): PostValue = PS(v, s)

  override def nondet[X](
      t: ScEvalM[X],
      f: ScEvalM[X],
      v: Option[Boolean]
    ): ScEvalM[X] = nondets(Set(t, f))

  override def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = ConcolicMonad { context =>
    if (s.size == 2) {
      // two branches, usually from if condition
      val root = context.root
      val cs = s.toList
      val (leftContext, leftValue) = cs(0).m.run(context)
      val (rightContext, rightValue) = cs(1).m.run(context)
      (leftValue, rightValue) match {
        case (Some(v), None) => {
          val newRoot = root.take(true, leftContext.pc)
          root.take(false, rightContext.pc)
          (leftContext.copy(root = newRoot), Some(v))
        }
        case (None, Some(v)) => {
          val newRoot = root.take(false, rightContext.pc)
          root.take(true, leftContext.pc)
          (rightContext.copy(root = newRoot), Some(v))
        }

        case (None, None) =>
          // no path was possible
          throw new Exception("at least one path should be possible")

        case (_, _) =>
          throw new Exception("Non-determinism not allowed in concolic tester")
      }
    } else if (s.size > 2) {
      throw new Exception("Non-determinism is not allowed in the concolic tester (size > 2)")
    } else if (s.size == 1) {
      // single path, determnistic
      s.head.m.run(context)
    } else {
      // nothing to be deterministic about, this is a dead path
      (context, None)
    }
  }

  override def withPc[X](f: PC => X): ScEvalM[X] = ConcolicMonad { context =>
    (context, Some(f(context.pc)))
  }

  override def withStoreCacheExplicit[X](f: StoreCache => (X, StoreCache)): ScEvalM[X] = ConcolicMonad { context =>
    val (x, next) = f(context.store)
    (context.copy(store = next), Some(x))
  }

  override def withStoreCache[X](f: ConcolicStore => ScEvalM[X]): ScEvalM[X] = ConcolicMonad { context =>
    f(context.store).m.run(context)
  }

  // Same as addToCache since we are not in an abstract domain
  override def joinInCache(addr: Addr, value: PostValue): ScEvalM[()] = addToCache((addr, value))

  override def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = ConcolicMonad { context =>
    c.m.run(context) match {
      case (newContext, Some(vs)) if vs.size == 1 => (newContext, Some(vs.toList(0)))
      case (newContext, Some(vs)) if vs.size == 0 => (newContext, None)
      case (newContext, None)                     => (newContext, None)
      case (_, _)                                 => throw new Exception("only one or zero options allowed in concolic execution")
    }
  }

  override def printStore: ScEvalM[()] = ???

  override def write(addr: Addr, value: PostValue): ScEvalM[()] = modifyStoreCache { cache =>
    cache.update(addr, value).asInstanceOf[StoreCache]
  }

  override def readSafe(addr: Addr): ScEvalM[PostValue] = withStoreCache { cache =>
    cache.lookup(addr) match {
      case Some(v) => pure(v)
      case None    => result(ConcreteValues.Value.Nil)
    }
  }

  /** Forcefully write to the store */
  def writeForce(addr: Addr, value: PostValue): ScEvalM[()] = write(addr, value)

  /** Run the given computation without any initial context */
  def run[A](c: ScEvalM[A]): A =
    c.m
      .run(
        ConcolicContext(
          env = BasicEnvironment(Map()),
          store = ConcolicStore(Map()),
          pc = ScNil(),
          root = NilNode
        )
      )
      ._2
      .get
}
