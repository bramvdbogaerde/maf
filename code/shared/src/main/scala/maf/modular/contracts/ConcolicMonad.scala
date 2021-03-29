package maf.modular.contracts

import maf.modular.contracts.semantics._
import maf.language.contracts.ScExp
import maf.core.Store
import maf.core.BasicEnvironment
import maf.core.Identity
import maf.language.contracts.lattices.ScConcreteValues
import maf.language.scheme.interpreter.ConcreteValues
import maf.concolic.contracts._
import maf.language.contracts.ScNil

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
      inputGenerator: InputGenerator,
      trail: List[Boolean] = List(),
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
    val newPc = f(context.pc)
    // TODO: remove redundant pc variable in the state
    (context.copy(pc = newPc), Some(()))
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

  /**
   * Creates a new root given the new left and right branches.
   * If it detects that the new branches are incosistent with the current root,
   * then it fails
   */
  protected def branches(
      root: ConcTree,
      left: ConcTree,
      right: ConcTree,
      pc: PC
    ): ConcTree = root match {
    case TreeNode(oldLeft, oldRight, pc) =>
      val newLeft = oldLeft match {
        case UnexploredNode(_) | _ if oldLeft.pc == left.pc => left
        case _                                              =>
          // current left is not unexplored, and it also didn't adhere
          // to the current tree structure, which means that we have found a bug
          throw new Exception("Inconsistent tree")
      }

      val newRight = oldRight match {
        case UnexploredNode(_) | _ if oldRight.pc == right.pc => right
        case _                                                =>
          // current right is not unexplored, and it also didn't adhere
          // to the current tree structure, which means that we have found a bug
          throw new Exception("Incosistent tree")
      }

      TreeNode(newLeft, newRight, pc)
    case UnexploredNode(_) => TreeNode(left, right, pc)
    case _                 => throw new Exception("Incosistent tree")
  }

  override def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = ConcolicMonad { context =>
    if (s.size == 2) {
      // two branches, usually from if condition
      val cs = s.toList
      val (leftContext, leftValue) = cs(0).m.run(context)
      val (rightContext, rightValue) = cs(1).m.run(context)

      val leftTree = leftContext.root.modifyPc(pc = leftContext.pc)
      val rightTree = rightContext.root.modifyPc(pc = rightContext.pc)
      val newRoot = branches(context.root, leftTree, rightTree, context.pc)

      (leftValue, rightValue) match {
        case (Some(v), None) =>
          (leftContext.copy(root = newRoot, trail = true :: leftContext.trail), Some(v))
        case (None, Some(v)) =>
          (rightContext.copy(root = newRoot, trail = false :: rightContext.trail), Some(v))

        case (None, None) =>
          (context.copy(root = newRoot), None)

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

  def addSymbolicVariable(variable: String): ScEvalM[()] = unit // TODO

  def withInputGenerator[A](f: InputGenerator => ScEvalM[A]): ScEvalM[A] = ConcolicMonad { context =>
    f(context.inputGenerator).m.run(context)
  }

  def modifyConcTree[A](f: PC => ConcTree): ScEvalM[()] = ConcolicMonad { context =>
    // only allow modification when we are replacing an unexplored node
    val newRoot = context.root match {
      case _: UnexploredNode => f(context.root.pc)
      case _                 => context.root
    }
    (context.copy(root = newRoot), Some(()))
  }

  /** Run the given computation without any initial context */
  def run[A](c: ScEvalM[A]): A =
    c.m
      .run(
        ConcolicContext(
          env = BasicEnvironment(Map()),
          store = ConcolicStore(Map()),
          pc = ScNil(),
          root = NilNode,
          inputGenerator = InputGenerator(Map())
        )
      )
      ._2
      .get
}
