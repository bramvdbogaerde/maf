package maf.concolic.contracts

import maf.core.{BasicEnvironment, Identity, Store}
import maf.language.contracts.lattices.ScConcreteValues
import maf.language.contracts.{ScExp, ScNil}
import maf.language.scheme.interpreter.ConcreteValues
import maf.modular.contracts.semantics._

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
      ignoredIdentities: Set[Identity] = Set(),
      inputs: Map[String, Val] = Map(),
      error: Boolean = false)

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

  def modifyTree(f: ConcTree => ConcTree): ScEvalM[Unit] = ConcolicMonad { context =>
    (context.copy(root = f(context.root)), Some(()))
  }

  override type M[X] = ConcolicMonad[X]
  override type PostValue = PS
  override type StoreCache = ConcolicStore
  override type Val = ConcreteValues.Value
  type ConcreteStore = StoreCache
  override type Env = BasicEnvironment[Addr]
  override type Addr = ScConcreteValues.ScAddr

  override def modifyPC(f: PC => PC): ScEvalM[Unit] = ConcolicMonad { context =>
    val newPc = f(context.pc)
    // TODO: remove redundant pc variable in the state
    (context.copy(pc = newPc), Some(()))
  }

  override def modifyEnv(f: Env => Env): ScEvalM[Unit] = ConcolicMonad { context =>
    (context.copy(env = f(context.env)), Some(()))
  }

  override def withEnv[B](f: Env => ScEvalM[B]): ScEvalM[B] = ConcolicMonad { context =>
    f(context.env).m.run(context)
  }

  override def withIgnoredIdentities[X](f: List[Identity] => ScEvalM[X]): ScEvalM[X] = ConcolicMonad { context =>
    f(context.ignoredIdentities.toList).m.run(context)
  }

  override def addIgnored(idns: Iterable[Identity]): ScEvalM[Unit] = ConcolicMonad { context =>
    (context.copy(ignoredIdentities = context.ignoredIdentities ++ idns), Some(()))
  }

  override def value(v: Val, s: ScExp): PostValue = PS(v, s)

  override def nondet[X](
      t: ScEvalM[X],
      f: ScEvalM[X],
      v: Option[Boolean]
    ): ScEvalM[X] = ConcolicMonad { context =>
    // note that this is fundemantally different from `nondets` as in
    // `nondets` the list of computations is unordered

    // we replace the current root that is able to split
    val newRoot =
      context.root.replaceAt(context.trail.reverse, branches(context.root.followTrail(context.trail.reverse), NilNode, NilNode, context.pc))

    // true to execute both branches, as we are in a concrete execution, only one branch should result in a value
    val (trueContext, trueRes) = t.m.run(context.copy(root = newRoot, trail = true :: context.trail))
    val (falseContext, falseRes) = f.m.run(context.copy(root = newRoot, trail = false :: context.trail))

    (trueRes, falseRes) match {
      case (Some(v), None) =>
        // true branch resulted in a value
        // update the false branch as well
        val updatedRoot = trueContext.root.replaceAt((false :: context.trail).reverse, UnexploredNode(falseContext.pc))
        // TODO: this is not so nice, as we now have safeguards in the tree structure against replacing TreeNodes with UnexploredNode
        // safeguards would be better here and leaving the tree only as a datastructure
        (trueContext.copy(root = updatedRoot), Some(v))
      case (None, Some(v)) =>
        // false branch result in a vlaue
        val updatedRoot = falseContext.root.replaceAt((true :: context.trail).reverse, UnexploredNode(trueContext.pc))
        (falseContext.copy(root = updatedRoot), Some(v))
      case (None, None) =>
        // neither resultedin  a value
        //
        if (trueContext.error) {
          val updatedRoot = trueContext.root.replaceAt((false :: context.trail).reverse, UnexploredNode(falseContext.pc))
          (trueContext.copy(root = updatedRoot), None)
        } else if (falseContext.error) {
          val updatedRoot = falseContext.root.replaceAt((true :: context.trail).reverse, UnexploredNode(trueContext.pc))
          (falseContext.copy(root = updatedRoot), None)
        } else {
          throw new Exception("concolic tester is in an invalid state")
        }
      case (_, _) =>
        // both branches resulted in a value
        throw new Exception("non determinism not allowed")
    }
  }

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
    case TreeNode(oldLeft, oldRight, oldPc) =>
      val newLeft = oldLeft match {
        case UnexploredNode(_) | NilNode => left
        case _ if oldLeft.pc != left.pc  => oldLeft
        case _                           => left
      }

      val newRight = oldRight match {
        case UnexploredNode(_) | NilNode  => right
        case _ if oldRight.pc != right.pc => oldRight
        case _                            => right
      }

      TreeNode(newLeft, newRight, pc)
    case UnexploredNode(_) | NilNode => TreeNode(left, right, pc)
    case _ =>
      throw new Exception("Incosistent tree")
  }

  override def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = ConcolicMonad { context =>
    if (s.size == 2) {
      val elements = s.toList
      val (firstContext, firstRes) = elements(0).m.run(context)
      val (secondContext, secondRes) = elements(1).m.run(context)
      (firstRes, secondRes) match {
        case (Some(_), None) =>
          (firstContext, firstRes)
        case (None, Some(_)) =>
          (secondContext, secondRes)
        case (None, None) if firstContext.error && !secondContext.error =>
          (firstContext, None)
        case (None, None) if !firstContext.error && secondContext.error =>
          (secondContext, None)
        case _ =>
          throw new Exception("invalid case in nondets, at least one path must be an error or a value")
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
  override def joinInCache(addr: Addr, value: PostValue): ScEvalM[Unit] = addToCache((addr, value))

  override def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = ConcolicMonad { context =>
    c.m.run(context) match {
      case (newContext, Some(vs)) if vs.size == 1 => (newContext, Some(vs.toList(0)))
      case (newContext, Some(vs)) if vs.size == 0 => (newContext, None)
      case (newContext, None)                     => (newContext, None)
      case (_, _)                                 => throw new Exception("only one or zero options allowed in concolic execution")
    }
  }

  override def printStore: ScEvalM[Unit] = ???

  override def write(addr: Addr, value: PostValue): ScEvalM[Unit] = modifyStoreCache { cache =>
    cache.update(addr, value).asInstanceOf[StoreCache]
  }

  override def readSafe(addr: Addr): ScEvalM[PostValue] = withStoreCache { cache =>
    cache.lookup(addr) match {
      case Some(v) => pure(v)
      case None    => result(ConcreteValues.Value.Nil)
    }
  }

  /** Forcefully write to the store */
  def writeForce(addr: Addr, value: PostValue): ScEvalM[Unit] = write(addr, value)

  def addSymbolicVariable(variable: String): ScEvalM[Unit] = unit // TODO

  def withInputGenerator[A](f: InputGenerator => ScEvalM[A]): ScEvalM[A] = ConcolicMonad { context =>
    f(context.inputGenerator).m.run(context)
  }

  def error[A](f: PC => ConcTree): ScEvalM[Unit] = ConcolicMonad { context =>
    // only allow modification when we are replacing an unexplored node
    val newRoot = context.root.replaceAt(context.trail.reverse, f(context.pc))
    (context.copy(root = newRoot, error = true), Some(()))
  }

  def withContext[A](f: ConcolicContext => ScEvalM[A]): ScEvalM[A] = ConcolicMonad { context =>
    f(context).m.run(context)
  }

  /** Run the given computation without any initial context */
  def run(c: ScEvalM[PostValue]): PostValue =
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
