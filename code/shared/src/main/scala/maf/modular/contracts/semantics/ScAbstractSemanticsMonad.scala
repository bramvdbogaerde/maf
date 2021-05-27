package maf.modular.contracts.semantics

import maf.language.contracts.ScIdentifier
import maf.core.Store
import maf.core.Identity
import maf.core.Address
import maf.language.contracts.ScExp
import maf.core.Environment
import maf.core.BasicEnvironment
import maf.language.contracts.ScNil
import maf.ScSettings

case class AddrNotFound[A](addr: A) extends Exception {
  override def getMessage(): String =
    s"Address ${addr} not found"
}

trait Monad[M[_]] {

  /** Injects a value in the Monad */
  def pure[X](v: => X): M[X]

  /** Injects the unit in the Monad */
  def unit: M[()] = pure(())

  def map[X, Y](m: M[X], f: X => Y): M[Y] =
    flatMap(m, (x: X) => pure(f(x)))

  def flatMap[X, Y](m: M[X], f: X => M[Y]): M[Y]

  def >>=[A, B](m: M[A], f: A => M[B]): M[B] =
    flatMap(m, f)

  def >>[A, B](m: M[A], f: => M[B]): M[B] =
    flatMap(m, (_: A) => f)
}

/** This typeclass represents an extended version of a Monad */
trait ScAbstractSemanticsMonad[M[_]] extends Monad[M] {

  /**
   * Is supposed to halt the computation, when
   *  the monad is sequenced with another
   *
   *  <code>
   *  void >> ( effectful { println("not reachable") } )
   *  </code>
   */
  def void[X]: M[X]
}

/**
 * This trait specificies an analysis that provides
 * (a) a monad that is able to handle non deterministic behaviour
 * (b) auxilary functions for working with this monad
 *
 * It can be mixed in with another trait or class so that the monad
 * and its auxilary functions become available
 */
trait ScAbstractSemanticsMonadAnalysis {
  /*
   * The monad that will be used to guide the analysis
   */
  type M[_]
  /*
   * The type of the path condition (e.g. ScExp)
   */
  type PC = ScExp

  /** A value combined with some symbolic information */
  type PostValue <: IsPostValue

  /** The type of a mapping between an addresses and a value */
  type StoreCache <: Store[Addr, PostValue]

  /** The t ype of a raw value without any symbolic information */
  type Val

  /** The type of an address */
  type Addr <: Address

  /** The type of primitive values */
  type Prim

  /**
   * The type of an environment, which should be a mapping between
   *  an identifier (e.g. string) and an address
   */
  type Env = BasicEnvironment[Addr]

  /** An instance of the monad typeclass */
  def abstractMonadInstance: ScAbstractSemanticsMonad[M]

  trait IsPostValue {
    def pure: Val
    def symbolic: ScExp
  }

  case class ScEvalM[X](m: M[X]) {
    def map[Y](f: X => Y): ScEvalM[Y] =
      ScEvalM(abstractMonadInstance.map(m, f))

    def flatMap[Y](f: X => ScEvalM[Y]): ScEvalM[Y] =
      ScEvalM(abstractMonadInstance.flatMap(m, (x: X) => f(x).m))

    def >>=[B](f: X => ScEvalM[B]): ScEvalM[B] =
      flatMap(f)

    def >>[B](f: => ScEvalM[B]): ScEvalM[B] =
      flatMap(_ => f)
  }

  implicit def wrap[X](m: M[X]): ScEvalM[X] = ScEvalM(m)

  /** Injects the value in the monad */
  def pure[X](v: => X): ScEvalM[X] = ScEvalM(abstractMonadInstance.pure(v))

  /** Injects the unit in the monad */
  def unit: ScEvalM[()] = ScEvalM(abstractMonadInstance.unit)

  /*
   * See ScAbstractSemanticsMonad for details
   */
  def void[X]: ScEvalM[X] =
    ScEvalM(abstractMonadInstance.void)

  def sequence1[X](xs: List[ScEvalM[X]]): ScEvalM[List[X]] = xs match {
    case List() => void
    case _      => sequence(xs)
  }

  def sequenceFlatten[X](xs: List[ScEvalM[Option[X]]]): ScEvalM[List[X]] = xs match {
    case List() => pure(List())
    case _ =>
      xs.head.flatMap(v =>
        sequenceFlatten(xs.tail).flatMap(results =>
          v match {
            case Some(result) => pure(result :: results)
            case _            => pure(results)
          }
        )
      )
  }

  /**
   * Runs the given sequence of actions in the given order,
   * and collects their results in a list
   */
  def sequence[X](xs: List[ScEvalM[X]]): ScEvalM[List[X]] = xs match {
    case List() => pure(List())
    case _ =>
      for {
        result <- xs.head
        results <- sequence(xs.tail)
      } yield (result :: results)
  }

  /**
   * Same as <code>sequence</code> but only returns the result of the last
   * action in the sequqence of actions
   */
  def sequenceLast[X](xs: List[ScEvalM[X]]): ScEvalM[X] =
    sequence(xs).map(_.last)

  /**
   * Executes some action <code>c</code> for its side effects but also
   *  explicitly states that it is for debugging reasons
   */
  def debug(c: => ()): ScEvalM[()] = unit.flatMap { _ =>
    if (ScSettings.DEBUG_STATIC || ScSettings.DEBUG_STATIC) {
      print(s"[debug] ")
      c
    }
    pure(())
  }

  /** Executes the given action simply for its side effects */
  def effectful(c: => ()): ScEvalM[()] = unit >> {
    c
    pure(())
  }

  /**
   * Executes cthe given action for its side effects and returns
   *  the return value
   */
  def pureWith[A](c: => A): ScEvalM[A] = unit.flatMap { _ =>
    val result = c
    pure(result)
  }

  /**
   * Returns a computation that
   * wraps the given value into a value with symbolic information,
   */
  def result(v: Val): ScEvalM[PostValue] = pure(value(v))

  /** Modifies the PC using the given function */
  def modifyPC(f: PC => PC): ScEvalM[()]

  /**
   * Replaces the path condition with another one and
   *  runs the given computation with the updated path condition
   */
  def replacePc[X](pc: PC)(c: ScEvalM[X]): ScEvalM[X] =
    modifyPC(_ => pc) >> c

  /** Adds symbolic information to the given raw value */
  def value(v: Val): PostValue = value(v, ScNil())

  /** Adds the given symbolic information to the given raw value */
  def value(v: Val, s: ScExp): PostValue

  /**
   * Applies f with the list of ignored identities,
   * ignored identities refer to values of which the validity of the
   * contract does not matter
   */
  def withIgnoredIdentities[X](f: List[Identity] => ScEvalM[X]): ScEvalM[X]

  /** Adds an ignored identity to the context */
  def addIgnored(idns: Iterable[Identity]): ScEvalM[()]

  /*
   * Applies  the given function with the current environment
   */
  def withEnv[B](f: Env => ScEvalM[B]): ScEvalM[B]

  /** Applies the modification function to the current environment */
  def modifyEnv(f: Env => Env): ScEvalM[()]

  def replaceEnv[B](replacement: Env): ScEvalM[()] =
    modifyEnv(_ => replacement)

  /**
   * Runs the given computation in the environment modified by f,
   *  and restores it afterwards
   */
  def local[B](f: Env => Env, c: ScEvalM[B]): ScEvalM[B] =
    local(modifyEnv(f), c)

  def local[A, B](updateEnv: ScEvalM[A], c: ScEvalM[B]): ScEvalM[B] = withEnv { oldEnv =>
    updateEnv >> c >>= (value => replaceEnv(oldEnv) >> pure(value))
  }

  /**
   * Returns a computation that looks up the given identifier in the current"
   * environment and returns its associated address
   */
  def lookup(identifier: String): ScEvalM[Addr] =
    withEnv(env => pure(env.lookup(identifier).getOrElse(throw new Exception(s"variable $identifier not found"))))

  // TODO: this is actually something that belongs elsewhere, maybe in the main analysis,
  // we don't want to know about allocations and components here
  //def lookupOrDefine(identifier: ScIdentifier, component: Component): ScEvalM[Addr] = withEnv { (env) =>
  //  pure(env.lookup(identifier.name).getOrElse {
  //    val addr = allocVar(identifier, context(component))
  //    addr
  //  })
  //}

  /**
   * Nondeterministicly execute the given branches
   * optionally, a value can be given that determines which branch was chosen.
   * True = the t branch
   * False = the f branch
   */
  def nondet[X](
      t: ScEvalM[X],
      f: ScEvalM[X],
      v: Option[Boolean] = None
    ): ScEvalM[X]

  /**
   * Same as nondet but works with a set of branches, here the optional v value to
   * indicate which branch was taken cannot be used.
   */
  def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X]

  /**
   * Returns a computation that applies the given function with the current
   * path condition
   */
  def withPc[X](f: PC => X): ScEvalM[X]

  /**
   * Returns a computation that applies the given function with the current
   * store cache.
   */
  def withStoreCache[X](f: StoreCache => ScEvalM[X]): ScEvalM[X]

  /**
   * Returns a computation that applies the given function on the current store cache
   * and expects a tuple of a value and a new store cache
   */
  def withStoreCacheExplicit[X](f: StoreCache => (X, StoreCache)): ScEvalM[X]

  def modifyStoreCache(f: StoreCache => StoreCache): ScEvalM[()] =
    withStoreCacheExplicit(cache => ((), f(cache)))

  // TODO: we don't want to expose the entire context, check the big step semantics
  // to ensure that we only use the auxilary functions
  // def withContext[X](f: Context => ScEvalM[X]): ScEvalM[X]

  /**
   * Forcefully adds t he given mapping to the store, should only be
   * used when overapproximations are not necessary, or when a force
   * update is required.
   */
  def addToCache(mapping: (Addr, PostValue)): ScEvalM[()] = modifyStoreCache { cache =>
    cache.extend(mapping._1, mapping._2).asInstanceOf[StoreCache]
  }

  /** Same as addToCache but joins the value in the cache according to some lattice (only for abstract domains) */
  def joinInCache(addr: Addr, value: PostValue): ScEvalM[()]

  /** Adds a binding to the environment */
  def addBindingToEnv(ident: ScIdentifier, addr: Addr): ScEvalM[()] = {
    modifyEnv(env => env.extend(ident.name, addr))
  }

  /**
   * Given a computation that yields states that contain sets of values, this operator yields a single computation
   * that gives rises to a state for every element in the given set.
   */
  def options[X](c: ScEvalM[Set[X]]): ScEvalM[X]

  /**
   * Action that prints the current store as a table
   * to the screen. Useful for debugging.
   */
  def printStore: ScEvalM[()]

  /** Removes the given addresses from the store */
  def evict(addresses: List[Addr]): ScEvalM[()]

  /** Reads from the given address in the store */
  def read(addr: Addr): ScEvalM[PostValue] = withStoreCache { cache =>
    pure(cache.lookup(addr).getOrElse(throw AddrNotFound(addr)))
  }

  /**
   * Same as `read` but ensures that it does not result
   * in an exception in strict analyses that requires
   * values to be defined in the store before they are used.
   */
  def readSafe(addr: Addr): ScEvalM[PostValue]

  /**
   * Writes the given value to the given address
   *
   * @param addr the address to write the value to
   * @param value the value to write to the given address
   * @return a computation that writes the given value to the address
   */
  def write(addr: Addr, value: PostValue): ScEvalM[()]

  /** Forcefully write to the store */
  def writeForce(addr: Addr, value: PostValue): ScEvalM[()]

  /** Run the given computation without any initial context */
  def run(c: ScEvalM[PostValue]): PostValue

  // TODO: again this refers to components and allocations, this should reside elsewhere
  //def extended[X](ident: ScIdentifier, component: Component)(c: Addr => ScEvalM[X]): ScEvalM[X] =
  //  extended(List(ident), component)(addrs => c(addrs.head))

  //  def extended[X](idents: List[ScIdentifier], component: Component)(c: List[Addr] => ScEvalM[X]): ScEvalM[X] = ScEvalM { (ctx) =>
  //    val addrs = idents.map(ident => allocVar(ident, context(component)))
  //    val extendedEnv = idents.zip(addrs).foldLeft(ctx.env)((env, p) => env.extend(p._1.name, p._2))
  //    c(addrs).run(ctx.copy(env = extendedEnv)).map { case (updatedContext, value) =>
  //      (updatedContext.copy(env = ctx.env), value)
  //    }
  //  }

  //def addBindingToEnv(ident: ScIdentifier, component: Component): ScEvalM[()] = ScEvalM { (ctx) =>
  //  val addr = allocVar(ident, context(component))
  //  Set((ctx.copy(env = ctx.env.extend(ident.name, addr)), ()))
  //}

  /**
   * Given a computation that yields a value corresponding to a certain lattice, this function runs the computation
   * on the given context, and joins all the values of the resulting states together using the join operator of the
   * lattice.
   */
  // TODO: figure out if this is actually used, this must be migrated to a more concrete implementation because
  // the context is not available in the abstract monad
  //def merged[L: Lattice](c: ScEvalM[L])(context: Context): (L, Store) = {
  //  val (v, store, _) = mergedPC(c)(context)
  //  (v, store)
  //}

  //def mergedPC[L: Lattice](c: ScEvalM[L])(context: Context): (L, Store, PC) = {
  //  import maf.lattice.MapLattice._
  //  val result = c.run(context)
  //  // optimisation: if the number of output states is one, then we don't need to merge anything
  //  if (result.size == 1) {
  //    val (context, v) = result.head
  //    (v, context.store, context.pc)
  //  } else {
  //    result.foldLeft[(L, Store, PC)]((Lattice[L].bottom, Lattice[Store].bottom, ScNil()))((acc, v) =>
  //      v match {
  //        case (context, l) =>
  //          (Lattice[L].join(acc._1, l), Lattice[Store].join(acc._2, context.store), acc._3.or(context.pc))
  //      }
  //    )
  //  }
  //}

  //def compute(c: ScEvalM[PostValue])(context: Context): (Value, Store, List[ScExp]) = {
  //  // TODO: this looks a lot like mergedPC, see if we can abstract this away a bit

  //  import maf.lattice.MapLattice._
  //  val result = c.run(context)

  //  // optimisation: if the number of output states is one, then we don't need to merge anything
  //  if (result.size == 1) {
  //    val (context, (v, s)) = result.head
  //    (v, context.store, List(s))
  //  } else {
  //    result.foldLeft[(Value, Store, List[ScExp])]((lattice.bottom, Lattice[Store].bottom, List()))((acc, v) =>
  //      v match {
  //        case (context, (l, s)) =>
  //          (lattice.join(acc._1, l), Lattice[Store].join(acc._2, context.store), s :: acc._3)
  //      }
  //    )
  //  }
  //}
  //
  // def mergeStores(calleeStore: Store): ScEvalM[()]
  // sequence(calleeStore.view.map { case (addr, v) =>
  //   joinInCache(addr, value(v))
  // }.toList).flatMap(_ => unit)

  // def getStore: ScEvalM[Store] = ScEvalM { context =>
  //   Set((context, context.store))
  // }
}
