package maf.modular.contracts.semantics

import maf.core._
import maf.language.contracts.{ScExp, ScIdentifier, ScNil, ScSchemeLattice}

trait ScModAnalysisSemanticsMonad extends ScAbstractSemanticsMonadAnalysis {
  implicit class PS(v: (Val, ScExp)) extends IsPostValue {
    override def pure: Val = v._1
    override def symbolic: PC = v._2
    override def toString(): String =
      s"($pure, $symbolic)"
  }

  object PS {
    def unapply(v: Any): Option[(Val, ScExp)] = v match {
      case s: PS => Some(fromPS(s))
      case _     => None
    }
  }

  implicit def fromPS(ps: PS): (Val, ScExp) =
    (ps.pure, ps.symbolic)

  override type StoreCache = StoreMap[Addr, PostValue]
  override type M[X] = AnalysisMonad[X]
  override type PostValue = PS
  implicit val lattice: ScSchemeLattice[Val, Addr]

  case class Context(
      env: BasicEnvironment[Addr],
      pc: PC,
      cache: StoreCache,
      ignoredIdn: List[Identity] = List()) {
    def store: Map[Addr, Val] =
      cache.map.mapValues(_.pure).toMap
  }

  case class AnalysisMonad[X](run: Context => Set[(Context, X)])
  override def abstractMonadInstance: ScAbstractSemanticsMonad[M] = new ScAbstractSemanticsMonad[AnalysisMonad] {

    override def pure[X](v: => X): AnalysisMonad[X] =
      AnalysisMonad((context) => List((context, v)).toSet)

    override def flatMap[X, Y](m: AnalysisMonad[X], f: X => AnalysisMonad[Y]): AnalysisMonad[Y] =
      AnalysisMonad((context) =>
        m.run(context).flatMap { case (updatedContext, value) =>
          f(value).run(updatedContext)
        }
      )

    override def void[X]: M[X] =
      AnalysisMonad((context) => Set[(Context, X)]())
  }

  implicit def fromStoreCache(store: StoreCache): Map[Addr, PostValue] =
    store.map

  implicit def toStoreCache(store: Map[Addr, PostValue]): StoreCache =
    StoreMap(store)

  implicit def toScEvalMonad[X](analysisMonad: AnalysisMonad[X]): ScEvalM[X] =
    ScEvalM(analysisMonad)

  def withIgnoredIdentities[X](f: List[Identity] => ScEvalM[X]): ScEvalM[X] =
    withContext(context => f(context.ignoredIdn))

  def withContext[X](f: Context => ScEvalM[X]): ScEvalM[X] =
    AnalysisMonad((context) => f(context).m.run(context))

  def addIgnored(idns: Iterable[Identity]): ScEvalM[()] = AnalysisMonad { (context) =>
    List((context.copy(ignoredIdn = context.ignoredIdn ++ idns), ())).toSet
  }

  override def withEnv[X](f: Env => ScEvalM[X]): ScEvalM[X] =
    AnalysisMonad((context) => f(context.env).m.run(context))

  override def modifyEnv(f: BasicEnvironment[Addr] => BasicEnvironment[Addr]): ScEvalM[Unit] =
    AnalysisMonad[()]((context) => List((context.copy(env = f(context.env)), ())).toSet)

  override def nondet[X](
      t: ScEvalM[X],
      f: ScEvalM[X],
      branch: Option[Boolean]
    ): ScEvalM[X] = AnalysisMonad { (context) =>
    val resF = f.m.run(context)
    val resT = t.m.run(context)
    resF ++ resT
  }

  override def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = AnalysisMonad { (context) =>
    s.flatMap(_.m.run(context))
  }

  /** Run the given computation without any initial context */
  override def run(c: ScEvalM[PostValue]): PostValue = {
    val (v, _, _) = compute(c)(Context(env = BasicEnvironment(Map()), pc = ScNil(), cache = StoreMap(Map())))
    (v, ScNil())
  }

  override def withPc[X](f: PC => X): ScEvalM[X] = AnalysisMonad { (context: Context) =>
    Set((context, f(context.pc)))
  }

  override def modifyPC(f: PC => PC): ScEvalM[Unit] = AnalysisMonad { context =>
    Set((context.copy(pc = f(context.pc)), ()))
  }

  override def withStoreCache[X](f: StoreCache => ScEvalM[X]): ScEvalM[X] = AnalysisMonad { (context) =>
    f(context.cache).m.run(context)
  }

  /**
   * Returns a computation that applies the given function on the current store cache
   * and expects a tuple of a value and a new store cache
   */
  override def withStoreCacheExplicit[X](f: StoreCache => (X, StoreCache)): ScEvalM[X] = ???

  override def joinInCache(addr: Addr, value: PostValue): ScEvalM[()] = AnalysisMonad { (context) =>
    val valueInStore: PostValue = context.cache.lookup(addr).getOrElse(new PS((lattice.bottom, ScNil())))
    val joinedValue: Val = lattice.join(valueInStore.pure, value._1)
    val updatedCache = context.cache.updated(addr, PS((joinedValue, ScNil()))) // TODO: check if ScNil cannot be more precise
    Set((context.copy(cache = StoreMap(updatedCache)), ()))
  }

  /**
   * Given a computation that yields states that contain sets of values, this operator yields a single computation
   * that gives rises to a state for every element in the given set.
   */
  override def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = AnalysisMonad((context) =>
    c.m.run(context).flatMap { case (updatedContext, set) =>
      set.map((updatedContext, _))
    }
  )

  /**
   * Action that prints the current store as a table
   * to the screen. Useful for debugging.
   */
  override def printStore: ScEvalM[()] = withStoreCache { store =>
    import maf.util.StoreUtil._
    println(store.map.asTable.prettyString())
    unit
  }

  override def evict(addresses: List[Addr]): ScEvalM[()] = AnalysisMonad { context =>
    Set((context.copy(cache = context.cache.removedAll(addresses)), ()))
  }

  override def readSafe(addr: Addr): ScEvalM[PostValue] = withStoreCache { store =>
    pure(store.get(addr).getOrElse((lattice.bottom, ScNil())))
  }

  def compute(c: ScEvalM[PostValue])(context: Context): (Val, Map[Addr, Val], List[ScExp]) = {
    type Store = Map[Addr, Val]
    import maf.lattice.MapLattice._

    // TODO: this looks a lot like mergedPC, see if we can abstract this away a bit
    val result = c.m.run(context)

    // optimisation: if the number of output states is one, then we don't need to merge anything
    if (result.size == 1) {
      val (context, ps) = result.head
      (ps.pure, context.store, List(ps.symbolic))
    } else {
      result.foldLeft((lattice.bottom, Lattice[Store].bottom, List[PC]()))((acc, v) =>
        v match {
          case (context, ps) =>
            (lattice.schemeLattice.join(acc._1, ps.pure), Lattice[Store].join(acc._2, context.store), ps.symbolic :: acc._3)
        }
      )
    }
  }

  override def value(v: Val, e: ScExp): PS = new PS((v, e))

}

/** This trait provides a monad that aids with defining a big step semantics for soft contract verification */
trait ScSchemeSemanticsMonad extends ScModSemanticsScheme { outer =>
  type PC = ScExp
  type PostValue = (Value, ScExp)
  type StoreCache = Map[Addr, PostValue]
  case class Context(
      env: Environment[Addr],
      pc: PC,
      cache: StoreCache,
      ignoredIdn: List[Identity] = List()) {
    def store: Store = cache.view.mapValues(_._1).toMap
  }

  def value(v: Value): PostValue = (v, ScNil())

  object ScEvalM {
    def pure[X](v: => X): ScEvalM[X] = ScEvalM((context) => List((context, v)).toSet)
    def unit: ScEvalM[()] = pure(())
    def void[X]: ScEvalM[X] =
      ScEvalM((context) => Set[(Context, X)]())

    case class ScEvalM[X](run: Context => Set[(Context, X)]) {
      def map[Y](f: X => Y): ScEvalM[Y] = ScEvalM { (context) =>
        run(context).map { case (updatedContext, value) =>
          (updatedContext, f(value))
        }
      }

      def flatMap[Y](f: X => ScEvalM[Y]): ScEvalM[Y] = ScEvalM((context) =>
        run(context).flatMap { case (updatedContext, value) =>
          f(value).run(updatedContext)
        }
      )

      def >>=[B](f: X => ScEvalM[B]): ScEvalM[B] =
        flatMap(f)

      def >>[B](f: => ScEvalM[B]): ScEvalM[B] =
        flatMap(_ => f)
    }

    def sequence[X](xs: List[ScEvalM[X]]): ScEvalM[List[X]] = xs match {
      case List() => pure(List())
      case _ =>
        for {
          result <- xs.head
          results <- sequence(xs.tail)
        } yield (result :: results)
    }

    def withIgnoredIdentities(f: List[Identity] => Unit): ScEvalM[()] =
      withContext(context => effectful(f(context.ignoredIdn)))

    def addIgnored(idns: Iterable[Identity]): ScEvalM[()] = ScEvalM { (context) =>
      List((context.copy(ignoredIdn = context.ignoredIdn ++ idns), ())).toSet
    }

    def sequenceLast[X](xs: List[ScEvalM[X]]): ScEvalM[X] =
      sequence(xs).map(_.last)

    def withEnv[B](f: Environment[Addr] => ScEvalM[B]): ScEvalM[B] =
      ScEvalM((context) => f(context.env).run(context))

    def lookup(identifier: String): ScEvalM[Addr] = withEnv { (env) =>
      pure(env.lookup(identifier).getOrElse(throw new Exception(s"variable ${identifier} not found")))
    }

    def lookupOrDefine(identifier: ScIdentifier, component: Component): ScEvalM[Addr] = withEnv { (env) =>
      pure(env.lookup(identifier.name).getOrElse {
        val addr = allocVar(identifier, context(component))
        addr
      })
    }

    def nondet[X](t: ScEvalM[X], f: ScEvalM[X]): ScEvalM[X] = ScEvalM { (context) =>
      val resF = f.run(context)
      val resT = t.run(context)
      resF ++ resT
    }

    def nondets[X](s: Set[ScEvalM[X]]): ScEvalM[X] = ScEvalM { (context) =>
      s.flatMap(_.run(context))
    }

    def withPc[X](f: PC => X): ScEvalM[X] = ScEvalM { (context) =>
      Set((context, f(context.pc)))
    }

    def withStoreCache[X](f: StoreCache => ScEvalM[X]): ScEvalM[X] = ScEvalM { (context) =>
      f(context.cache).run(context)
    }

    def withContext[X](f: Context => ScEvalM[X]): ScEvalM[X] = ScEvalM((context) => f(context).run(context))

    def addToCache(mapping: (Addr, PostValue)): ScEvalM[()] = ScEvalM { (context) =>
      List((context.copy(cache = context.cache + mapping), ())).toSet
    }

    def joinInCache(addr: Addr, value: PostValue): ScEvalM[()] = ScEvalM { (context) =>
      Set(
        (
          (context.copy(cache = context.cache.updated(addr, (lattice.join(context.store.getOrElse(addr, lattice.bottom), value._1), value._2)))),
          ()
        )
      )
    }

    def replacePc[X](pc: PC)(c: ScEvalM[X]): ScEvalM[X] = ScEvalM { (context) =>
      c.run(context.copy(pc = pc))
    }

    /**
     * This function creates a computation that yields a single state contain the abstract value with no
     * symbolic information.
     */
    def result(v: Value): ScEvalM[PostValue] = pure(value(v))

    def extended[X](ident: ScIdentifier, component: Component)(c: Addr => ScEvalM[X]): ScEvalM[X] =
      extended(List(ident), component)(addrs => c(addrs.head))

    def extended[X](idents: List[ScIdentifier], component: Component)(c: List[Addr] => ScEvalM[X]): ScEvalM[X] = ScEvalM { (ctx) =>
      val addrs = idents.map(ident => allocVar(ident, context(component)))
      val extendedEnv = idents.zip(addrs).foldLeft(ctx.env)((env, p) => env.extend(p._1.name, p._2))
      c(addrs).run(ctx.copy(env = extendedEnv)).map { case (updatedContext, value) =>
        (updatedContext.copy(env = ctx.env), value)
      }
    }

    def addBindingToEnv(ident: ScIdentifier, component: Component): ScEvalM[()] = ScEvalM { (ctx) =>
      val addr = allocVar(ident, context(component))
      Set((ctx.copy(env = ctx.env.extend(ident.name, addr)), ()))
    }

    /**
     * Given a computation that yields a value corresponding to a certain lattice, this function runs the computation
     * on the given context, and joins all the values of the resulting states together using the join operator of the
     * lattice.
     */
    def merged[L: Lattice](c: ScEvalM[L])(context: Context): (L, Store) = {
      val (v, store, _) = mergedPC(c)(context)
      (v, store)
    }

    def mergedPC[L: Lattice](c: ScEvalM[L])(context: Context): (L, Store, PC) = {
      import maf.lattice.MapLattice._
      val result = c.run(context)
      // optimisation: if the number of output states is one, then we don't need to merge anything
      if (result.size == 1) {
        val (context, v) = result.head
        (v, context.store, context.pc)
      } else {
        result.foldLeft[(L, Store, PC)]((Lattice[L].bottom, Lattice[Store].bottom, ScNil()))((acc, v) =>
          v match {
            case (context, l) =>
              (Lattice[L].join(acc._1, l), Lattice[Store].join(acc._2, context.store), acc._3.or(context.pc))
          }
        )
      }
    }

    def compute(c: ScEvalM[PostValue])(context: Context): (Value, Store, List[ScExp]) = {
      // TODO: this looks a lot like mergedPC, see if we can abstract this away a bit

      import maf.lattice.MapLattice._
      val result = c.run(context)

      // optimisation: if the number of output states is one, then we don't need to merge anything
      if (result.size == 1) {
        val (context, (v, s)) = result.head
        (v, context.store, List(s))
      } else {
        result.foldLeft[(Value, Store, List[ScExp])]((lattice.bottom, Lattice[Store].bottom, List()))((acc, v) =>
          v match {
            case (context, (l, s)) =>
              (lattice.join(acc._1, l), Lattice[Store].join(acc._2, context.store), s :: acc._3)
          }
        )
      }
    }

    /**
     * Given a computation that yields states that contain sets of values, this operator yields a single computation
     * that gives rises to a state for every element in the given set.
     */
    def options[X](c: ScEvalM[Set[X]]): ScEvalM[X] = ScEvalM((context) =>
      c.run(context).flatMap { case (updatedContext, set) =>
        set.map((updatedContext, _))
      }
    )

    def debug(c: => ()): ScEvalM[()] = unit.flatMap { _ =>
      c
      pure(())
    }

    /** Executes the given action simply for its side effects */
    def effectful(c: => ()): ScEvalM[()] = debug(c)

    def trace[X](m: String): (X => ScEvalM[X]) = { x =>
      println(s"trace $m $x")
      pure(x)
    }

    def trace[X]: (X => ScEvalM[X]) = { x =>
      println(("trace", x))
      pure(x)
    }

    /**
     * Action that prints the current store as a table
     * to the screen. Useful for debugging.
     */
    def printStore: ScEvalM[()] = withStoreCache { store =>
      import maf.util.StoreUtil._
      println(store.asTable.prettyString())
      unit
    }

    def evict(addresses: List[Addr]): ScEvalM[()] = ScEvalM { context =>
      Set((context.copy(cache = context.cache.removedAll(addresses)), ()))
    }

    def mergeStores(calleeStore: Store): ScEvalM[()] =
      sequence(calleeStore.view.map { case (addr, v) =>
        joinInCache(addr, value(v))
      }.toList).flatMap(_ => unit)

    def getStore: ScEvalM[Store] = ScEvalM { context =>
      Set((context, context.store))
    }

  }

  case class StoreCacheAdapter(cache: StoreCache, globalStore: maf.core.Store[Addr, Value]) extends maf.core.Store[Addr, Value] {
    def lookup(addr: Addr): Option[Value] =
      cache.get(addr).map((v: PostValue) => v._1).orElse(if (GLOBAL_STORE_ENABLED) globalStore.lookup(addr) else None)

    /** Add a new entry in the store */
    def extend(a: Addr, v: Value): maf.core.Store[Addr, Value] = {
      if (GLOBAL_STORE_ENABLED) {
        val _ = globalStore.extend(a, v)
      }

      StoreCacheAdapter(cache + (a -> ((v, ScNil()))), globalStore)
    }
  }
}
