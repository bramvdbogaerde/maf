package maf.deltaDebugging.treeDD

import maf.language.scheme.*
import maf.util.FunctionUtils
import maf.util.benchmarks.Timer

type Oracle[E] = E => Boolean

abstract class Reducer[E](originalTree: E):
    /** Reduce the given tree for a single step and return the reduced tree */
    protected def reduceSingle(currentTree: E): E

    protected def invokeOracle(e: E): Boolean

    protected def reduce(e: E): E =
        FunctionUtils.fix(e)(reduceSingle)

    /** Reduce the original Scheme expression according to the given oracle */
    def reduce(): E = reduce(originalTree)

/** Implements <code>invokeOracle</code> as an invocation of the given lambda */
trait LambdaOracle[E](oracle: Oracle[E]) extends Reducer[E]:
    override protected def invokeOracle(e: E): Boolean = oracle(e)

/**
 * Adds instrumentation to the reduction such that it keeps track of the number of oracle invocations, the time it takes to run them, and the time for
 * each iteration of the transformation to succeed.
 */
trait TimedReducer[E] extends Reducer[E]:
    /** List of execution times, in reverse order, of performing one successful transformation (includes search) */
    var singleEvolution: List[Long] = List()

    /** List of execution times, in reverse order, of execution the oracle */
    var oracleEvolution: List[Long] = List()

    abstract override def reduceSingle(currentTree: E): E =
        val (t, e) = Timer.time(super.reduceSingle(currentTree))
        singleEvolution = t :: singleEvolution
        e

    abstract override def invokeOracle(e: E): Boolean =
        val (t, b) = Timer.time(super.invokeOracle(e))
        oracleEvolution = t :: oracleEvolution
        b

/** Keep track of the intermediate Scheme expressions */
trait IntermediateReducer[E] extends Reducer[E]:
    var expressionEvolution: List[E] = List()

    abstract override def reduce(e: E): E =
        expressionEvolution = e :: expressionEvolution
        super.reduce(e)

    abstract override def reduceSingle(currentTree: E): E =
        val e = super.reduceSingle(currentTree)
        expressionEvolution = e :: expressionEvolution
        e
