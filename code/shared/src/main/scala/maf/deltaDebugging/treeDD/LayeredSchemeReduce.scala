package maf.deltaDebugging.treeDD

import maf.deltaDebugging.treeDD.transformations.Transformation
import maf.language.scheme.SchemeExp

// TODO: this overrides `reduce` which should really be a final
// method. Doing so breaks instrumentation from TimedReducer and IntermediateReducer
abstract class LayeredSchemeReduce(
    originalTree: SchemeExp,
    onOracleHit: SchemeExp => Unit,
    transformations: List[Transformation],
    layerSize: Int,
    deadCodeRemover: Option[SchemeExp => Option[SchemeExp]] = None)
    extends Reducer[SchemeExp](originalTree):

    override protected def reduceSingle(currentTree: SchemeExp): SchemeExp =
        throw new Exception("will never be called")

    override def reduce(): SchemeExp =
        var reduced = originalTree
        var subset: List[Transformation] = List()
        while subset.size != transformations.size do
            val reducer = new SchemeReduce(reduced, onOracleHit, subset, deadCodeRemover) with LambdaOracle(invokeOracle)
            subset = transformations.take(subset.size + layerSize)
            reduced = reducer.reduce()
        reduced
