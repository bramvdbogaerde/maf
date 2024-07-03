package maf.deltaDebugging.treeDD

import maf.deltaDebugging.treeDD.transformations.Transformation
import maf.language.scheme.SchemeExp
import scala.collection.parallel.CollectionConverters._

import scala.annotation.tailrec

import scala.annotation.tailrec

abstract class ParallelSchemeReduce(originalTree: SchemeExp, onOracleHit: SchemeExp => Unit, transformations: List[Transformation])
    extends Reducer[SchemeExp](originalTree):
    var fixpoint = true

    protected def reduceSingle(tree: SchemeExp): SchemeExp =
        var reducedTree = tree
        for (lvl <- 0 to reducedTree.height)
            reducedTree = reduceLevelNodes(reducedTree, lvl)
        reducedTree

    private def reduceLevelNodes(
        tree: SchemeExp,
        lvl: Int,
      ): SchemeExp =
        val nodes = tree.levelNodes(lvl)
        var candidates: List[SchemeExp] = List()
        for (t <- transformations) {
            for (node <- nodes) {
                for (candidate <- t.transform(tree, node)) {
                    candidates = candidates.::(candidate)
                    if candidates.size == 16 then
                        candidates.par.find(invokeOracle(_)) match
                            case Some(c) =>
                                fixpoint = false
                                onOracleHit(c)
                                return reduceLevelNodes(c, lvl)
                            case _ =>
                                candidates = List()
                }
            }
        }

        candidates.find(invokeOracle(_)) match
            case Some(c) =>
                fixpoint = false
                onOracleHit(c)
                reduceLevelNodes(c, lvl)
            case _ => tree
