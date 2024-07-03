package maf.deltaDebugging.treeDD
package variants

import maf.deltaDebugging.treeDD.transformations.Transformation
import maf.core.Expression
import maf.language.scheme.SchemeExp

import scala.annotation.tailrec

abstract class GTR(tree: SchemeExp, transformations: List[Transformation]) extends Reducer[SchemeExp](tree):
    protected def reduceSingle(tree: SchemeExp): SchemeExp =
        var reducedTree = tree
        for (lvl <- 0 to reducedTree.height)
            for (transformation <- transformations)
                reducedTree = reduceLevelNodes(reducedTree, lvl, transformation)
        reducedTree

    private def reduceLevelNodes(tree: SchemeExp, lvl: Int, transformation: Transformation): SchemeExp =
        for (node <- tree.levelNodes(lvl))
            for (candidateTree <- transformation.transform(tree, node))
                if candidateTree.size <= tree.size then
                    if invokeOracle(candidateTree) then return reduceLevelNodes(candidateTree, lvl, transformation)

        tree
