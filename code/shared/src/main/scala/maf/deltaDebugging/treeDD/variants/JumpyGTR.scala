package maf.deltaDebugging.treeDD
package variants

import maf.deltaDebugging.treeDD.transformations.Transformation
import maf.core.Expression
import maf.language.scheme.SchemeExp

import scala.annotation.tailrec

abstract class JumpyGTR(originalTree: SchemeExp, transformations: List[Transformation]) extends Reducer(originalTree):
    protected def reduceSingle(tree: SchemeExp): SchemeExp =
        (0 to tree.height).foldLeft(tree)((reducedTree, lvl) =>
            transformations.foldLeft(reducedTree)((reducedTree, transformation) =>
                reduceLevelNodes(reducedTree, reducedTree.levelNodes(lvl), transformation)
            )
        )

    private def reduceLevelNodes(
        tree: SchemeExp,
        lvlNodes: List[SchemeExp],
        transformation: Transformation
      ): SchemeExp =
        for (node <- lvlNodes)
            for ((candidateTree, candidateIdx) <- transformation.transform(tree, node).zipWithIndex)
                if candidateTree.size <= tree.size then if invokeOracle(candidateTree) then return candidateTree
        tree
