package maf.deltaDebugging.treeDD

import maf.deltaDebugging.treeDD.transformations.Transformation
import maf.language.scheme.SchemeExp
import maf.core.Expression

import scala.annotation.tailrec

abstract class SchemeReduce(
    tree: SchemeExp,
    onOracleHit: SchemeExp => Unit,
    transformations: List[Transformation],
    deadCodeRemover: Option[SchemeExp => Option[SchemeExp]] = None)
    extends Reducer[SchemeExp](tree):

    protected def reduceSingle(
        tree: SchemeExp,
      ): SchemeExp =
        var reducedTree = tree
        for (lvl <- 0 to reducedTree.height)
            for (transformation <- transformations)
                reducedTree = reduceLevelNodes(reducedTree, lvl, transformation)
        reducedTree

    private def reduceLevelNodes(
        tree: SchemeExp,
        lvl: Int,
        transformation: Transformation,
      ): SchemeExp =
        for (node <- tree.levelNodes(lvl))
            for (candidateTree <- transformation.transform(tree, node))
                if candidateTree.size <= tree.size then
                    transformation.invoke()
                    if invokeOracle(candidateTree) then
                        onOracleHit(candidateTree)
                        transformation.hit()
                        deadCodeRemover match
                            case Some(remover) =>
                                val maybeRemoved = remover(candidateTree)
                                maybeRemoved match
                                    case Some(removed) =>
                                        return reduceLevelNodes(candidateTree, lvl, transformation)
                                    case _ => return reduceLevelNodes(candidateTree, lvl, transformation)
                            case _ => return reduceLevelNodes(candidateTree, lvl, transformation)
        tree
