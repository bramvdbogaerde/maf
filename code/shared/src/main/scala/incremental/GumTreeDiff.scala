package incremental

import scalaam.core.{Expression, Identifier}
import scalaam.language.scheme._

import scala.collection.mutable
import scala.util.control.Breaks._

/**
 * This file contains the implementations of the Gumtree code differences as presented in <br><br>
 *    Jean-Rémy Falleri, Floréal Morandat, Xavier Blanc, Matias Martinez, Martin Monperrus:<br>
 *    Fine-grained and accurate source code differencing. ASE 2014: 313-324.
 */
object GumTreeDiff {

  type E  = Expression
  type T  = TreeNode
  type MP = Map[T, T] // Mapping (parent1, node1) -> (parent2, node2)

  case class TreeNode(self: E)(parent: E) { // Parent is excluded from equals (== and !=).
    val height: Int = self.height
  }

  def topDown(T1: E, T2: E, minHeight: Int = 3): MP = {
    var L1 = new mutable.PriorityQueue[T]()(Ordering.by(_.height))
    var L2 = new mutable.PriorityQueue[T]()(Ordering.by(_.height))
    L1 += TreeNode(T1)(null)
    L2 += TreeNode(T2)(null)

    var A: Set[(T, T)] = Set() // List of candidate mappings. ((parent1, node1), (parent2, node2))
    var M: MP = Map()

    val subs1 = s(TreeNode(T1)(null))
    val subs2 = s(TreeNode(T2)(null))
    breakable {
      while (true) {
        val n1 = L1.headOption.getOrElse(break())
        val n2 = L2.headOption.getOrElse(break())
        if (n1.height.min(n2.height) <= minHeight) break()

        if (n1.height > n2.height)
          L1.dequeueAll.foreach(n => L1 ++= open(n))
        else if (n2.height > n1.height)
          L2.dequeueAll.foreach(n => L2 ++= open(n))
        else {
          val height = n1.height
          val H1 = L1.takeWhile(_.height == height).toList
          val H2 = L2.takeWhile(_.height == height).toList
          L1 = L1.drop(H1.length)
          L2 = L2.drop(H2.length)
          for (t1 <- H1) {
            val s1 = s(t1)
            for (t2 <- H2) {
              if (isomorphic(t1, t2)) {
                if (subs2.exists(tx => isomorphic(t1, tx) && tx != t2) || subs1.exists(tx => isomorphic(tx, t2) && tx != t1))
                  A = A + ((t1, t2))
                else {
                  val s2 = s(t2)
                  s1.zip(s2).foreach(t => M = M + t) // TODO is this correct?
                }
              }
            }
          }
          val AM = A ++ M.toSet
          for (t1 <- H1)
            if (!AM.exists(_._1 == t1)) L1 ++= open(t1)
          for (t2 <- H2)
            if (!AM.exists(_._2 == t2)) L2 ++= open(t2)
        }
      }
    }
    var Asorted = A.toList.sortBy({case (t1, t2) => dice(t1, t2, M)})
    while (Asorted.nonEmpty) {
      val (t1, t2) = Asorted.head
      Asorted = Asorted.tail
      s(t1).zip(s(t2)).foreach(t => M = M + t) // TODO is this correct?
      A.filterNot({case (x, y) => x == t1 || y == t2})
    }
    M
  }

  /*
  def bottomUp(T1: E, T2: E, m: MP, maxSize: Int, minDice: Double): MP = {
    var M: MP = m
    val Q = new mutable.PriorityQueue[(E, E)]()(Ordering.by(_._2.height * -1)) // Reverse the order.
    Q ++= s(T1).filter(t => M.get(t).isEmpty && open(t._2).map((t._2, _)).flatMap(M.get(_)).nonEmpty)
    while (Q.nonEmpty) {
      val t1 = Q.dequeue()
    }
  } */

  def open(n: T): List[T] = open(n.self).map(TreeNode(_)(n.self))

  def open(e: E): List[E] = e match {
    case                             _: Identifier => List()
    case              SchemeLambda(args, body,  _) => args ::: body
    case                SchemeFuncall(f, args,  _) => f :: args
    case              SchemeIf(cond, cons, alt, _) => List(cond, cons, alt)
    case              SchemeLet(bindings, body, _) =>         bindings.foldLeft(List[E]())((a, b) => b._2:: b._1 :: a) ::: body
    case          SchemeLetStar(bindings, body, _) =>         bindings.foldLeft(List[E]())((a, b) => b._2:: b._1 :: a) ::: body
    case           SchemeLetrec(bindings, body, _) =>         bindings.foldLeft(List[E]())((a, b) => b._2:: b._1 :: a) ::: body
    case   SchemeNamedLet(name, bindings, body, _) => name :: bindings.foldLeft(List[E]())((a, b) => b._2:: b._1 :: a) ::: body
    case             SchemeSet(variable, value, _) => List(variable, value)
    case       SchemeSetLex(variable, _, value, _) => List(variable, value)
    case                      SchemeBegin(exps, _) => exps
    case                        SchemeAnd(exps, _) => exps
    case                         SchemeOr(exps, _) => exps
    case      SchemeDefineVariable(name, value, _) => List(name, value)
    case SchemeDefineFunction(name, args, body, _) => name :: args ::: body
    case                          SchemeVar(id   ) => List(id)
    case                       SchemeVarLex(id, _) => List(id)
    case      _: SchemeQuoted | _: SchemeValue     => List()
    case                                        _  => throw new Exception("Unknown expression type.")
  }

  def isoRec(e1: SchemeExp, e2: SchemeExp): Boolean = {
    val o1 = open(e1)
    val o2 = open(e2)
    if (o1.length != o2.length) return false
    o1.zip(o2).forall(t => isomorphic(t._1, t._2))
  }

  def isomorphic(t1: T, t2: T): Boolean = isomorphic(t1.self, t2.self)

  // TODO: use another isoMorphic comparison method (paper: O(1) ?)
  // TODO: can this function be derived from s?
  def isomorphic(e1: E, e2: E): Boolean = (e1, e2) match {
    case (x:         SchemeLambda, y:         SchemeLambda) => isoRec(x, y)
    case (x:        SchemeFuncall, y:        SchemeFuncall) => isoRec(x, y)
    case (x:             SchemeIf, y:             SchemeIf) => isoRec(x, y)
    case (x:            SchemeLet, y:            SchemeLet) => isoRec(x, y)
    case (x:        SchemeLetStar, y:        SchemeLetStar) => isoRec(x, y)
    case (x:         SchemeLetrec, y:         SchemeLetrec) => isoRec(x, y)
    case (x:       SchemeNamedLet, y:       SchemeNamedLet) => isoRec(x, y)
    case (x:            SchemeSet, y:            SchemeSet) => isoRec(x, y)
    case (x:         SchemeSetLex, y:         SchemeSetLex) => isoRec(x, y)
    case (x:          SchemeBegin, y:          SchemeBegin) => isoRec(x, y)
    case (x:            SchemeAnd, y:            SchemeAnd) => isoRec(x, y)
    case (x:             SchemeOr, y:             SchemeOr) => isoRec(x, y)
    case (x: SchemeDefineVariable, y: SchemeDefineVariable) => isoRec(x, y)
    case (x: SchemeDefineFunction, y: SchemeDefineFunction) => isoRec(x, y)
    case (x:            SchemeVar, y:            SchemeVar) => isoRec(x, y)
    case (x:         SchemeVarLex, y:         SchemeVarLex) => isoRec(x, y)
    case (x:         SchemeQuoted, y:         SchemeQuoted) => isoRec(x, y)
    case (x:          SchemeValue, y:          SchemeValue) => true // x.value == y.value
    case (x:           Identifier, y:           Identifier) => true // x.name  == y.name
    case  _                                                 => false
  }

  // All subexpressions as (parent, subtree)
  def s(n: T): List[T] = {
    var   todo: Set[T] = Set(n)
    var   done: Set[T] = Set( )
    var result: Set[T] = Set( )
    while (todo.nonEmpty) {
      done = done ++ todo
      val nw: Set[T] = todo.flatMap(open)
      result = result ++ nw
      todo = todo ++ (nw -- done)
    }
    result.toList
  }

  def dice(t1: T, t2: T, M: MP): Double = {
    val s1 = s(t1)
    2.0 * s1.count(M.contains).toDouble / (s1.size + s(t2).size).toDouble
  }
}