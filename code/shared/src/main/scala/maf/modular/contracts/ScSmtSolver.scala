package maf.modular.contracts

object ScSMTSolver {
  sealed trait Result[+V]
  case class Satisfiable[+V](model: Map[String, V]) extends Result[V]
  case object Unknown extends Result[Nothing]
  case object Unsatisfiable extends Result[Nothing]
}

trait ScSmtSolver {
  def isSat: Boolean
}
