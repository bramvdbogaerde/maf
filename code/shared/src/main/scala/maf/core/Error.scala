package maf.core

/** An error that is not thrown but rather used as an erroneous value. */
// TODO Perhaps rename to ErrorValue?
trait Error extends Serializable
//case class ArityError[C](call: C, expected: Int, got: Int)                extends Error
//case class NotSupported(message: String)                                  extends Error
case class OperatorNotApplicable[V](operator: String, arguments: List[V]) extends Error
case class TypeError[V](message: String, on: V) extends Error
case class InvalidRelease[V](message: String, on: V) extends Error

/** An error that is thrown as an exception. */
trait MAFException extends Throwable
