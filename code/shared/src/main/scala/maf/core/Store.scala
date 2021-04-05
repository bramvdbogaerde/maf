package maf.core

import maf.util.SmartHash

case class UnboundAddress[A <: Address](a: A) extends Error

trait Store[A <: Address, V] extends SmartHash {

  // Core operations.

  /** Looks up a value in the store */
  def lookup(a: A): Option[V]

  /** Add a new entry in the store */
  def extend(a: A, v: V): Store[A, V]

  // Derived operations.

  def lookupDefault(a: A, default: V): V = lookup(a) match {
    case Some(a) => a
    case None    => default
  }
  def lookupMF(a: A): MayFail[V, Error] = lookup(a) match {
    case Some(a) => MayFail.success(a)
    case None    => MayFail.failure(UnboundAddress(a))
  }

  // Allow strong updates if needed.

  /** Update an entry in the store */
  def update(a: A, v: V): Store[A, V] = extend(a, v)

  /** Tries to update an address if it's already mapped into the store. Otherwise, extend the store */
  def updateOrExtend(a: A, v: V): Store[A, V] = extend(a, v)
}

/* A store based on a map */
case class StoreMap[A <: Address, V](map: Map[A, V]) extends Store[A, V] {

  /** Looks up a value in the store */
  def lookup(a: A): Option[V] =
    map.get(a)

  /** Add a new entry in the store */
  def extend(a: A, v: V): Store[A, V] =
    StoreMap(map + (a -> v))

}
