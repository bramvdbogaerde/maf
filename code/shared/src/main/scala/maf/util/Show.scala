package maf.util

import maf.core._

trait Show[V] extends Serializable {
  def show(v: V): String
}

object Show {
  def apply[V: Show]: Show[V] = implicitly
}

trait StoreShow[V, A <: Address] {
  def show(v: V, store: Store[A, V]): String
}

object StoreShow {
  def apply[V, A <: Address](implicit e: StoreShow[V, A]): StoreShow[V, A] = e
  def fromShow[V: Show, A <: Address]: StoreShow[V, A] = (v: V, _) => Show[V].show(v)
}
