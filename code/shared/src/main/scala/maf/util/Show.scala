package maf.util

import maf.core._

trait Show[V] extends Serializable {
  def show(v: V): String
}

object Show {
  def apply[V: Show]: Show[V] = implicitly

  implicit val stringShow: Show[String] = new Show[String] {
    def show(s: String): String = s""""$s""""
  }
  implicit val boolShow: Show[Boolean] = new Show[Boolean] {
    def show(b: Boolean): String =
      if (b) {
        "#t"
      } else {
        "#f"
      }
  }
  implicit val intShow: Show[BigInt] = new Show[BigInt] {
    def show(i: BigInt): String = s"$i"
  }
  implicit val doubleShow: Show[Double] = new Show[Double] {
    def show(d: Double): String = s"$d"
  }
  implicit val charShow: Show[Char] = new Show[Char] {
    def show(c: Char): String = s"#\\$c"
  }
  // Not implicit because it would conflict with stringShow.
  val symShow: Show[String] = new Show[String] {
    def show(s: String): String = s"'$s"
  }
}

trait StoreShow[V, A <: Address] {
  def show(v: V, store: Store[A, V]): String
}

object StoreShow {
  def apply[V, A <: Address](implicit e: StoreShow[V, A]): StoreShow[V, A] = e
  def fromShow[V: Show, A <: Address]: StoreShow[V, A] = (v: V, _) => Show[V].show(v)
}
