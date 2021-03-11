package maf.core

import maf.util.SmartHash

sealed trait Environment[A <: Address] extends SmartHash {
  type This <: Environment[A]

  /** Restrict the environment to only certain keys */
  def restrictTo(keys: Set[String]): This

  /** Looks up a value in the environment */
  def lookup(name: String): Option[A]

  /** Extend the environment */
  def extend(name: String, a: A): This
  def extend(values: Iterable[(String, A)]): This

  /** Mapping over the environment */
  def mapAddrs(f: A => A): This

  def size: Int
}

/** Mapping from variable name to addresses */
case class BasicEnvironment[A <: Address](content: Map[String, A]) extends Environment[A] {
  type This = BasicEnvironment[A]
  def restrictTo(keys: Set[String]): BasicEnvironment[A] = this.copy(content = content.view.filterKeys(keys).toMap)
  def lookup(name: String): Option[A] = content.get(name)
  def extend(name: String, a: A): BasicEnvironment[A] = this.copy(content = content + (name -> a))
  def extend(values: Iterable[(String, A)]): BasicEnvironment[A] = this.copy(content = content ++ values)
  def mapAddrs(f: A => A): BasicEnvironment[A] = this.copy(content.view.mapValues(f).toMap)
  def size: Int = content.size

  /** Better printing. */
  override def toString: String = s"ENV{${content.filter(_._2.printable).mkString(", ")}}"
}

case class WrappedEnv[A <: Address, D](
    env: Environment[A],
    depth: Int,
    data: D)
    extends Environment[A] {
  type This = WrappedEnv[A, D]
  def restrictTo(keys: Set[String]): WrappedEnv[A, D] = this.copy(env = env.restrictTo(keys))
  def lookup(name: String): Option[A] = env.lookup(name)
  def extend(name: String, a: A): WrappedEnv[A, D] = this.copy(env = env.extend(name, a))
  def extend(values: Iterable[(String, A)]): WrappedEnv[A, D] = this.copy(env = env.extend(values))
  def mapAddrs(f: A => A): WrappedEnv[A, D] = this.copy(env = env.mapAddrs(f))
  def size: Int = env.size
}

object Environment {
  def apply[A <: Address](bds: Iterable[(String, A)]): Environment[A] = BasicEnvironment(bds.toMap)
}
