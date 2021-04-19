package maf.util

import maf.core.Position
import maf.core.Identity

class PrettyPrinter {

  /** The indentation level */
  private var level: Int = 0

  /** THe current string builder for the pretty printer */
  private val builder: StringBuilder = new StringBuilder()

  /** Generate a new line on the output */
  def newline(): Unit = {
    builder.append('\n')
    (0 to level).foreach { _ =>
      newtab()
    }
  }

  /** Generate a tab on the output */
  def newtab(): Unit =
    builder.append("  ")

  /** Generates a new line and advances the indentation level */
  def newIndent(): Unit = {
    level += 1
    newline()
  }

  /** Exit the indentation level */
  def exitIndent(): Unit = {
    level -= 1
  }

  def print(s: String, position: Identity = Identity.none): Unit =
    builder.append(s)

  def render: String = builder.toString()

}
