package maf.modular.scheme

import maf.core._
import maf.language.scheme._

/**
 * Addresses to be used with a Scheme analysis.
 * @tparam Context A type of Contexts that can be used to distinguish more addresses. The type context is covariant.
 */
trait SchemeAddr[+Context] extends Address
case class VarAddr[Context](id: Identifier, ctx: Context)   extends SchemeAddr[Context] { def printable = true;  def idn: Identity =  id.idn;       override def toString: String = s"var ($id)"        }
case class PtrAddr[Context](exp: SchemeExp, ctx: Context)   extends SchemeAddr[Context] { def printable = false; def idn: Identity =  exp.idn;      override def toString: String = s"ptr (${exp.idn})" }
case class PrmAddr(nam: String)                             extends SchemeAddr[Nothing] { def printable = false; def idn: Identity = Identity.none; override def toString: String = s"prm ($nam)"       }
