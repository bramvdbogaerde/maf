package maf.modular.contracts.analyses

import maf.core.Identity
import maf.language.contracts.{ScExp, ScProgram}

import maf.modular.contracts.semantics._

trait ScAnalysisWithPrelude extends ScModSemanticsScheme {
  import maf.language.contracts.ScPrelude._
  override def program: ScExp = {
    val prg = super.program
    prg match {
      case ScProgram(expressions, idn) => ScProgram(prelude ++ expressions, idn)
      case e                           => ScProgram(prelude ++ List(e), Identity.none)
    }
  }
}
