package maf.web.visualisations.softcontract

import maf.language.contracts._
import maf.modular.contracts.analyses._
import maf.modular.contracts.domain._
import maf.modular.contracts._

abstract class ScTestAnalysis(prg: ScExp) extends SimpleScSemantics(prg) with ScCallInsensitivity with ScSchemeConstantPropagationDomain {}

class ScSMTSolverWeb extends ScSmtSolver {
  def isSat: Boolean = true
}

class ScTestAnalysisWeb(prog: ScExp) extends ScTestAnalysis(prog) {
  override val GLOBAL_STORE_ENABLED: Boolean = false
  override type SMTSolver = ScSMTSolverWeb
  override def newSmtSolver(program: PC): ScSMTSolverWeb =
    new ScSMTSolverWeb()
}
