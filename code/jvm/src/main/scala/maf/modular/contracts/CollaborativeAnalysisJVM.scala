package maf.modular.contracts

import maf.concolicbridge.ConcolicBridge
import maf.language.contracts.ScExp
import maf.modular.contracts.analyses.ScCallInsensitivity
import maf.modular.contracts.analyses.SimpleScSemantics
import maf.modular.contracts.domain.ScSchemeConstantPropagationDomain
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.concolic.contracts.ConcolicTesting
import maf.concolic.ConcolicTestingJVM

class ScTestAnalysis(prg: ScExp) extends SimpleScSemantics(prg) with ScCallInsensitivity with ScSchemeConstantPropagationDomain {

  type SMTSolver = ScSmtSolver
  override val GLOBAL_STORE_ENABLED: Boolean = true

  override def newSmtSolver(program: ScExp): SMTSolver =
    new ScSMTSolverJVM(program, primitivesMap)

}
class CollaborativeAnalysisJVM(exp: ScExp) extends ConcolicBridge(exp) {
  var currentAnalysis: Option[ScModSemanticsCollaborativeTesting] = None
  var currentTester: Option[ConcolicTesting] = None
  private def newAnalysis(program: ScExp): ScModSemanticsCollaborativeTesting =
    new ScTestAnalysis(program)

  override def modAnalysis(exp: ScExp): ScModSemanticsCollaborativeTesting = {
    currentAnalysis = Some(newAnalysis(exp))
    currentAnalysis.get
  }

  override def concolicTester(exp: ScExp): ConcolicTesting = {
    currentTester = Some(new ConcolicTestingJVM(exp))
    currentTester.get
  }
}
