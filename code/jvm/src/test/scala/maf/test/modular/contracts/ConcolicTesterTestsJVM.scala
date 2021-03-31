package maf.test.modular.contracts

import maf.test.contracts.ScConcolicTesterTests
import maf.language.contracts.ScExp
import maf.modular.contracts.ConcolicTesting
import maf.modular.contracts.ScSMTSolverJVM
import maf.modular.contracts.analyses.SimpleScSemantics
import maf.modular.contracts.ScSMTSolver

class ConcolicTesterTestsJVM extends ScConcolicTesterTests {
  override def createAnalysis(exp: ScExp): ConcolicTesting = {
    new ConcolicTesting(exp) {
      def isSat(exp: ScExp): Option[Map[String, Val]] = {
        val solver = new ScSMTSolverJVM(exp, SimpleScSemantics.primitivesMap, (v) => Some(v))
        solver.isSatWithModel match {
          case ScSMTSolver.Satisfiable(model) =>
            Some(model)

          case ScSMTSolver.Unknown =>
            Some(Map())

          case ScSMTSolver.Unsatisfiable =>
            None
        }
      }
    }
  }
}
