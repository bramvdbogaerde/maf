package maf.modular.contracts

import maf.modular.contracts.analyses.SimpleScSemantics
import maf.language.contracts.ScExp

/**
 * Soft contract verification that use an SMT solver (Z3) which
 * only runs on the JVM.
 */
trait ScJVMAnalysis extends SimpleScSemantics {
  type SMTSolver = ScSMTSolverJVM[Nothing]

  def newSmtSolver(program: ScExp): ScSMTSolverJVM[Nothing] =
    new ScSMTSolverJVM(program, primitivesMap)
}
