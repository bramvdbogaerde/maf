package maf.test.modular.contracts

import maf.test.contracts.ScConcolicTesterTests
import maf.language.contracts.ScExp
import maf.concolic.contracts.ConcolicTesting
import maf.concolic.ConcolicTestingJVM

class ConcolicTesterTestsJVM extends ScConcolicTesterTests {
  override def createAnalysis(exp: ScExp): ConcolicTesting = {
    new ConcolicTestingJVM(exp)
  }
}
