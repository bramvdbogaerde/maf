package maf.test.modular.contracts

import maf.test.contracts.ScConcolicTesterTests
import maf.language.contracts.ScExp
import maf.modular.contracts.ConcolicTesting

class ConcolicTesterTestsJVM extends ScConcolicTesterTests {
  override def createAnalysis(exp: ScExp): ConcolicTesting = {
    new ConcolicTesting(exp) {
      def isSat(exp: ScExp): List[Val] = ???
    }
  }
}
