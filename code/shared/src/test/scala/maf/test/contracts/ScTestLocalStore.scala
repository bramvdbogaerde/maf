package maf.test.contracts

import maf.language.contracts.ScExp
import maf.test.{ScAnalysisTests, ScTests}
import maf.modular.contracts.analyses.ScLocalStoreAnalysis

trait ScTestLocalStore extends ScTests with ScAnalysisTests {
  trait ScTestAnalysisLocalStore extends ScTestAnalysis with ScLocalStoreAnalysis
  override def newAnalysis(program: ScExp): ScTestAnalysisLocalStore
}
