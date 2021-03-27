package maf.test.contracts

import maf.language.contracts.ScExp
import maf.test.{ScAnalysisTests, ScTests}
import maf.modular.contracts.analyses.ScGlobalStoreAnalysis

trait ScTestGlobalStore extends ScTests with ScAnalysisTests {
  trait ScTestAnalysisGlobalStore extends ScTestAnalysis with ScGlobalStoreAnalysis
  override def newAnalysis(program: ScExp): ScTestAnalysisGlobalStore
}
