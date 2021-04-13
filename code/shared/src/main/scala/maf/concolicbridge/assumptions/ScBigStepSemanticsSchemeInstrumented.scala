package maf.concolicbridge.assumptions

import maf.concolicbridge.ScModSemanticsCollaborativeTesting

// TODO:
// 2. Implemented the semantics of inline tagged closures

/** Convience trait that combines all the assumptions together */
trait ScBigStepSemanticsSchemeInstrumented
    extends AnalysisWithAssumptions
       with ScModSemanticsCollaborativeTesting
       with PurityAssumption
       with NondetIf
       with ValueAssumption
       with RecursiveAssumption {

  override def intraAnalysis(component: Component): IntraAnalysisInstrumented
  trait IntraAnalysisInstrumented
      extends AnalysisWithAssumptionsIntra
         with PurityAssumptionIntra
         with NondetIfIntra
         with ValueAssumptionIntra
         with RecursiveAssumptionIntra
}
