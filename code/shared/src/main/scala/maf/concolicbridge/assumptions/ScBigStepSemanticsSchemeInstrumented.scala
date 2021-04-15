package maf.concolicbridge.assumptions

import maf.concolicbridge.ScModSemanticsCollaborativeTesting

/** Convience trait that combines all the assumptions together */
trait ScBigStepSemanticsSchemeInstrumented
    extends AnalysisWithAssumptions
       with ScModSemanticsCollaborativeTesting
       with PurityAssumption
       with NondetIf
       with ValueAssumption
       with RecursiveAssumption
       with HoldsAssumptionAnalysis
       with NonBlameAssumption {

  override def intraAnalysis(component: Component): IntraAnalysisInstrumented
  trait IntraAnalysisInstrumented
      extends AnalysisWithAssumptionsIntra
         with PurityAssumptionIntra
         with NondetIfIntra
         with ValueAssumptionIntra
         with RecursiveAssumptionIntra
         with HoldsAssumptionAnalysisIntra
         with NonBlameAssumptionIntra
}
