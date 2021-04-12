package maf.concolicbridge.assumptions

import maf.concolicbridge.ScModSemanticsCollaborativeTesting

// TODO:
// 1. find a way to tag values, check if the redirection with Addr is actually necessary because we have pointer values in the scheme domain
// 2. Implemented the semantics of inline tagged closures
// 3. Implemented the semantics of the "value" assumption, which does not evaluate the given expression but instead "just" returns the given value

/** Convience trait that combines all the assumptions together */
trait ScBigStepSemanticsSchemeInstrumented extends AnalysisWithAssumptions with ScModSemanticsCollaborativeTesting with PurityAssumption {
  override def intraAnalysis(component: Component): IntraAnalysisInstrumented
  trait IntraAnalysisInstrumented extends AnalysisWithAssumptionsIntra with PurityAssumptionIntra
}
