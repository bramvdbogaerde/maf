package maf.web

import maf.core.Expression
import maf.modular.DependencyTracking
import maf.modular.incremental.IncrementalModAnalysis

class WebVisualisationIncrementalAnalysis[Expr <: Expression](override val analysis: IncrementalModAnalysis[Expr] with DependencyTracking[Expr]) extends WebVisualisation(analysis) {

}
