package maf.modular.contracts.analyses

import maf.modular.contracts.semantics._
trait ScGlobalStoreAnalysis extends ScModSemanticsScheme {
  override val GLOBAL_STORE_ENABLED: Boolean = true
}
