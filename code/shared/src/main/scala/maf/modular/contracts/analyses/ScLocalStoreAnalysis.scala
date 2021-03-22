package maf.modular.contracts.analyses

import maf.modular.contracts.semantics.ScModSemanticsScheme

trait ScLocalStoreAnalysis extends ScModSemanticsScheme {
  override val GLOBAL_STORE_ENABLED = false
}
