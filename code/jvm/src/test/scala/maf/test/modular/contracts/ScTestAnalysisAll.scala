package maf.test.modular.contracts

import maf.test.{ScTestsJVMGlobalStore, ScTestsJVMLocalStore}
import maf.modular.contracts.ScMain

class ScTestAnalysisGlobalStoreTest extends ScTestsJVMGlobalStore with ScBigStepSemanticsTest
class ScTestAnalysisLocalStoreTest extends ScTestsJVMLocalStore with ScBigStepSemanticsTest

class ScSmallTestSuite extends ScTestsJVMGlobalStore {}
