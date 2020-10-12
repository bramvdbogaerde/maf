package maf.modular.incremental.scheme.modf

import maf.language.scheme.{SchemeCodeChange, SchemeExp}
import maf.modular.incremental.scheme.IncrementalSchemeSemantics
import maf.modular.scheme.modf._
import maf.language.change.CodeVersion._
import maf.modular.scheme.modf.EvalM._

trait IncrementalSchemeModFBigStepSemantics extends BigStepModFSemantics with IncrementalSchemeSemantics {
  trait IncrementalSchemeModFBigStepIntra extends BigStepModFIntra {
    override protected def eval(exp: SchemeExp): EvalM[Value] = exp match {
      case SchemeCodeChange(e, _, _) if version == Old =>
        registerComponent(e, component)
        eval(e) // TODO: shoudn't this also be a super call?
      case SchemeCodeChange(_, e, _) if version == New =>
        registerComponent(e, component)
        eval(e) // TODO: shoudn't this also be a super call?
      case _                                     =>
        registerComponent(exp, component)
        super.eval(exp)
    }
  }
}
