package maf.language.CScheme

import maf.core.Identifier
import maf.language.scheme._
import maf.language.sexp._

import scala.util.control.TailCalls

object CSchemeCompiler extends BaseSchemeCompiler {
  import scala.util.control.TailCalls._

  override def reserved: List[String] = List("fork", "join", "<change>") ::: super.reserved

  override def _compile(exp: SExp): TailCalls.TailRec[SchemeExp] = exp match {
    case SExpPair(SExpId(Identifier("fork", _)), SExpPair(expr, SExpValue(ValueNil, _), _), _) =>
      tailcall(this._compile(expr)).map(CSchemeFork(_, exp.idn))
    case SExpPair(SExpId(Identifier("fork", _)), _, _) =>
      throw new Exception(s"Invalid CScheme fork: $exp (${exp.idn}).")
    case SExpPair(SExpId(Identifier("join", _)), SExpPair(expr, SExpValue(ValueNil, _), _), _) =>
      tailcall(this._compile(expr)).map(CSchemeJoin(_, exp.idn))
    case SExpPair(SExpId(Identifier("join", _)), _, _) =>
      throw new Exception(s"Invalid CScheme join: $exp (${exp.idn}).")

    case SExpPair(SExpId(Identifier("<change>", _)), SExpPair(old, SExpPair(nw, SExpValue(ValueNil, _), _), _), _) =>
      for {
        oldv <- tailcall(this._compile(old))
        newv <- tailcall(this._compile(nw))
      } yield SchemeCodeChange(oldv, newv, exp.idn)
    case SExpPair(SExpId(Identifier("<change>", _)), _, _) =>
      throw new Exception(s"Invalid code change: $exp (${exp.idn}).")

    case _ => super._compile(exp)
  }
}
