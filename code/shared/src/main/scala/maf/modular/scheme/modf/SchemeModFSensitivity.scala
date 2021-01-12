package maf.modular.scheme.modf

import maf.core.Position._

// TODO: make allocCtx an abstract method of this trait
trait SchemeModFSensitivity extends BaseSchemeModFSemantics

/* Simplest (and most imprecise): no context-sensitivity */
case object NoContext extends Serializable {
  override def toString: String = "ε" // Mostly for the web visualisation that otherwise prints "undefined".
}

trait SchemeModFNoSensitivity extends SchemeModFSensitivity {
  type ComponentContext = NoContext.type
  def allocCtx(
      nam: Option[String],
      clo: lattice.Closure,
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext = NoContext
}

/* Full argument sensitivity for ModF */
case class ArgContext(values: List[_]) { //TODO: preserve type information
  override def toString: String = values.mkString(",")
}
trait SchemeModFFullArgumentSensitivity extends SchemeModFSensitivity {
  type ComponentContext = ArgContext
  def allocCtx(
      nam: Option[String],
      clo: lattice.Closure,
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext = ArgContext(args)
}

/* Call-site sensitivity for ModF */
case class CallSiteContext(calls: List[Position]) {
  override def toString: String = calls.mkString("[", ",", "]")
}
trait SchemeModFKCallSiteSensitivity extends SchemeModFSensitivity {
  val k: Int
  type ComponentContext = CallSiteContext
  def allocCtx(
      nam: Option[String],
      clo: lattice.Closure,
      args: List[Value],
      call: Position,
      caller: Component
    ) = context(caller) match {
    case None                           => CallSiteContext(List(call).take(k))
    case Some(CallSiteContext(callers)) => CallSiteContext((call :: callers).take(k))
  }
}
// shorthand for 1-CFA
trait SchemeModFCallSiteSensitivity extends SchemeModFKCallSiteSensitivity {
  override val k = 1
}

/* Call-site x full-argument sensitivity for ModF */
case class ArgCallSiteContext(
    fn: Position,
    call: Position,
    args: List[_]) { //TODO: type information about Value is lost!
  override def toString: String = {
    val argsstr = args.mkString(",")
    s"$call->$fn $argsstr"
  }
}
trait SchemeModFFullArgumentCallSiteSensitivity extends SchemeModFSensitivity {
  type ComponentContext = ArgCallSiteContext
  def allocCtx(
      nam: Option[String],
      clo: lattice.Closure,
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext =
    ArgCallSiteContext(clo._1.idn.pos, call, args)
}

trait SchemeModFUserGuidedSensitivity1 extends SchemeModFSensitivity {
  type ComponentContext = Any
  def allocCtx(
      nam: Option[String],
      clo: lattice.Closure,
      args: List[Value],
      call: Position,
      caller: Component
    ): ComponentContext =
    clo._1.annotation match {
      case None =>
        // println(s"WARNING: Function has no annotation: $nam ($clo), using FA")
        ("No", ())
      case Some(("@sensitivity", "1CS")) =>
        ("1CS", call)
      case Some(("@sensitivity", "2CS")) =>
        context(caller) match {
          case Some(("1CS", call2: Position)) =>
            ("2CS", call :: call2 :: Nil)
          case Some(("2CS", calls: List[Position])) =>
            ("2CS", (call :: calls).take(2))
          case _ =>
            ("2CS", call :: Nil)
        }
      case Some(("@sensitivity", "FA")) =>
        ("FA", args)
      case Some(("@sensitivity", "1A")) =>
        ("1A", args.take(1))
      case Some(("@sensitivity", "2A")) =>
        ("2A", args.drop(1).take(1))
      case Some(("@sensitivity", "No")) =>
        ("No", ())
      case annot =>
        println(s"WARNING: Function has an invalid annotation: $nam ($clo), using no sensitivity instead of: $annot")
        ("No", ())

    }
}

// TODO: do not use inner class definition
// TODO: find a way to reuse previous sensitivities?
object SchemeModFCompoundSensitivities {
  import maf.language.scheme.primitives.SchemePrelude

  trait Sensitivity[Value, Component] {
    trait Context
    def alloc(
        target: Position,
        args: List[Value],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context
  }

  class NoSensitivity[V, Component] extends Sensitivity[V, Component] {
    object NoContext extends Context {
      override def toString = "NoCtx"
    }
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context = NoContext
  }

  class CallSiteSensitivity[V, Component] extends Sensitivity[V, Component] {
    case class CallSiteContext(callSite: Position) extends Context {
      override def toString = s"CSCtx($callSite)"
    }
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context = CallSiteContext(callSite)
  }

  class FullArgumentSensitivity[V, Component] extends Sensitivity[V, Component] {
    case class FullArgumentContext(args: List[V]) extends Context {
      override def toString = s"FACtx($args)"
    }
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context = FullArgumentContext(args)
  }

  class ProductSensitivity[V, Component](val sensitivity1: Sensitivity[V, Component], val sensitivity2: Sensitivity[V, Component])
      extends Sensitivity[V, Component] {
    case class ProductContext(p1: sensitivity1.Context, p2: sensitivity2.Context) extends Context
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context = {
      val (p1, p2) = callerCtx match {
        case Some(ProductContext(p1, p2)) => (Some(p1), Some(p2))
        case _                            => (None, None)
      }
      ProductContext(sensitivity1.alloc(target, args, callSite, p1), sensitivity2.alloc(target, args, callSite, p2))
    }
  }

  class kContextSensitivity[V, Component](val k: Int, val sensitivity: Sensitivity[V, Component]) extends Sensitivity[V, Component] {
    case class kContext(l: List[sensitivity.Context]) extends Context
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context =
      kContext((sensitivity.alloc(target, args, callSite, None /* inner sensitivity should not be context sensitive */ ) :: (callerCtx match {
        case Some(kContext(l2)) => l2
        case _                  => List()
      })).take(k))
  }

  // Acyclic k-CFA inspired by "JSAI: A Static Analysis Platform for JavaScript" (FSE'14)
  class kAcyclicCallSiteSensitivity[V, Component](val k: Int) extends Sensitivity[V, Component] {
    case class kContext(l: List[Position]) extends Context
    def alloc(
        target: Position,
        args: List[V],
        callSite: Position,
        callerCtx: Option[Context]
      ): Context =
      kContext(callerCtx match {
        case Some(kContext(l2)) =>
          if (l2.contains(callSite)) {
            l2.dropWhile(_ != callSite)
          } else {
            (callSite :: l2).take(k)
          }
        case _ => List(callSite)
      })
  }

  class kCallSitesSensitivity[V, Component](k: Int) extends kContextSensitivity(k, new CallSiteSensitivity[V, Component])
  class kFullArgumentSensitivity[V, Component](k: Int) extends kContextSensitivity(k, new FullArgumentSensitivity[V, Component])
  class kCSFASensitivity[V, Component](k: Int)
      extends kContextSensitivity(
        k,
        new ProductSensitivity[V, Component](new CallSiteSensitivity[V, Component], new FullArgumentSensitivity[V, Component])
      )

  trait CompoundSensitivity extends SchemeModFSemantics {
    val HighSensitivity: Sensitivity[Value, Component]
    val LowSensitivity: Sensitivity[Value, Component]
    val primPrecision: Set[String] = SchemePrelude.primNames

    trait ComponentContext

    def isPrimitive(nam: Option[String]): Boolean = nam match {
      case Some(n) if primPrecision.contains(n) => true
      case _                                    => false
    }
  }

  trait SeparateLowHighSensitivity extends CompoundSensitivity {
    case class High(ctx: HighSensitivity.Context) extends ComponentContext
    case class Low(ctx: LowSensitivity.Context) extends ComponentContext

    def allocCtx(
        nam: Option[String],
        clo: lattice.Closure,
        args: List[Value],
        call: Position,
        caller: Component
      ): ComponentContext =
      if (isPrimitive(nam)) {
        High(
          HighSensitivity.alloc(clo._1.idn.pos,
                                args,
                                call,
                                context(caller) match {
                                  case Some(High(ctx)) => Some(ctx)
                                  case _               => None
                                }
          )
        )
      } else {
        Low(
          LowSensitivity.alloc(clo._1.idn.pos,
                               args,
                               call,
                               context(caller) match {
                                 case Some(Low(ctx)) => Some(ctx)
                                 case _              => None
                               }
          )
        )
      }
  }

  object SeparateLowHighSensitivity {
    trait S_0_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new NoSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_CS_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new CallSiteSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2CS_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kCallSitesSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10CS_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kCallSitesSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_FA_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new FullArgumentSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2FA_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kFullArgumentSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10FA_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kFullArgumentSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_CSFA_0 extends SeparateLowHighSensitivity {
      val HighSensitivity =
        new ProductSensitivity[Value, Component](new CallSiteSensitivity[Value, Component], new FullArgumentSensitivity[Value, Component])
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2AcyclicCS_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kAcyclicCallSiteSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10AcyclicCS_0 extends SeparateLowHighSensitivity {
      val HighSensitivity = new kAcyclicCallSiteSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }

    object Sensitivity extends Enumeration {
      type Sensitivity = Value
      val S_0_0, S_CS_0, S_2CS_0, S_10CS_0, S_FA_0, S_2FA_0, S_10FA_0, S_CSFA_0, S_2AcyclicCS_0, S_10AcyclicCS_0 = Value
    }

  }

  trait TrackLowToHighSensitivity extends CompoundSensitivity {
    case class High(ctx: HighSensitivity.Context, userCall: Position) extends ComponentContext
    case class Low(ctx: LowSensitivity.Context) extends ComponentContext

    def allocCtx(
        nam: Option[String],
        clo: lattice.Closure,
        args: List[Value],
        call: Position,
        caller: Component
      ): ComponentContext =
      if (isPrimitive(nam)) {
        High(
          HighSensitivity.alloc(clo._1.idn.pos,
                                args,
                                call,
                                context(caller) match {
                                  case Some(High(ctx, _)) => Some(ctx)
                                  case _                  => None
                                }
          ),
          caller match {
            case Some(High(_, userCall)) => userCall
            case _                       => call
          }
        )
      } else {
        Low(
          LowSensitivity.alloc(clo._1.idn.pos,
                               args,
                               call,
                               context(caller) match {
                                 case Some(Low(ctx)) => Some(ctx)
                                 case _              => None
                               }
          )
        )
      }
  }

  object TrackLowToHighSensitivity {
    trait S_0_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new NoSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_CS_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new CallSiteSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2CS_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kCallSitesSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10CS_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kCallSitesSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_FA_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new FullArgumentSensitivity[Value, Component]
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2FA_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kFullArgumentSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10FA_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kFullArgumentSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_CSFA_0 extends TrackLowToHighSensitivity {
      val HighSensitivity =
        new ProductSensitivity[Value, Component](new CallSiteSensitivity[Value, Component], new FullArgumentSensitivity[Value, Component])
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_2AcyclicCS_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kAcyclicCallSiteSensitivity[Value, Component](2)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
    trait S_10AcyclicCS_0 extends TrackLowToHighSensitivity {
      val HighSensitivity = new kAcyclicCallSiteSensitivity[Value, Component](10)
      val LowSensitivity = new NoSensitivity[Value, Component]
    }
  }
}
