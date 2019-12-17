package scalaam.modular.scheme

import scalaam.core._
import scalaam.modular._
import scalaam.language.scheme._
import scalaam.language.sexp
import scalaam.util._
import scalaam.modular.ModAnalysis._

/**
 * Base definitions for a Scheme MODF analysis.
 */
trait SchemeModFSemanticBase extends ModAnalysis[SchemeExp]
                                with GlobalStore[SchemeExp]
                                with ReturnResult[SchemeExp] {

  //XXXXXXXXXXXXXXXXXXXX//
  // LEXICAL ADDRESSING //
  //XXXXXXXXXXXXXXXXXXXX//

  // Ensure that the program is translated to use lexical addresses first!
  override lazy val program: SchemeExp = {
    val originalProgram = super.program
    val initialBindings = primitives.allPrimitives.map(_.name).toSet
    SchemeLexicalAddresser.translateProgram(originalProgram, initialBindings)
  }

  // Local addresses are simply made out of lexical information.
  trait LocalAddr extends Address { def pos(): Position }
  case class VarAddr(id: Identifier)           extends LocalAddr { def printable = true;  def pos(): Position =  id.pos }
  case class PtrAddr[C](exp: Expression, c: C) extends LocalAddr { def printable = false; def pos(): Position = exp.pos }
  case class PrmAddr(nam: String)              extends LocalAddr { def printable = true;  def pos(): Position = Position.none }

  //XXXXXXXXXXXXXXXXX//
  // ABSTRACT VALUES //
  //XXXXXXXXXXXXXXXXX//

  // Abstract values come from a Scala-AM Scheme lattice (a type lattice).
  type Prim = SchemePrimitive[Value, Addr]
  implicit val lattice: SchemeLattice[Value, Addr, Prim, ComponentPointer]
  lazy val primitives = new SchemePrimitives[Value, Addr]

  // Set up initial environment and install the primitives in the global store.
  primitives.allPrimitives.foreach { p =>
    val addr = ComponentAddr(ref(initialComponent), PrmAddr(p.name))
    store += (addr -> lattice.primitive(p))
  }

  //XXXXXXXXXXXXXXXXXXXXXXXXX//
  // COMPONENTS AND CONTEXTS //
  //XXXXXXXXXXXXXXXXXXXXXXXXX//

  // In ModF, components are function calls in some context.

  // This abstract class is parameterised by the choice of two types of components:
  // * A MainComponent type representing the main function of the program.
  // * A CallComponent type representing function calls. CallComponents must have a parent pointer and lambda expression, contain a context and may contain a name.
  // The MainComponent should be unique and can hence be an object. CallComponents can be created using the `newCallComponent` function.
  type MainComponent <: Component
  type CallComponent <: Component
  val MainComponent: Component
  val initialComponent: Component
  def getParent(c: CallComponent): ComponentPointer
  def getLambda(c: CallComponent): SchemeLambdaExp
  def newCallComponent(clo: lattice.Closure, nam: Option[String], ctx: Context): CallComponent

  // This abstract class is also parameterized by the choice of Context and allocation strategy for Contexts.
  type Context
  def allocCtx(clo: lattice.Closure, args: List[Value]): Context

  //XXXXXXXXXXXXXXXXXXXXXXXXXX//
  // INTRA-COMPONENT ANALYSIS //
  //XXXXXXXXXXXXXXXXXXXXXXXXXX//

  // Extensions to the intraAnalysis.
  trait SchemeModFSemanticsIntra extends super.IntraAnalysis with GlobalStoreIntra with ReturnResultIntra {
    // variable lookup
    protected def lookupVariable(lex: LexicalRef): Value =
      readAddr(resolveAddr(lex))
    protected def setVariable(lex: LexicalRef, vlu: Value): Unit =
      writeAddr(resolveAddr(lex),vlu)
    protected def defineVariable(id: Identifier, vlu: Value): Unit =
      writeAddr(VarAddr(id),vlu)
    // resolve a lexical address to the corresponding address in the store
    private def resolveAddr(lex: LexicalRef): Addr = lex match {
      case LocalRef(identifier) =>
        ComponentAddr(ptr,VarAddr(identifier))
      case GlobalRef(identifier) =>
        ComponentAddr(ref(MainComponent),VarAddr(identifier))
      case PrimRef(name) =>
        ComponentAddr(ref(MainComponent),PrmAddr(name))
      case NonLocalRef(identifier,scp) =>
        val cmp = resolveParent(ptr,scp)
        ComponentAddr(cmp,VarAddr(identifier))
    }
    @scala.annotation.tailrec
    private def resolveParent(ptr: ComponentPointer, scp: Int): ComponentPointer =
      if (scp == 0) { ptr } else deref(ptr) match {
        // If the program has succesfully passed the lexical translation, the lookup should never fail!
        case MainComponent => throw new Exception("Incorrect lexical address: trying to resolve the parent of the MainComponent.")
        case cmp: CallComponent@unchecked => resolveParent(getParent(cmp), scp - 1)
      }
    // apply
    protected def applyFun(fexp: SchemeExp, fval: Value, args: List[(SchemeExp,Value)]): Value =
      if(args.forall(_._2 != lattice.bottom)) {
        val fromClosures = applyClosures(fval,args)
        val fromPrimitives = applyPrimitives(fexp,fval,args)
        lattice.join(fromClosures,fromPrimitives)
      } else {
        lattice.bottom
      }
    // TODO[minor]: use foldMap instead of foldLeft
    private def applyClosures(fun: Value, args: List[(SchemeExp,Value)]): Value = {
      val arity = args.length
      val closures = lattice.getClosures(fun)
      closures.foldLeft(lattice.bottom)((acc,clo) => lattice.join(acc, clo match {
        case (clo@(SchemeLambda(prs,_,_),_), nam) if prs.length == arity =>
          val argVals = args.map(_._2)
          val context = allocCtx(clo,argVals)
          val component = newCallComponent(clo,nam,context)
          bindArgs(component, prs, argVals)
          call(component)
        case (clo@(SchemeVarArgLambda(prs,vararg,_,_),_), nam) if prs.length < arity =>
          val (fixedArgs,varArgs) = args.splitAt(prs.length)
          val fixedArgVals = fixedArgs.map(_._2)
          val varArgVal = allocateList(varArgs)
          val context = allocCtx(clo, fixedArgVals :+ varArgVal)
          val component = newCallComponent(clo,nam,context)
          bindArgs(component,prs,fixedArgVals)
          bindArg(component,vararg,varArgVal)
          call(component)
        case _ => lattice.bottom
      }))
    }
    protected def allocateList(elms: List[(SchemeExp,Value)]): Value = elms match {
      case Nil                => lattice.nil
      case (exp,vlu) :: rest  => allocateCons(exp)(vlu,allocateList(rest))
    }
    protected def allocateCons(pairExp: SchemeExp)(car: Value, cdr: Value): Value = {
      val pair = lattice.cons(car,cdr)
      val addr = allocAddr(PtrAddr(pairExp,()))
      writeAddr(addr,pair)
      lattice.pointer(addr)
    }
    protected def append(appendExp: SchemeExp)(l1: (SchemeExp, Value), l2: (SchemeExp, Value)): Value = {
      val appendPrim = lattice.primitive(primitives.PrimitiveDefs.Append)
      applyFun(appendExp, appendPrim, List(l1,l2))
    }
    private def bindArg(component: Component, par: Identifier, arg: Value): Unit =
      writeAddr(VarAddr(par),arg,component)
    private def bindArgs(component: Component, pars: List[Identifier], args: List[Value]): Unit =
      pars.zip(args).foreach { case (par,arg) => bindArg(component,par,arg) }

    private val allocator: SchemeAllocator[Addr] = new SchemeAllocator[Addr] {
      def pointer[C](exp: SchemeExp, c: C): Addr = allocAddr(PtrAddr(exp,c))
    }
    // TODO[minor]: use foldMap instead of foldLeft
    private def applyPrimitives(fexp: SchemeExp, fval: Value, args: List[(SchemeExp,Value)]): Value =
      lattice.getPrimitives(fval).foldLeft(lattice.bottom)((acc,prm) => lattice.join(acc,
        prm.call(fexp, args, StoreAdapter, allocator) match {
          case MayFailSuccess((vlu,_))  => vlu
          case MayFailBoth((vlu,_),_)   => vlu
          case MayFailError(_)          => lattice.bottom
        }))
    // primitives glue code
    // TODO[maybe]: while this should be sound, it might be more precise to not immediately write every value update to the global store ...
    case object StoreAdapter extends Store[Addr,Value] {
      def lookup(a: Addr): Option[Value] = Some(readAddr(a))
      def extend(a: Addr, v: Value): Store[Addr, Value] = { writeAddr(a,v) ; this }
      // all the other operations should not be used by the primitives ...
      def content                               = throw new Exception("Operation not allowed!")
      def keys                                  = throw new Exception("Operation not allowed!")
      def restrictTo(a: Set[Addr])              = throw new Exception("Operation not allowed!")
      def forall(p: ((Addr, Value)) => Boolean) = throw new Exception("Operation not allowed!")
      def join(that: Store[Addr, Value])        = throw new Exception("Operation not allowed!")
      def subsumes(that: Store[Addr, Value])    = throw new Exception("Operation not allowed!")
    }
    // evaluation helpers
    protected def evalLiteralValue(literal: sexp.Value): Value = literal match {
      case sexp.ValueInteger(n)   => lattice.number(n)
      case sexp.ValueReal(r)      => lattice.real(r)
      case sexp.ValueBoolean(b)   => lattice.bool(b)
      case sexp.ValueString(s)    => lattice.string(s)
      case sexp.ValueCharacter(c) => lattice.char(c)
      case sexp.ValueSymbol(s)    => lattice.symbol(s)
      case sexp.ValueNil          => lattice.nil
      case _ => throw new Exception(s"Unsupported Scheme literal: $literal")
    }
    // The current component serves as the lexical environment of the closure.
    protected def newClosure(lambda: SchemeLambdaExp, name: Option[String]): Value = lattice.closure((lambda, ptr), name)

    // other helpers
    protected def conditional[M : Monoid](prd: Value, csq: => M, alt: => M): M = {
      val csqVal = if (lattice.isTrue(prd)) csq else Monoid[M].zero
      val altVal = if (lattice.isFalse(prd)) alt else Monoid[M].zero
      Monoid[M].append(csqVal,altVal)
    }
  }
}

/** Standard semantics for a Scheme MODF analysis. */
trait SchemeModFSemantics extends ModAnalysis[SchemeExp]
                             with GlobalStore[SchemeExp]
                             with ReturnResult[SchemeExp]
                             with SchemeModFSemanticBase {
  trait Component
  case object MainComponent extends Component {
    override def toString: String = "main"
  }
  case class CallComponent(clo: lattice.Closure,
                           nam: Option[String],
                           ctx: Context) extends Component {
    val (lambda, parent) = clo
    override def toString: String = nam match {
      case None => s"anonymous@${lambda.pos} [${ctx.toString}]"
      case Some(name) => s"$name [${ctx.toString}]"
    }
  }
  lazy val initialComponent: Component = MainComponent
  def getParent(c: CallComponent): ComponentPointer = c.parent
  def getLambda(c: CallComponent): SchemeLambdaExp  = c.lambda
  def newCallComponent(clo: lattice.Closure, nam: Option[String], ctx: Context): CallComponent = CallComponent(clo, nam, ctx)
}

/** Semantics for an incremental Scheme MODF analysis. */
trait IncrementalSchemeModFSemantics extends IncrementalModAnalysis[SchemeExp]
                                        with GlobalStore[SchemeExp]
                                        with ReturnResult[SchemeExp]
                                        with SchemeModFSemanticBase {

  // Every component holds a pointer to the corresponding lexical module.
  trait Component extends LinkedComponent
  case object MainComponent extends Component {
    override def toString: String = "MAIN"
    val module: Module = SimplePosition(0, 0)
  }
  case class CallComponent(clo: lattice.Closure,
                           nam: Option[String],
                           ctx: Context) extends Component {
    val (lambda, parent) = clo
    override def toString: String = nam match {
      case None => s"λ@${lambda.pos} [${ctx.toString}]"
      case Some(name) => s"$name [${ctx.toString}]"
    }
    val module: Module = lambda.pos
  }
  override lazy val initialComponent: Component = MainComponent
}

/** Semantics for an adaptive Scheme MODF analysis. */
trait AdaptiveSchemeModFSemantics extends AdaptiveModAnalysis[SchemeExp]
                                     with AdaptiveGlobalStore[SchemeExp]
                                     with AdaptiveReturnResult[SchemeExp]
                                     with SchemeModFSemantics
