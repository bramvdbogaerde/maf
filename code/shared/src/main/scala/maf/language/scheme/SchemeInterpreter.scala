package maf.language.scheme

import java.util.concurrent.TimeUnit

import maf.core.Position.Position
import maf.core._
import maf.language.CScheme._
import maf.language.change.CodeVersion._
import maf.util._
import maf.language.sexp._
import maf.util.benchmarks.Timeout

import scala.concurrent.TimeoutException
import scala.concurrent._
import ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration

case class ChildThreadDiedException(e: VirtualMachineError) extends Exception(s"A child thread has tragically died with ${e.getMessage}.")
case class UnexpectedValueTypeException[V](v: V) extends Exception(s"The interpreter encountered an unexpected value during its execution: $v.")

/**
  * This is an interpreter that runs a program and calls a callback at every evaluated value.
  * This interpreter dictates the concrete semantics of the Scheme language analyzed by MAF.
 */
class SchemeInterpreter(cb: (Identity, SchemeInterpreter.Value) => Unit, output: Boolean = true, stack: Boolean = false) {
  import SchemeInterpreter._
  /**
    * Evaluates `program`.
    * Will check the analysis result by calling `compare` on all encountered values.
    */
  def run(program: SchemeExp, timeout: Timeout.T, version: Version = New): Value = {
    setStore(initialSto)
    val res = eval(program, initialEnv, timeout, version)
    val resAddr = newAddr(AddrInfo.RetAddr(program))
    extendStore(resAddr, res)
    res
  }

  lazy val (initialEnv, initialSto) = {
    val emptyEnv = Map.empty[String,Addr]
    val emptySto = Map.empty[Addr, Value]
    Primitives.allPrimitives.foldLeft((emptyEnv, emptySto)) {
      case ((env: Env, sto: Store), prim: Prim) =>
        val addr = newAddr(AddrInfo.PrmAddr(prim.name))
        (env + (prim.name -> addr), sto + (addr -> Value.Primitive(prim)))
    }
  }

  def safeFuture(bdy: => Value): Future[Value] = Future {
    try {
      bdy
    } catch {
      case e: VirtualMachineError =>
        throw ChildThreadDiedException(e)
    }
  }

  // Access to cb should be syncrhonized on 'Callback'.
  object Callback {
    def call(i: Identity, v: Value): Unit = synchronized {
      cb(i, v)
    }
  }

  var compared = 0
  def check(i: Identity, v : Value): Value = {
    compared += 1
    v match {
      case Value.Undefined(idn@_) => () // println(s"Undefined behavior arising from identity $idn seen at ${e.idn.pos}")
      case Value.Unbound(idn) => println(s"Seen unbound identifier $idn at ${i}")
      case _ => ()
    }
    Callback.call(i, v)
    v
  }

  // Both access to 'lastAddr' and 'store' should be synchronized on 'this'!
  var lastAddr = 0
  def newAddr(meta: AddrInfo): (Int, AddrInfo) = synchronized {
    lastAddr += 1
    (lastAddr, meta)
  }
  var store = Map[Addr, Value]()
  def extendStore(a: Addr, v: Value): Unit = synchronized {
    store = store + (a -> v)
  }
  def lookupStore(a: Addr): Value = synchronized {
    store(a)
  }
  def lookupStoreOption(a: Addr): Option[Value] = synchronized {
    store.get(a)
  }
  def setStore(s: Map[Addr, Value]): Unit = synchronized {
    store = s
  }

  // Access to the standard output stream should be synchronized on 'Out'.
  object Out {
    def prt(s: Value): Unit = synchronized {
      print(s)
    }
    def prtln(s: String): Unit = synchronized {
      println(s)
    }
  }

  // Keep an artificial call stack to ease debugging.
  var callStack: List[String] = List()
  def stackedCall(name: Option[String], idn: Identity, block: => Value): Value = {
    val n = name.getOrElse("λ") + s"@${idn.pos}"
    if (stack) callStack = n :: callStack
    val res = block
    if (stack) callStack = callStack.tail
    res
  }
  def stackedException[R](msg: String): R = {
    val m = if (stack) callStack.mkString(s"$msg\n Callstack:\n * ", "\n * ", "\n **********") else msg
    throw new Exception(m)
  }

  def eval(e: SchemeExp, env: Env, timeout: Timeout.T, version: Version): Value = {
    if (timeout.reached) throw new TimeoutException()
    e match {
      case lambda: SchemeLambdaExp => Value.Clo(lambda, env)
      case call@SchemeFuncall(f, args, idn) =>
        eval(f, env, timeout, version) match {
          case Value.Clo(lambda@SchemeLambda(argsNames, body, pos2), env2, name) =>
            if (argsNames.length != args.length) {
              stackedException(s"Invalid function call at position ${idn}: ${args.length} arguments given to function lambda (${lambda.idn.pos}), while exactly ${argsNames.length} are expected")
            }
            val envExt = argsNames.zip(args).foldLeft(env2)((env3, arg) => {
              val addr = newAddr(AddrInfo.VarAddr(arg._1))
              extendStore(addr, check(arg._1.idn, eval(arg._2, env, timeout, version)))
              (env3 + (arg._1.name -> addr))
            })
            val res = stackedCall(name, pos2, { eval(SchemeBegin(body, pos2), envExt, timeout, version) })
            val resAddr = newAddr(AddrInfo.RetAddr(SchemeBody(lambda.body)))
            extendStore(resAddr, res)
            res
          case Value.Clo(lambda@SchemeVarArgLambda(argsNames, vararg, body, pos2), env2, name) =>
            val arity = argsNames.length
            if (args.length < arity) {
              stackedException(s"Invalid function call at position $idn: ${args.length} arguments given, while at least ${argsNames.length} are expected")
            }
            val envExt = argsNames.zip(args).foldLeft(env2)((env3, arg) => {
              val addr = newAddr(AddrInfo.VarAddr(arg._1))
              extendStore(addr, check(arg._1.idn, eval(arg._2, env, timeout, version)))
              (env3 + (arg._1.name -> addr))
            })
            val varArgVals = args.drop(arity).map(e => (e, eval(e, env, timeout, version)))
            val varArgAddr = newAddr(AddrInfo.VarAddr(vararg))
            extendStore(varArgAddr, makeList(varArgVals))
            val envExt2 = envExt + (vararg.name -> varArgAddr)
            val res = stackedCall(name, pos2, { eval(SchemeBegin(body, pos2), envExt2, timeout, version) })
            val resAddr = newAddr(AddrInfo.RetAddr(SchemeBody(lambda.body)))
            extendStore(resAddr, res)
            res
          case Value.Primitive(p) => stackedCall(Some(p.name), Identity.none, { p.call(call, args.map(arg => (arg, eval(arg, env, timeout, version)))) })
          case v =>
            stackedException(s"Invalid function call at position ${idn}: ${v} is not a closure or a primitive")
        }
      case SchemeIf(cond, cons, alt, _) =>
        eval(cond, env, timeout, version) match {
          case Value.Bool(false) => eval(alt, env, timeout, version)
          case _ => eval(cons, env, timeout, version)
        }
      case SchemeLet(bindings, body, pos) =>
        val envExt = bindings.foldLeft(env)((env2, binding) => {
          val addr = newAddr(AddrInfo.VarAddr(binding._1))
          extendStore(addr, check(binding._1.idn, eval(binding._2, env, timeout, version)))
          (env2 + (binding._1.name -> addr))
        })
        eval(SchemeBegin(body, pos), envExt, timeout, version)
      case SchemeLetStar(bindings, body, pos) =>
        val envExt = bindings.foldLeft(env)((env2, binding) => {
          val addr = newAddr(AddrInfo.VarAddr(binding._1))
          extendStore(addr, check(binding._1.idn, eval(binding._2, env2, timeout, version)))
          (env2 + (binding._1.name -> addr))
        })
        eval(SchemeBegin(body, pos), envExt, timeout, version)
      case SchemeLetrec(bindings, body, pos) =>
        /* First extend the environment with all bindings set to unbound */
        val envExt = bindings.foldLeft(env)((env2, binding) => {
          val addr = newAddr(AddrInfo.VarAddr(binding._1))
          extendStore(addr, Value.Unbound(binding._1))
          val env3 = env2 + (binding._1.name -> addr)
          env3
        })
        /* Then evaluate all bindings in the extended environment */
        bindings.foreach(binding => {
          val value = eval(binding._2, envExt, timeout, version)
          val namedValue = value match {
            case Value.Clo(lambda, env, _) => Value.Clo(lambda, env, Some(binding._1.name)) // Add names to closures.
            case _ => value
          }
          extendStore(envExt(binding._1.name), check(binding._1.idn, namedValue))
        })
        eval(SchemeBegin(body, pos), envExt, timeout, version)
      case SchemeNamedLet(name, bindings, body, pos) =>
        val addr = newAddr(AddrInfo.VarAddr(name))
        val env2 = env + (name.name -> addr)
        val (prs,ags) = bindings.unzip
        val lambda = SchemeLambda(prs, body, pos)
        val clo = Value.Clo(lambda, env2, Some(name.name))
        extendStore(addr, clo)
        ags.foreach(argExp => (argExp, eval(argExp, env, timeout, version)))
        eval(SchemeFuncall(lambda, ags, pos), env2, timeout, version)
      case SchemeSet(id, v, pos) =>
        /* TODO: primitives can be reassigned with set! without being redefined */
        val addr = env.get(id.name) match {
          case Some(addr) => addr
          case None => stackedException(s"Unbound variable $id accessed at position $pos")
        }
        extendStore(addr, eval(v, env, timeout, version))
        Value.Void
      case SchemeBegin(exps, _) =>
        val init: Value = Value.Void
        exps.foldLeft(init)((_, e) => eval(e, env, timeout, version))
      case SchemeAnd(Nil, _) =>
        Value.Bool(true)
      case SchemeAnd(e :: Nil, _) =>
        eval(e, env, timeout, version)
      case SchemeAnd(e :: exps, pos) =>
        eval(e, env, timeout, version) match {
          case Value.Bool(false) => Value.Bool(false)
          case _ => eval(SchemeAnd(exps, pos), env, timeout, version)
        }
      case SchemeOr(Nil, _) =>
        Value.Bool(false)
      case SchemeOr(e :: exps, pos) =>
        eval(e, env, timeout, version) match {
          case Value.Bool(false) => eval(SchemeOr(exps, pos), env, timeout, version)
          case v => v
        }
      case SchemeAssert(_, _) =>
        Value.Void
      case SchemeDefineVariable(_, _, _) => ???
      case SchemeDefineFunction(_, _, _, _) => ???
      case SchemeDefineVarArgFunction(_, _, _, _, _) => ???
      case SchemeVar(id) =>
        env.get(id.name) match {
          case Some(addr) => lookupStoreOption(addr) match {
            case Some(v) => v
            case None => stackedException(s"Unbound variable $id at position ${id.idn}")
          }
          case None => stackedException(s"Undefined variable $id at position ${id.idn}")
        }
      case SchemePair(car,cdr,_) =>
        val carv = eval(car, env, timeout, version)
        val cdrv = eval(cdr, env, timeout, version)
        allocateCons(e,carv,cdrv)
      case SchemeSplicedPair(_,_,_) =>
        stackedException("NYI -- Unquote splicing")
        //val splicev = eval(splice,env,timeout)
        //val cdrv    = eval(cdr,env,timeout)
        //Primitives.Append.append(splicev,cdrv)
      case SchemeValue(v, _) =>
        v match {
          case ValueString(s)      => Value.Str(s)
          case ValueSymbol(s)      => Value.Symbol(s)
          case ValueInteger(n)     => Value.Integer(n)
          case ValueReal(r)        => Value.Real(r)
          case ValueBoolean(b)     => Value.Bool(b)
          case ValueCharacter(c)   => Value.Character(c)
          case ValueNil            => Value.Nil
        }
      case CSchemeFork(body, _)    => Value.Thread(safeFuture { eval(body, env, timeout, version) })
      case CSchemeJoin(tExp, _)    => eval(tExp, env, timeout, version) match {
        case Value.Thread(fut)     => Await.result(fut, timeout.timeLeft.map(Duration(_, TimeUnit.NANOSECONDS)).getOrElse(Duration.Inf))
        case v                     => stackedException(s"Join expected thread, but got $v")
      }
      case SchemeCodeChange(old, nw, _)  => if (version == Old) eval(old, env, timeout, version) else eval(nw, env, timeout, version)
    }
  }
  def allocateCons(exp: SchemeExp, car: Value, cdr: Value): Value = {
    val addr = newAddr(AddrInfo.PtrAddr(exp))
    val pair = Value.Cons(car,cdr)
    extendStore(addr, pair)
    Value.Pointer(addr)
  }

  def makeList(values: List[(SchemeExp,Value)]): Value = values match {
    case Nil                   => Value.Nil
    case (exp, value) :: rest  => allocateCons(exp, value, makeList(rest))
  }

  object Primitives {
    //def primitiveMap: Map[String, Prim] = allPrimitives.map(p => (p.name, p)).toMap
    def allPrimitives: List[Prim] = List(
      Times, /* [vv] *: Arithmetic */
      Plus, /* [vv] +: Arithmetic */
      Minus, /* [vv] -: Arithmetic */
      Div, /* [vx] /: Arithmetic (no support for fractions) */
      Abs, /* [vv] abs: Arithmetic */
      ACos, /* [vv] acos: Scientific */
      /* [x]  angle: Complex */
      //Append, /* [x]  append: Append/Reverse */
      /* [x]  apply: Fly Evaluation */
      ASin, /* [vv] asin: Scientific */
      //Assoc, /* [vv] assoc: Retrieving Alist Entries */
      //Assq, /* [vv] assq: Retrieving Alist Entries */
      /* [x]  assv: Retrieving Alist Entries */
      ATan, /* [vv] atan: Scientific */
      Booleanp, /* [vv] boolean?: Booleans */
      /* [x]  call-with-current-continuation: Continuations */
      /* [x]  call-with-input-file: File Ports */
      /* [x]  call-with-output-file: File Ports */
      /* [x]  call-with-values: Multiple Values */
      Car, /* [vv] car: Pairs */
      Cdr, /* [vv] cdr: Pairs */
      Ceiling, /* [vv] ceiling: Arithmetic */
      CharToInteger, /* [vv]  char->integer: Characters */
      /* [x]  char-alphabetic?: Characters */
      /* [x]  char-ci<=?: Characters */
      /* [x]  char-ci<?: Characters */
      /* [x]  char-ci=?: Characters */
      /* [x]  char-ci>=?: Characters */
      /* [x]  char-ci>?: Characters */
      /* [x]  char-downcase: Characters */
      /* [x]  char-lower-case?: Characters */
      /* [x]  char-numeric?: Characters */
      /* [x]  char-ready?: Reading */
      /* [x]  char-upcase: Characters */
      /* [x]  char-upper-case?: Characters */
      /* [x]  char-whitespace?: Characters */
      /* [x]  char<=?: Characters */
      /* [x]  char<?: Characters */
      /* [x]  char=?: Characters */
      /* [x]  char>=?: Characters */
      /* [x]  char>?: Characters */
      Charp, /* [vv] char?: Characters */
      /* [x]  close-input-port: Closing */
      /* [x]  close-output-port: Closing */
      /* [x]  complex?: Complex Numbers */
      Cons, /* [vv] cons: Pairs */
      Cos, /* [vv] cos: Scientific */
      /* [x]  current-input-port: Default Ports */
      /* [x]  current-output-port: Default Ports */
      Display, /* [v]  display: Writing */
      /* [x]  dynamic-wind: Dynamic Wind */
      /* [x]  eof-object?: Reading */
      Eq, /* [vv] eq?: Equality */
      //Equal, /* [vx] equal?: Equality */
      /* [x]  eqv?: Equality */
      /* [x]  eval: Fly Evaluation */
      Evenp, /* [vv] even?: Integer Operations */
      ExactToInexact, /* [vv] exact->inexact: Exactness */
      /* [x]  exact?: Exactness */
      /* [x]  exp: Scientific */
      Expt, /* [vv] expt: Scientific */
      Floor, /* [vv] floor: Arithmetic */
      /* [x]  for-each: List Mapping */
      /* [x]  force: Delayed Evaluation */
      Gcd, /* [vx] gcd: Integer Operations */
      /* [x]  imag-part: Complex */
      InexactToExact, /* [vv] inexact->exact: Exactness */
      /* [x]  inexact?: Exactness */
      /* [x]  input-port?: Ports */
      IntegerToChar, /* [vv]  integer->char: Characters */
      Integerp, /* [vv] integer?: Integers */
      /* [x]  interaction-environment: Fly Evaluation */
      /* [x]  lcm: Integer Operations */
      //Length, /* [vv] length: List Selection */
      ListPrim, /* [vv] list: List Constructors */
      /* [x]  list->string: String Constructors */
      /* [x]  list->vector: Vector Creation */
      //ListRef, /* [vv] list-ref: List Selection */
      /* [x]  list-tail: List Selection */
      //Listp, /* [vv] list?: List Predicates */
      /* [x]  load: Loading */
      Log, /* [vv] log: Scientific */
      /* [x]  magnitude: Complex */
      /* [x]  make-polar: Complex */
      /* [x]  make-rectangular: Complex */
      /* [x]  make-string: String Constructors */
      /* [x]  map: List Mapping */
      Max, /* [vv] max: Arithmetic */
      //Member, /* [vv] member: List Searching */
      //Memq, /* [v]  memq: List Searching */
      /* [x]  memv: List Searching */
      Min, /* [vv] min: Arithmetic */
      Modulo, /* [vv] modulo: Integer Operations */
      Negativep, /* [vv] negative?: Comparison */
      Newline, /* [v]  newline: Writing */
      Not, /* [vv] not: Booleans */
      Nullp, /* [vv] null?: List Predicates */
      NumberToString, /* [vx] number->string: Conversion: does not support two arguments */
      Numberp, /* [vv] number?: Numerical Tower */
      Oddp, /* [vv] odd?: Integer Operations */
      /* [x]  open-input-file: File Ports */
      /* [x]  open-output-file: File Ports */
      /* [x]  output-port?: Ports */
      Pairp, /* [vv] pair?: Pairs */
      /* [x]  peek-char?: Reading */
      Positivep, /* [vv] positive?: Comparison */
      Procp, /* [x]  procedure?: Procedure Properties */
      Quotient, /* [vv] quotient: Integer Operations */
      /* [x]  rational?: Reals and Rationals */
      /* [x]  read: Scheme Read */
      /* [x]  read-char?: Reading */
      /* [x]  real-part: Complex */
      Realp, /* [vv] real?: Reals and Rationals */
      Remainder, /* [vv] remainder: Integer Operations */
      /* [x]  reverse: Append/Reverse */
      Round, /* [vv] round: Arithmetic */
      SetCar, /* [vv] set-car!: Pairs */
      SetCdr, /* [vv] set-cdr!: Pairs */
      Sin, /* [vv] sin: Scientific */
      Sqrt, /* [vv] sqrt: Scientific */
      /* [x]  string: String Constructors */
      /* [x]  string->list: List/String Conversion */
      StringToNumber, /* [x]  string->number: Conversion */
      StringToSymbol, /* [vv] string->symbol: Symbol Primitives */
      StringAppend, /* [vx] string-append: Appending Strings: only two arguments supported */
      /* [x]  string-ci<: String Comparison */
      /* [x]  string-ci=?: String Comparison */
      /* [x]  string-ci>=?: String Comparison */
      /* [x]  string-ci>?: String Comparison */
      /* [x]  string-copy: String Selection */
      /* [x]  string-fill!: String Modification */
      StringLength, /* [vv] string-length: String Selection */
      StringRef, /* [x]  string-ref: String Selection */
      /* [x]  string-set!: String Modification */
      /* [x]  string<=?: String Comparison */
      StringLt, /* [vv]  string<?: String Comparison */
      /* [x]  string=?: String Comparison */
      /* [x]  string>=?: String Comparison */
      /* [x]  string>?: String Comparison */
      Stringp, /* [vv]  string?: String Predicates */
      /* [x]  substring: String Selection */
      SymbolToString, /* [vv] symbol->string: Symbol Primitives */
      Symbolp, /* [vv] symbol?: Symbol Primitives */
      Tan, /* [vv] tan: Scientific */
      /* [x]  truncate: Arithmetic */
      /* [x]  values: Multiple Values */
      MakeVector, /* [vv] make-vector: Vector Creation */
      Vector, /* [vv] vector: Vector Creation */
      /* [x]  vector->list: Vector Creation */
      /* [x]  vector-fill!: Vector Accessors */
      VectorLength, /* [vv] vector-length: Vector Accessors */
      VectorRef, /* [vv] vector-ref: Vector Accessors */
      VectorSet, /* [vv] vector-set!: Vector Accessors */
      Vectorp, /* [vv] vector?: Vector Creation */
      /* [x]  with-input-from-file: File Ports */
      /* [x]  with-output-to-file: File Ports */
      /* [x]  write-char: Writing */
      Zerop, /* [vv] zero?: Comparison */
      LessThan, /* [vv]  < */
      LessOrEqual, /* [vv]  <= */
      NumEq, /* [vv]  = */
      GreaterThan, /* [vv]  > */
      GreaterOrEqual, /* [vv]  >= */
      /* [x]  numerator */
      /* [x]  denominator */
      /* [x]  rationalize-string */
      /* [x]  scheme-report-environment */
      /* [x]  null-environment */
      /* [x]  write transcript-on */
      /* [x]  transcript-off */
      //Caar,
      //Cadr, /* [v]  caar etc. */
      //Cdar,
      //Cddr,
      //Caaar,
      //Caadr,
      //Cadar,
      //Caddr,
      //Cdaar,
      //Cdadr,
      //Cddar,
      //Cdddr,
      //Caaaar,
      //Caaadr,
      //Caadar,
      //Caaddr,
      //Cadaar,
      //Cadadr,
      //Caddar,
      //Cadddr,
      //Cdaaar,
      //Cdaadr,
      //Cdadar,
      //Cdaddr,
      //Cddaar,
      //Cddadr,
      //Cdddar,
      //Cddddr,
      /* Other primitives that are not R5RS */
      Random,
      Error,
      NewLock,
      Acquire,
      Release
    )

    abstract class SingleArgumentPrim(val name: String) extends SimplePrim {
      def fun: PartialFunction[Value, Value]
      def call(args: List[Value], position: Position) = args match {
        case x :: Nil =>
          if (fun.isDefinedAt(x)) {
            fun(x)
          } else {
            stackedException(s"$name ($position): invalid argument type $x")
          }
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    ////////////////
    // Arithmetic //
    ////////////////
    object Plus extends SimplePrim {
      val name = "+"
      val default: Value = Value.Integer(0)
      def call(args: List[Value], position: Position): Value = args.foldLeft(default)({
          case (Value.Integer(n1), Value.Integer(n2)) => Value.Integer(n1 + n2)
          case (Value.Integer(n1), Value.Real(n2)) => Value.Real(n1 + n2)
          case (Value.Real(n1), Value.Integer(n2)) => Value.Real(n1 + n2)
          case (Value.Real(n1), Value.Real(n2)) => Value.Real(n1 + n2)
          case (x, y) => stackedException(s"+ ($position): invalid argument types ($x and $y)")
      })
    }
    object Times extends SimplePrim {
      val name = "*"
      val default: Value = Value.Integer(1)
      def call(args: List[Value], position: Position): Value = args.foldLeft(default)({
        case (Value.Integer(n1), Value.Integer(n2)) => Value.Integer(n1 * n2)
          case (Value.Integer(n1), Value.Real(n2)) => Value.Real(n1 * n2)
          case (Value.Real(n1), Value.Integer(n2)) => Value.Real(n1 * n2)
          case (Value.Real(n1), Value.Real(n2)) => Value.Real(n1 * n2)
          case (x, y) => stackedException(s"* ($position): invalid argument types ($x and $y)")
      })
    }
    object Minus extends SimplePrim {
      val name = "-"
      def call(args: List[Value], position: Position) = args match {
        case Nil => stackedException("-: wrong number of arguments")
        case Value.Integer(x) :: Nil => Value.Integer(- x)
        case Value.Real(x) :: Nil => Value.Real(- x)
        case Value.Integer(x) :: rest => Plus.call(rest, position) match {
          case Value.Integer(y) => Value.Integer(x - y)
          case Value.Real(y) => Value.Real(x - y)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case Value.Real(x) :: rest => Plus.call(rest, position) match {
          case Value.Integer(y) => Value.Real(x - y)
          case Value.Real(y) => Value.Real(x - y)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case _ => stackedException(s"- ($position): invalid arguments $args")
      }
    }
    object Div extends SimplePrim {
      val name = "/"
      def call(args: List[Value], position: Position) = args match {
        case Nil => stackedException("/: wrong number of arguments")
        case Value.Integer(1) :: Nil => Value.Integer(1)
        case Value.Integer(x) :: Nil => Value.Real(1.0 / x)
        case Value.Real(x) :: Nil => Value.Real(1.0 / x)
        case Value.Integer(x) :: rest => Times.call(rest, position) match {
          case Value.Integer(y) => if (x % y == 0) { Value.Integer(x / y) } else { Value.Real(x.toDouble / y) }
          case Value.Real(y) => Value.Real(x / y)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case Value.Real(x) :: rest => Times.call(rest, position) match {
          case Value.Integer(y) => Value.Real(x / y)
          case Value.Real(y) => Value.Real(x / y)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case _ => stackedException(s"/ ($position): invalid arguments $args")
      }
    }

    object Modulo extends SimplePrim {
      val name = "modulo"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil if y != 0 =>
          Value.Integer(maf.lattice.MathOps.modulo(x, y))
        case _ :: _ :: Nil => stackedException(s"$name ($position): illegal computation: modulo zero")
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    object Abs extends SingleArgumentPrim("abs") {
      def fun = {
        case Value.Integer(x) => Value.Integer(scala.math.abs(x))
        case Value.Real(x) => Value.Real(scala.math.abs(x))
      }
    }
    abstract class DoublePrim(name: String, f: Double => Double)
        extends SingleArgumentPrim(name) {
      def fun = {
        case Value.Real(x) => Value.Real(f(x))
        case Value.Integer(x) => Value.Real(f(x.toDouble))
      }
    }
    object Sin extends DoublePrim("sin", scala.math.sin)
    object ASin extends DoublePrim("asin", scala.math.asin)
    object Cos extends DoublePrim("cos", scala.math.cos)
    object ACos extends DoublePrim("acos", scala.math.acos)
    object Tan extends DoublePrim("tan", scala.math.tan)
    object ATan extends DoublePrim("atan", scala.math.atan)
    object Log extends DoublePrim("log", scala.math.log)

    object Sqrt extends SingleArgumentPrim("sqrt") {
      def fun = {
        case Value.Integer(x) if x < 0 => stackedException(s"sqrt: negative argument $x")
        case Value.Real(x) if x < 0 => stackedException(s"sqrt: negative argument $x")
        case Value.Integer(x) =>
          val r = scala.math.sqrt(x.toDouble)
          if (r == r.floor) {
            Value.Integer(r.toInt)
          } else {
            Value.Real(r)
          }
        case Value.Real(x) => Value.Real(scala.math.sqrt(x))
      }
    }
    object Expt extends SimplePrim {
      val name = "expt"
      // TODO: expt should also preserve exactness if possible
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil =>
          Value.Integer(scala.math.pow(x.toDouble, y.toDouble).toInt)
        case Value.Integer(x) :: Value.Real(y) :: Nil =>
          Value.Real(scala.math.pow(x.toDouble, y))
        case Value.Real(x) :: Value.Integer(y) :: Nil =>
          Value.Real(scala.math.pow(x, y.toDouble))
        case Value.Real(x) :: Value.Real(y) :: Nil =>
          Value.Real(scala.math.pow(x, y))
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    object Ceiling extends SingleArgumentPrim("ceiling") {
      def fun = {
        case x: Value.Integer => x
        case Value.Real(x) => Value.Real(x.ceil)
      }
    }
    object Floor extends SingleArgumentPrim("floor") {
      def fun = {
        case x: Value.Integer => x
        case Value.Real(x) => Value.Real(x.floor)
      }
    }
    object Quotient extends SimplePrim {
      val name = "quotient"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Integer(x / y)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object Remainder extends SimplePrim {
      val name = "remainder"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Integer(x % y)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object Round extends SingleArgumentPrim("round") {
      def fun = {
        case x: Value.Integer => x
        case Value.Real(x) => Value.Real(maf.lattice.MathOps.round(x))
      }
    }
    object Evenp extends SingleArgumentPrim("even?") {
      def fun = {
        case Value.Integer(x) if x % 2 == 0 => Value.Bool(true)
        case _: Value.Integer => Value.Bool(false)
      }
    }
    object Oddp extends SingleArgumentPrim("odd?") {
      def fun = {
        case Value.Integer(x) if x % 2 == 1 => Value.Bool(true)
        case _: Value.Integer => Value.Bool(false)
      }
    }
    object Negativep extends SingleArgumentPrim("negative?") {
      def fun = {
        case Value.Integer(x) if x < 0 => Value.Bool(true)
        case _: Value.Integer => Value.Bool(false)
      }
    }
    object Positivep extends SingleArgumentPrim("positive?") {
      def fun = {
        case Value.Integer(x) if x > 0 => Value.Bool(true)
        case _: Value.Integer => Value.Bool(false)
      }
    }
    object Zerop extends SingleArgumentPrim("zero?") {
      def fun = {
        case Value.Integer(0) => Value.Bool(true)
        case _: Value.Integer => Value.Bool(false)
      }
    }

    object Max extends SimplePrim {
      val name = "max"
      def max(maximum: Value, rest: List[Value]): Value = rest match {
        case Nil => maximum
        case x :: rest => max(x match {
          case Value.Integer(n1) => maximum match {
            case Value.Integer(n2) => if (n1 > n2) { Value.Integer(n1) } else { maximum }
            case Value.Real(n2) =>
              val r = n1.toDouble
              if (r > n2) { Value.Real(r) } else { maximum }
            case v => throw new UnexpectedValueTypeException[Value](v)
          }
          case Value.Real(n1) => maximum match {
            case Value.Integer(n2) =>
              val r = n2.toDouble
              if (n1 > r) { Value.Real(n1) } else { maximum }
            case Value.Real(n2) => if (n1 > n2) { Value.Real(n1) } else { Value.Real(n2) }
            case v => throw new UnexpectedValueTypeException[Value](v)
          }
          case v => throw new UnexpectedValueTypeException[Value](v)
        }, rest)
      }
      def call(args: List[Value], position: Position): Value = args match {
        case Nil => stackedException(s"max ($position): wrong number of arguments")
        case Value.Integer(first) :: rest =>
          max(Value.Integer(first), rest)
        case Value.Real(first) :: rest =>
          max(Value.Real(first), rest)
        case _ => stackedException(s"max ($position): invalid arguments $args")
      }
    }
    object Min extends SimplePrim {
      val name = "min"
      def min(minimum: Value, rest: List[Value]): Value = rest match {
        case Nil => minimum
        case x :: rest => min(x match {
          case Value.Integer(n1) => minimum match {
            case Value.Integer(n2) => if (n1 < n2) { Value.Integer(n1) } else { minimum }
            case Value.Real(n2) =>
              val r = n1.toDouble
              if (r < n2) { Value.Real(r) } else { minimum }
            case v => throw new UnexpectedValueTypeException[Value](v)
          }
          case Value.Real(n1) => minimum match {
            case Value.Integer(n2) =>
              val r = n2.toDouble
              if (n1 < r) { Value.Real(n1) } else { minimum }
            case Value.Real(n2) => if (n1 < n2) { Value.Real(n1) } else { Value.Real(n2) }
            case v => throw new UnexpectedValueTypeException[Value](v)
          }
          case v => throw new UnexpectedValueTypeException[Value](v)
        }, rest)
      }
      def call(args: List[Value], position: Position): Value = args match {
        case Nil => stackedException(s"min ($position): wrong number of arguments")
        case Value.Integer(first) :: rest =>
          min(Value.Integer(first), rest)
        case Value.Real(first) :: rest =>
          min(Value.Real(first), rest)
        case _ => stackedException(s"min ($position): invalid arguments $args")
      }
    }
    object Gcd extends SimplePrim {
      val name = "gcd"
      def gcd(a: Int, b: Int): Int = if (b == 0) { a } else { gcd(b, a % b) }
      def call(args: List[Value], position: Position): Value.Integer = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Integer(gcd(x, y))
        case _ => stackedException(s"gcd ($position): invalid arguments $args")
      }
    }

    object LessThan extends SimplePrim {
      val name = "<"
      def call(args: List[Value], position: Position): Value.Bool = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Bool(x < y)
        case Value.Integer(x) :: Value.Real(y) :: Nil => Value.Bool(x < y)
        case Value.Real(x) :: Value.Integer(y) :: Nil => Value.Bool(x < y)
        case Value.Real(x) :: Value.Real(y) :: Nil => Value.Bool(x < y)
        case _ => stackedException(s"< ($position): invalid arguments $args")
      }
    }

    object LessOrEqual extends SimplePrim {
      val name = "<="
      def call(args: List[Value], position: Position): Value.Bool = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Bool(x <= y)
        case Value.Integer(x) :: Value.Real(y) :: Nil => Value.Bool(x <= y)
        case Value.Real(x) :: Value.Integer(y) :: Nil => Value.Bool(x <= y)
        case Value.Real(x) :: Value.Real(y) :: Nil => Value.Bool(x <= y)
        case _ => stackedException(s"<= ($position): invalid arguments $args")
      }
    }

    object GreaterThan extends SimplePrim {
      val name = ">"
      def call(args: List[Value], position: Position): Value.Bool = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Bool(x > y)
        case Value.Integer(x) :: Value.Real(y) :: Nil => Value.Bool(x > y)
        case Value.Real(x) :: Value.Integer(y) :: Nil => Value.Bool(x > y)
        case Value.Real(x) :: Value.Real(y) :: Nil => Value.Bool(x > y)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    object GreaterOrEqual extends SimplePrim {
      val name = ">="
      def call(args: List[Value], position: Position) = args match {
        case Value.Integer(x) :: Value.Integer(y) :: Nil => Value.Bool(x >= y)
        case Value.Integer(x) :: Value.Real(y) :: Nil => Value.Bool(x >= y)
        case Value.Real(x) :: Value.Integer(y) :: Nil => Value.Bool(x >= y)
        case Value.Real(x) :: Value.Real(y) :: Nil => Value.Bool(x >= y)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    object NumEq extends SimplePrim {
      val name = "="
      @scala.annotation.tailrec
      def numEqInt(first: Int, l: List[Value]): Value = l match {
        case Nil => Value.Bool(true)
        case Value.Integer(x) :: rest if x == first => numEqInt(first, rest)
        case (_: Value.Integer) :: _ => Value.Bool(false)
        case Value.Real(x) :: rest if x == first => numEqInt(first, rest)
        case (_: Value.Real) :: _ => Value.Bool(false)
        case _ => stackedException(s"=: invalid type of arguments $l")
      }
      @scala.annotation.tailrec
      def numEqReal(first: Double, l: List[Value]): Value = l match {
        case Nil => Value.Bool(true)
        case Value.Integer(x) :: rest if x == first => numEqReal(first, rest)
        case (_: Value.Integer) :: _ => Value.Bool(false)
        case Value.Real(x) :: rest if x == first => numEqReal(first, rest)
        case (_: Value.Real) :: _ => Value.Bool(false)
        case _ => stackedException(s"=: invalid type of arguments $l")
      }
      def call(args: List[Value], position: Position): Value = args match {
        case Nil => Value.Bool(true)
        case Value.Integer(x) :: rest => numEqInt(x, rest)
        case Value.Real(x) :: rest => numEqReal(x, rest)
        case _ => stackedException(s"$name ($position): invalid type of arguments $args")
      }
    }

    //////////////
    // Booleans //
    //////////////
    object Not extends SingleArgumentPrim("not") {
      def fun = {
        case Value.Bool(b) => Value.Bool(!b)
        case _ => Value.Bool(false) /* any non-bool value is considered true */
      }
    }

    /////////////////
    // Conversions //
    /////////////////
    object ExactToInexact extends SingleArgumentPrim("exact->inexact") {
      def fun = {
        case Value.Integer(x) => Value.Real(x.toDouble)
        case x: Value.Real => x
      }
    }
    object InexactToExact extends SingleArgumentPrim("inexact->exact") {
      def fun = {
        case x: Value.Integer => x
        case Value.Real(x) => Value.Integer(x.toInt) /* TODO: fractions */
      }
    }
    object NumberToString extends SingleArgumentPrim("number->string") {
      def fun = {
        case Value.Integer(x) => Value.Str(s"$x")
        case Value.Real(x) => Value.Str(s"$x")
      }
    }
    object SymbolToString extends SingleArgumentPrim("symbol->string") {
      def fun = {
        case Value.Symbol(x) => Value.Str(x)
      }
    }
    object StringToSymbol extends SingleArgumentPrim("string->symbol") {
      def fun = {
        case Value.Str(x) => Value.Symbol(x)
      }
    }
    object CharToInteger extends SingleArgumentPrim("char->integer") {
      def fun = {
        case Value.Character(c) => Value.Integer(c.toInt)
      }
    }
    object IntegerToChar extends SingleArgumentPrim("integer->char") {
      def fun = {
        case Value.Integer(n) => Value.Character(n.toChar)
      }
    }

    ////////
    // IO //
    ////////
    object Display extends SingleArgumentPrim("display") {
      def fun = {
        case x =>
          if (output) Out.prt(x)
          Value.Undefined(Identity.none)
      }
    }
    object Newline extends SimplePrim {
      val name = "newline"
      def call(args: List[Value], position: Position) = args match {
        case Nil =>
          if (output) Out.prtln("\n")
          Value.Undefined(Identity.none)
        case _ => stackedException(s"$name ($position): wrong number of arguments, 0 expected, got ${args.length}")
      }
    }
    object Error extends SimplePrim {
      val name = "error"
      def call(args: List[Value], position: Position) = stackedException(s"user-raised error ($position): $args")
    }

    /////////////////
    // Type checks //
    /////////////////
    object Booleanp extends SingleArgumentPrim("boolean?") {
      def fun = {
        case _: Value.Bool => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Charp extends SingleArgumentPrim("char?") {
      def fun = {
        case _: Value.Character => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Nullp extends SingleArgumentPrim("null?") {
      def fun = {
        case Value.Nil => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Pairp extends SingleArgumentPrim("pair?") {
      def fun = {
        case Value.Pointer(addr) => lookupStore(addr) match {
          case _: Value.Cons  => Value.Bool(true)
          case _              => Value.Bool(false)
        }
        case _ => Value.Bool(false)
      }
    }
    object Symbolp extends SingleArgumentPrim("symbol?") {
      def fun = {
        case _: Value.Symbol => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Stringp extends SingleArgumentPrim("string?") {
      def fun = {
        case _: Value.Str => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Integerp extends SingleArgumentPrim("integer?") {
      def fun = {
        case _: Value.Integer => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Realp extends SingleArgumentPrim("real?") {
      def fun = {
        case _: Value.Real => Value.Bool(true)
        case _: Value.Integer => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Numberp extends SingleArgumentPrim("number?") {
      def fun = {
        case _: Value.Integer => Value.Bool(true)
        case _: Value.Real => Value.Bool(true)
        case _ => Value.Bool(false)
      }
    }
    object Vectorp extends SingleArgumentPrim("vector?") {
      def fun = {
        case Value.Pointer(a) => lookupStore(a) match {
          case _ : Value.Vector => Value.Bool(true)
          case _ => Value.Bool(false)
        }
        case _ => Value.Bool(false)
      }
    }
    object Procp extends SingleArgumentPrim("procedure?") {
      def fun = {
        case Value.Clo(_, _, _) => Value.Bool(true)
        case _                  => Value.Bool(false)
      }
    }

    /////////////
    // Strings //
    /////////////
    object StringAppend extends SimplePrim {
      val name = "string-append"
      def call(args: List[Value], position: Position) =
        Value.Str(args.foldLeft("")((acc, v) => v match {
          case Value.Str(x) => s"$acc$x"
          case _ => stackedException(s"$name ($position): invalid argument $v")
        }))
    }
    object StringLength extends SingleArgumentPrim("string-length") {
      def fun = {
        case Value.Str(x) => Value.Integer(x.length)
      }
    }
    object StringRef extends SimplePrim {
      val name = "string-ref"
      def call(args: List[Value], position: Position): Value.Character = args match {
        case Value.Str(x) :: Value.Integer(n) :: Nil =>
          Value.Character(x(n))
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object StringLt extends SimplePrim {
      val name = "string<?"
      def call(args: List[Value], position: Position): Value.Bool = args match {
        case Value.Str(x) :: Value.Str(y) :: Nil => Value.Bool(x < y)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object StringToNumber extends SimplePrim {
      val name = "string->number"
      def call(args: List[Value], position: Position): Value.Integer = args match {
        case Value.Str(x) :: Nil if x.toIntOption.nonEmpty => Value.Integer(x.toIntOption.get)
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    ///////////////
    // Equality //
    //////////////

    object Eq extends SimplePrim {
      val name = "eq?"
      def call(args: List[Value], position: Position): Value.Bool = args match {
        case x :: y :: Nil => Value.Bool(x == y)
        case _ => stackedException(s"$name ($position): wrong number of arguments ${args.length}")
      }
    }
    /////////////
    // Vectors //
    /////////////
    object Vector extends Prim {
      val name = "vector"
      def newVector(fexp: SchemeFuncall, siz: Int, elms: Map[Int,Value], ini: Value): Value = {
        val ptr = newAddr(AddrInfo.PtrAddr(fexp))
        val vct = Value.Vector(siz, elms, ini)
        extendStore(ptr, vct)
        Value.Pointer(ptr)
      }
      def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = {
        val elms = args.map(_._2).zipWithIndex.map(_.swap).toMap
        newVector(fexp, args.size, elms, Value.Undefined(fexp.idn))
      }
    }
    object MakeVector extends Prim {
      val name = "make-vector"
      def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = args.map(_._2) match {
        case Value.Integer(size) :: Nil =>
          Vector.newVector(fexp, size, Map(), Value.Undefined(fexp.idn))
        case Value.Integer(size) :: init :: Nil =>
          Vector.newVector(fexp, size, Map(), init)
        case _ => stackedException(s"$name (${fexp.idn.pos}): invalid arguments $args")
      }
    }
    object VectorLength extends SingleArgumentPrim("vector-length") {
      def fun = {
        case Value.Pointer(a) => lookupStore(a) match {
          case Value.Vector(siz,_,_) => Value.Integer(siz)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
      }
    }
    object VectorRef extends SimplePrim {
      val name = "vector-ref"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Pointer(a) :: Value.Integer(idx) :: Nil => lookupStore(a) match {
          case Value.Vector(siz,els,ini) if idx >= 0 && idx < siz => els.getOrElse(idx, ini)
          case Value.Vector(siz,_,_) => stackedException(s"$name ($position): index $idx out of range (valid range: [0,${siz-1}])")
        }
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object VectorSet extends SimplePrim {
      val name = "vector-set!"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Pointer(a) :: Value.Integer(idx) :: v :: Nil => lookupStore(a) match {
          case Value.Vector(siz,els,ini) if idx >= 0 && idx < siz =>
            val updatedVct = Value.Vector(siz, els + (idx -> v), ini)
            extendStore(a, updatedVct)
            Value.Undefined(Identity.none)
          case Value.Vector(siz,_,_) => stackedException(s"$name ($position): index $idx out of range (valid range: [0,${siz-1}])")
        }
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    //////////
    // Cons //
    //////////

    object Car extends SingleArgumentPrim("car") {
      def fun = {
        case Value.Pointer(addr) => lookupStore(addr) match {
          case Value.Cons(car,_) => car
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
      }
    }
    object Cdr extends SingleArgumentPrim("cdr") {
      def fun = {
        case Value.Pointer(addr) => lookupStore(addr) match {
          case Value.Cons(_,cdr) => cdr
          case v => throw new UnexpectedValueTypeException[Value](v)
        }      
      }
    }
    object Cons extends Prim {
      val name = "cons"
      def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = args match {
        case (_, car) :: (_, cdr) :: Nil =>
          allocateCons(fexp, car, cdr)
        case _ => stackedException(s"cons: wrong number of arguments $args")
      }
    }
    object SetCar extends SimplePrim {
      val name = "set-car!"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Pointer(addr) :: v :: Nil => lookupStore(addr) match {
          case Value.Cons(_,cdr) => 
            extendStore(addr, Value.Cons(v,cdr))
            Value.Undefined(Identity.none)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }
    object SetCdr extends SimplePrim {
      val name = "set-cdr!"
      def call(args: List[Value], position: Position): Value = args match {
        case Value.Pointer(addr) :: v :: Nil => lookupStore(addr) match {
          case Value.Cons(car,_) => 
            extendStore(addr, Value.Cons(car,v))
            Value.Undefined(Identity.none)
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
        case _ => stackedException(s"$name ($position): invalid arguments $args")
      }
    }

    ///////////
    // Lists //
    ///////////
    object ListPrim extends Prim {
      val name = "list"
      def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = args match {
        case Nil => Value.Nil
        case (exp, head) :: rest =>
          allocateCons(exp, head, call(fexp, rest))
      }
    }
    ///////////
    // Other //
    ///////////
    object Random extends SingleArgumentPrim("random") {
      def fun = {
        case Value.Integer(x) => Value.Integer((scala.math.random() * x).toInt)
        case Value.Real(x) => Value.Real(scala.math.random() * x)
      }
    }

    ///////////
    // Locks //
    ///////////

    object NewLock extends Prim {
      val name = "new-lock"
      def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = args match {
        case Nil => 
          val addr = newAddr(AddrInfo.PtrAddr(fexp))
          val lock = Value.Lock(new java.util.concurrent.locks.ReentrantLock())
          extendStore(addr, lock)
          Value.Pointer(addr)
        case _   => stackedException(s"new-lock: invalid arguments $args")
      }
    }
    case object Acquire extends SingleArgumentPrim("acquire") {
      def fun = {
        case Value.Pointer(ptr) => lookupStore(ptr) match {
          case Value.Lock(lck) => 
            lck.lock()
            Value.Void
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
      }
    }
    case object Release extends SingleArgumentPrim("release") {
      def fun = {
        case Value.Pointer(ptr) => lookupStore(ptr) match {
          case Value.Lock(lck) => 
            lck.unlock()
            Value.Void
          case v => throw new UnexpectedValueTypeException[Value](v)
        }
      }
    }
  }
}

object SchemeInterpreter {
  sealed trait Value
  sealed trait AddrInfo
  trait Prim {
    val name: String
    def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value
  }
  trait SimplePrim extends Prim {
    def call(args: List[Value], position: Position): Value
    def call(fexp: SchemeFuncall, args: List[(SchemeExp,Value)]): Value = call(args.map(_._2), fexp.idn.pos)
  }
  type Addr = (Int, AddrInfo)
  type Env = Map[String, Addr]
  type Store = Map[Addr, Value]
  object AddrInfo {
    case class VarAddr(vrb: Identifier) extends AddrInfo
    case class PrmAddr(nam: String)     extends AddrInfo
    case class PtrAddr(exp: SchemeExp)  extends AddrInfo
    case class RetAddr(exp: SchemeExp)  extends AddrInfo
  }
  object Value {
    case class Undefined(idn: Identity) extends Value { override def toString: String = "<#undef>" } /* arises from undefined behavior */
    case class Unbound(id: Identifier) extends Value { override def toString: String = "<#unbound>" } /* only used for letrec */
    case class Clo(lambda: SchemeLambdaExp, env: Env, name: Option[String] = None) extends Value { override def toString: String = name.map(n => s"#$n ${lambda.idn.pos}").getOrElse(s"<#clo ${lambda.idn.pos}>") }
    case class Primitive(p: Prim) extends Value { override def toString: String = s"<#prim ${p.name}>" }
    case class Str(str: String) extends Value { override def toString: String = str }
    case class Symbol(sym: String) extends Value { override def toString: String = s"'$sym" }
    case class Integer(n: Int) extends Value { override def toString: String = n.toString }
    case class Real(r: Double) extends Value { override def toString: String = r.toString }
    case class Bool(b: Boolean) extends Value { override def toString: String = if (b) "#t" else "#f" }
    case class Pointer(v: Addr) extends Value { override def toString: String = s"<#ptr $v>" }
    case class Character(c: Char) extends Value {
      override def toString: String = c match {
        case ' ' => "#\\space"
        case '\n' => "#\\newline"
        case c => s"#\\$c"
      }
    }
    case object Nil extends Value { override def toString: String = "'()" }
    case class Cons(car: Value, cdr: Value) extends Value { override def toString: String = s"<#cons $car $cdr>" }
    case class Vector(size: Int, elems: Map[Int,Value], init: Value) extends Value { override def toString: String = s"<#vector[$size]>" }
    case class Thread(fut: Future[Value]) extends Value { override def toString: String = s"<thread>"}
    case class Lock(l: java.util.concurrent.locks.Lock) extends Value { override def toString: String = "<Lock>"}
    case object Void extends Value { override def toString: String = "<void>"}
  }


  import scala.concurrent.duration._
  import maf.language.scheme.primitives._
  val timeout = Duration(30, SECONDS)
  def main(args: Array[String]): Unit =
    if (args.size == 1) {
      val text = Reader.loadFile(args(0))
      val pgm = SchemeUndefiner.undefine(List(SchemePrelude.addPrelude(SchemeParser.parse(text), Set("newline", "display"))))
      val interpreter = new SchemeInterpreter((id, v) => (), true)
      val res = interpreter.run(pgm, Timeout.start(timeout))
      println(s"Result: $res")
    } else {
      println(s"Expected file to run as argument")
    }
}
