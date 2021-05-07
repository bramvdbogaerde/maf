package maf.modular.contracts

import maf.language.contracts.{ScExp, ScFunctionAp, ScIdentifier, ScNil, ScValue}
import maf.language.sexp.Value
import maf.language.scheme.interpreter.ConcreteValues
import maf.ScSettings

/**
 * Transforms a condition built using basic predicates from the soft contract language
 * into valid assertions for Z3,
 * @param condition the condition which must be checked
 * @param primitives: a map of primitives to names in Z3
 */
class ScSMTSolverJVM[V](
    condition: ScExp,
    primitives: Map[String, String] = Map(),
    injectValue: ConcreteValues.Value => Option[V] = ((_: ConcreteValues.Value) => None))
    extends ScSmtSolver {

  val DEBUG_MODE = ScSettings.DEBUG_SMT

  import com.microsoft.z3._
  import ScSMTSolverJVM._
  import maf.util.MonoidInstances._

  private var variables: Set[String] = Set()

  object ScAnd {
    def unapply(exp: ScExp): Option[(ScExp, ScExp)] = exp match {
      case ScFunctionAp(ScIdentifier("and", _), List(e1, e2), _, _) => Some((e1, e2))
      case _                                                        => None
    }
  }

  // create a new context and solver
  private val context = new Context()
  private lazy val solver = context.mkSolver()

  private val datasort: String =
    """
  (declare-datatypes ()
    ((V (VInt  (unwrap-int Int))
        (VBool (unwrap-bool Bool))
        (VProc (unwrap-proc Int))
        (VPai  (car V) (cdr V))
        (VNil)
        (VTypeErr)
        (VString (unwrap-string String))
        (VPrim (unwrap-prim String)))))
  """

  private val prelude: String =
    """
  (declare-fun char/c (V) V)

  (define-fun >/c ((v1 V) (v2 V)) V
     (VBool (> (unwrap-int v1) (unwrap-int v2))))
     
  (define-fun </c ((v1 V) (v2 V)) V
     (VBool (< (unwrap-int v1) (unwrap-int v2))))

  (define-fun =/c ((v1 V) (v2 V)) V
     (VBool (= (unwrap-int v1) (unwrap-int v2))))
     
  (define-fun string=?/c ((v1 V) (v2 V)) V
     (VBool (= (unwrap-string v1) (unwrap-string v2))))
     
  (define-fun int?/c ((v1 V)) V
     (VBool ((_ is VInt) v1)))
     
  (define-fun bool?/c ((v1 V)) V
     (VBool ((_ is VBool) v1)))
     
  (define-fun string?/c ((v1 V)) V
     (VBool ((_ is VString) v1)))
     
  (define-fun proc?/c ((v1 V)) Bool
     (or ((_ is VPrim) v1)
         ((_ is VProc) v1)))
         
   (define-fun null?/c ((v1 V)) V
     (VBool ((_ is VNil) v1)))

   (define-fun nonzero?/c ((v1 V)) V
     (VBool (not (= (unwrap-int v1) 0))))

   ;; everything is true except false
   (define-fun true?/c ((v1 V)) Bool
     (or ((_ is VInt) v1)
         ((_ is VProc) v1)
         ((_ is VPrim) v1)
         ((_ is VString) v1)
         (and ((_ is VBool) v1)
              (unwrap-bool v1))))


    (define-fun equal?/c ((v1 V) (v2 V)) V 
      (ite (and (is-VInt v1) (is-VInt v2))
           (VBool (= (unwrap-int v1)
              (unwrap-int v2)))
           (VBool false)))
           ;(ite (and (is-VBool v1) (is-VBool v2))
           ;     (VBool (and (unwrap-bool v1) (unwrap-bool v2)))
           ;     (ite (is-VProc v1) (is-VProc v2)
           ;          (VBool (= (unwrap-proc v1) (unwrap-proc v2)))
           ;          (ite (and (is-VNil v1) (is-VNil v2))
           ;               (VBool #t)
           ;               (VBool #f))))))
                        
    ;; only false is false
    (define-fun false?/c ((v1 V)) Bool
      (not (unwrap-bool v1)))
      
   (define-fun pair?/c ((v1 V)) V
     (VBool ((_ is VPai) v1)))

   (define-fun car/c ((v1 V)) V
     (car v1))

   (define-fun cdr/c ((v1 V)) V
     (cdr v1))

    (define-fun -/c ((v1 V) (v2 V)) V
      (VInt (- (unwrap-int v1) (unwrap-int v2))))
    
    (define-fun +/c ((v1 V) (v2 V)) V
      (VInt (+ (unwrap-int v1) (unwrap-int v2))))
      
    (define-fun */c ((v1 V) (v2 V)) V
      (VInt (- (unwrap-int v1) (unwrap-int v2))))
      
    (define-fun //c ((v1 V) (v2 V)) V
      (VInt (- (unwrap-int v1) (unwrap-int v2))))
      
    (define-fun or/c ((v1 V) (v2 V)) V
      (VBool (or (true?/c v1) (true?/c v2)))) 
      
    (define-fun and/c ((v1 V) (v2 V)) V
      (VBool (and (true?/c v1) (true?/c v2))))

    (declare-fun string-length (V) V)
      
    (define-fun not/c ((v1 V)) V
      (VBool (not (true?/c v1))))
      
    (define-fun bool?/c ((v1 Bool)) V
     (VBool true))
         
   (define-fun any?/c ((v1 V)) V
     (VBool true))
    """.stripMargin

  protected lazy val sortVName: Symbol =
    context.mkSymbol("V")

  protected lazy val sortV: DatatypeSort = {
    context.mkDatatypeSort(
      sortVName,
      Array(
        context.mkConstructor("VInt", "is-VInt", Array("unwrap-int"), Array(context.getIntSort()), null),
        context.mkConstructor("VBool", "is-VBool", Array("unwrap-bool"), Array(context.getBoolSort()), null),
        context.mkConstructor("VProc", "is-VPoc", Array("unwrap-proc"), Array(context.getIntSort()), null),
        context.mkConstructor("VPai", "is-VPai", Array("car", "cdr"), Array(null, null), Array(0, 0)),
        context.mkConstructor("VNil", "is-VNil", Array[String](), Array(), null),
        context.mkConstructor("VString", "is-VString", Array("unwrap-string"), Array(context.getStringSort()), null),
        context.mkConstructor("VPrim", "is-VPrim", Array("unwrap-prim"), Array(context.getStringSort()), null)
      )
    )
  }

  /** Computes the list of symbols from the variables */
  protected def symbols: Array[Symbol] =
    variables.map(context.mkSymbol).toArray

  /** Computes a list of symbols that can be added as declare-consts to the solver */
  protected def funDecls(symbols: Array[Symbol]): Array[FuncDecl] =
    symbols.map(v => context.mkConstDecl(v, sortV))

  def transformExpression(exp: ScExp, operand: Boolean = false): Option[String] =
    exp match {
      case ScIdentifier("dependent-contract?", _) => None
      case ScIdentifier(name, _) =>
        primitives.get(name) match {
          case Some(primitiveName) if operand => Some(primitiveName)
          case _ =>
            variables = variables + name
            Some(name)
        }
      case ScValue(value, _) =>
        value match {
          case Value.String(v)  => Some("(VString \"" + v + "\")")
          case Value.Integer(v) => Some(s"(VInt $v)")
          case Value.Boolean(v) => Some(s"(VBool $v)")
        }
      case ScFunctionAp(operator, operands, _, _) =>
        for {
          transformedOperator <- transformExpression(operator, operand = true)
          transformedOperands <- combineAllNonEmpty(operands.map(e => transformExpression(e)))
        } yield (s"($transformedOperator $transformedOperands)")

      case ScNil(_) => None
    }

  def transform(exp: ScExp): String = exp match {
    case ScAnd(e1, e2) =>
      transform(e1) ++ transform(e2)
    case _: ScFunctionAp =>
      transformExpression(exp) match {
        case Some(s) => s"(assert $s)\n"
        case None    => ""
      }
    case _ => ""
  }

  /**
   * Transforms the condition into valid Z3 assertions
   * @return valid Z3 assertions
   */
  private def transformed: String = {
    val assertions = transform(condition)
    //val constants = variables.toSet.map((v: String) => s"(declare-const ${v} V)").mkString("\n")
    assertions
  }

  /**
   * Checks if the current formula is satisfiable
   * @return true if the formale is satisfiable otherwise false
   */
  def isSat: Boolean = {
    import ScSMTSolver._
    isSatWithModel match {
      case Satisfiable(_) | Unknown => true
      case _                        => false
    }
  }

  def isSatWithModel: ScSMTSolver.Result[V] = {
    // transform the code
    val userCode = transformed

    if (DEBUG_MODE) {
      println(s"variables $variables")
      println(userCode)
    }
    val smtCode = prelude ++ userCode

    val variableSymbols = symbols
    val variableFunDecl = funDecls(symbols)
    val sortSymbols = Array(sortVName)
    val sorts = Array[Sort](sortV)

    // transform the textual representation of the assertions to the internal format of Z3
    val e: Array[BoolExpr] = context.parseSMTLIB2String(smtCode, sortSymbols, sorts, variableSymbols, variableFunDecl)

    // check whether their exist a model which satisfies all the constraints
    solver.assert_(e)
    val check = solver.check()

    // the PC is satisfiable when the SMT solver either indicates that the model is satisfiable or
    // it does not know if it is satisfiable.
    //
    // the unknown case is important as we are making an overapproximation, it would be unsound if we would ignore
    // paths that are not known with the SMT solver to be satisfiable

    import ScSMTSolver._
    check match {
      case Status.SATISFIABLE   => Satisfiable(getModel)
      case Status.UNKNOWN       => Unknown
      case Status.UNSATISFIABLE => Unsatisfiable
    }
  }

  protected def getModel: Map[String, V] = {
    import ConcreteValues.Value

    val model = solver.getModel()
    val constantsDecls = funDecls(symbols)
    val result = constantsDecls.map(model.getConstInterp(_)).filterNot(_ == null)
    val values: Array[Value] = result
      .map(u =>
        u.getFuncDecl().getName().toString match {
          case "VInt"  => Value.Integer(u.getArgs()(0).asInstanceOf[IntNum].getInt())
          case "VBool" => Value.Bool(u.getArgs()(0).asInstanceOf[BoolExpr].isTrue())
          case v =>
            println(v)
            // TODO
            println("Warn: unrecognized value")
            Value.Nil
        }
      )

    (values
      .zip(symbols.map(_.toString))
      .flatMap { case (v, k) =>
        injectValue(v) match {
          case Some(v) => Some((k, v))
          case None    => None
        }
      })
      .toMap
  }
}

object ScSMTSolverJVM {
  import com.microsoft.z3._
  implicit class Z3Solver(solver: Solver) {
    def assert_(expressions: Array[BoolExpr]): Unit =
      for (expression <- expressions)
        solver.add(expression)
  }
}
