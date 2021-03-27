package maf.test.modular.contracts

import maf.language.contracts.ScLattice.Opq
import maf.modular.contracts.ScMain
import maf.test.{ScAnalysisTests, ScTests}

trait ScBigStepSemanticsTest extends ScTests with ScAnalysisTests {
  eval("(if OPQ 1 2)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.numTop)
  }

  eval("(+ 1 1)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(2))
  }

  eval("(* 2 3)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(6))
  }

  eval("(/ 6 2)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(3))

  }

  eval("(- 3 3)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(0))
  }

  eval("((lambda (x) x) 1)").tested { machine =>
    println(machine.getReturnValue(ScMain))
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(1))
  }

  eval("((lambda (x) (if (= x 0) x 0)) 0)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(0))
  }

  eval("((lambda (x) (if (= x 0) x 1)) 0)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(0))
  }

  eval("((lambda (x) (if (= x 0) 1 2)) OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.numTop)
  }

  eval("(int? 5)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(int? OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  // should retain type information although the final value is top
  eval("(int? (if (= OPQ 2) 5 6))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(int? (if (= OPQ 2) 5 OPQ))").tested { machine =>
    // we don't know whether OPQ is an int or not
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  eval("(int? (if (< 2 5) 5 OPQ))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(letrec (foo (lambda (x) (if (< x 1) 1 (+ (foo (+ x 1)) 1)))) (foo 42))").tested {
    // this is a test that checks whether the abstraction mechanism works, such that this infinite recursion
    // actually terminates in our analysis.
    machine =>
      machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.numTop)
  }

  eval("(nonzero? 5)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(nonzero? 0)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(nonzero? OPQ)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  eval("(proc? (lambda (x) x))").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(proc? +)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(proc? (mon (~> any? any?) (lambda (x) x)))").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(proc? 4)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(proc? OPQ)").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  eval("(dependent-contract? (~> any? any?))").tested { machine =>
    machine.summary.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  // an example of how the mon special form enriches the value it returns
  //eval("(mon int? OPQ)").tested { machine =>
  //  "Opq{int?}"
  //  machine.lattice.getOpq(machine.summary.getReturnValue(ScMain).get) shouldEqual Set(
  //    Opq(Set("int?"))
  //  )
  //}

  // an example of how the mon special form enriches the value it returns
  eval("(mon nonzero? (if (= 1 0) 0 1))").safe()

  /** Test that the OPQ value is refined to an integer */
  eval("(int? (mon int? OPQ))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(define (test a) (cadr a)) (cadr (cons 1 (cons 2 3)))")
    .tested { machine =>
      machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(2))
    }

  eval("(define/contract (f a) (~> int? int?) (+ a 1)) (f 5)").safe()

  /**
   * Unchecked does removes blame from the arguments of the function,
   * this should mostly be used for running tests or benchmarks where
   * we want to check whether f has the correct return value, but that
   * we assume that the input values are correct
   */
  eval("(define/contract (f x) (-> int? int?) x) (@unchecked f OPQ)").safe()

  /** Test if the semantics when running on a valid value are the same as the wrapped value */
  eval("((flat int?) 0)").tested { machine =>
    println(machine.getReturnValue(ScMain))
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("((flat int?) OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  eval("(letrec (zero? (flat (lambda (x) (= x 0)))) (mon zero? 1))").tested { machine =>
    println(machine)
  }

  //eval(
  //  "(define/contract (f x) (~> int? int?) x) f"
  //).tested { machine =>
  //  machine
  //    .getReturnValue(ScMain)
  //    .map(machine.lattice.getArr)
  //    .flatMap(_.headOption)
  //    .map(_.topLevel) shouldEqual Some(true)
  //}

  //eval(
  //  "(define (f x) (lambda (y) x)) (f 5)"
  //).tested { machine =>
  //  // TODO: shouldn't the returned lambda be treated as a non-local function for the analysis?
  //  machine
  //    .getReturnValue(ScMain)
  //    .map(machine.lattice.getClo)
  //    .flatMap(_.headOption)
  //    .map(_.topLevel) shouldEqual Some(false)
  //}

  /** A cons should evaluate to a cons pair */
  //eval("(cons 1 2)").tested { machine =>
  //  assert(
  //    machine
  //      .getReturnValue(ScMain)
  //      .map(machine.lattice.getCons)
  //      .isDefined
  //  )
  //}

  /** Tests on conditions */
  eval("(and #t #f)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(and #f #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(and #t #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(and OPQ OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.top)
  }

  eval("(or #t #f)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(or #f #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(or #f #f)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(or #f 4)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(4))
  }

  eval("(or 4 5)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(4))
  }

  eval("(or OPQ #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(or #t OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(or OPQ OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }

  eval("(or #t #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(not #t)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(false))
  }

  eval("(not #f)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.bool(true))
  }

  eval("(not OPQ)").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.top)
  }

  /** We should be able to get the car of a cons pair */
  eval("(car (cons 1 2))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(1))
  }

  /** We should be able to get the cdr of a cons pair */
  eval("(cdr (cons 1 2))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(2))
  }

  /** We should be able to define a function with variable number of arguments */
  eval("(define (list . args) args) (car (cdr (list 1 2 3)))").tested { machine =>
    machine.getReturnValue(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(2))
  }

  /** Testing whether provide contract works */
  eval("(define (f x) 5) (provide/contract (f (-> any? number?)))(f 5)").tested { machine =>
    assert(machine.summary.blames.isEmpty)
  }

  eval("(define (f x) #t) (provide/contract (f (-> any? number?))) (f 5)").tested { machine =>
    assert(machine.summary.blames.nonEmpty)
  }

  /** An integer literal should always pass the `int?` test */
  verify("int?", "5").named("flat_lit_int?").safe()

  /** An opaque value can be different from an integer, so this should not be verified as safe */
  verify("int?", "OPQ").named("flat_OPQ_int?").unsafe()

  /** Higher order contracts verification */
  verify("(or/c int? pair?)", "5").safe()

  verify("(or/c int? pair?)", "#t").unsafe()

  /** A contract from any to any should always be verified as safe */
  verify("(~> any? any?)", "(lambda (x) x)").applied().named("id_any2any").safe()

  verify("(~> any? int?)", "(lambda (x) 1)").applied().named("any2int_constant1").safe()

  verify("(~> any? int?)", "(lambda (x) OPQ)").applied().named("any2int_opq").unsafe()

  verify("(~> int? any?)", "(lambda (x) x)")
    .applied()
    .unsafe()

  verify("(~> nonzero? any?)", "(lambda (x) x)")
    .applied(value = "0")
    .unsafe()

  verify("(~> nonzero? any?)", "(lambda (x) x)")
    .applied(value = "1")
    .safe()

  // With the input of 1 this recursive function can return a zero number
  verify(
    "(~> any? nonzero?)",
    "(letrec (foo (lambda (x) (if (= x 1) 1 (- (foo (- x 1)) 1)))) foo)"
  ).applied()
    .unsafe()

  // This is the same as above, but the abstract interpretation keeps information about the type of the value.
  // in this case the value is Number(top) which is sufficient for int? to succeed
  verify(
    "(~> any? int?)",
    "(letrec (foo (lambda (x) (if (= x 0) 1 (- (foo (- x 1)) 1)))) foo)"
  ).applied(Set("int?"))
    .safe()

  // because we are using symbolic values with refinement sets, it should generate a blame on the domain contract
  // but not on the range contract
  verify("(~> int? int?)", "(lambda (x) x)").applied().checked { blames =>
    blames.size shouldEqual 1
  }

  verify("(~> int? int?)", "(lambda (x) OPQ)").tested { machine => }

  verify("(~> any? nonzero?)", "(lambda (x) (if (< x 2) (if (> x 2) 0 2) 2))")
    .applied(Set("int?"))
    .safe()

  verify("(~> any? nonzero?)", "(lambda (x) (if (< x 2) (if (< x 2) 0 2) 2))").applied().unsafe()

  // TODO: verify("(~> (~> any? int?) int?)", "(lambda (g) (g OPQ))").applied().unsafe()

  verify("(~> int? int?)", "(lambda (x) (letrec (y x) (begin (set! x #t) y)))")
    .applied(Set("int?"))
    .safeIf(machine => !machine.GLOBAL_STORE_ENABLED)

  /**
   * This should not be verified as safe, as the applied lambda changes x before returning it, this is to
   * test whether the store cache is correctly invalidated if the applied lambda captures variables
   */
  verify("(~> int? int?)", "(lambda (x) (begin ((lambda (y) (set! x #t)) OPQ) x))")
    .applied(Set("int?"))
    .unsafe()

  /*
  verify(
    "(~> int? int?)",
    "(lambda (x) (begin (assume (x int?) ((lambda (y) (set! x #t)) OPQ)) x))"
  ).applied(Set("int?"))
    .safe()
   */

  verify("(~> any? int?)", "(lambda (x) (letrec (y (OPQ int?)) (if (int? x) x y)))")
    .applied()
    .safe()

  verify("(~> any? int?)", "(lambda (x) (letrec (y (OPQ int?)) (if (int? x) x x)))")
    .applied()
    .unsafe()

  /** Test whether refined works on a both with an and in it */
  verify("(-> any? any? int?)", "(lambda (x y) (if (and (int? x) (int? y)) (+ x y) 0))")
    .applied2()
    .safe()

  /** Test whether refined works on a both with an and in it */
  verify("(-> any? any? int?)", "(lambda (x y) (if (and (int? x) #t) (+ x y) 0))")
    .applied2()
    .unsafe()

  /** Test that contracts for functions with no arguments work */
  verify("(-> number?)", "(lambda () 2)")
    .applied0()
    .safe()

  /* Test the letrec form wich returns a single value */
  verify("(-> number?)", "(lambda () (letrec (x 0) x))").applied0().safe()

  /* Test the letrec form with multiple bindings */
  eval("(letrec ((x 10) (y 5)) (+ x y))").tested { machine =>
    machine.summary.returnValues.get(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(15))
  }

  /* Test the let form with multiple bindings */
  eval("(let ((x 10) (y 5)) (+ x y))").tested { machine =>
    machine.summary.returnValues.get(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(15))
  }

  /* Test lambda with multiple expressions as the body */
  eval("((lambda (x) (set! x 10) x) 5)").tested { machine =>
    if (machine.GLOBAL_STORE_ENABLED) {
      machine.summary.returnValues.get(ScMain) shouldEqual Some(machine.lattice.schemeLattice.numTop)
    } else {
      machine.summary.returnValues.get(ScMain) shouldEqual Some(machine.lattice.schemeLattice.number(10))
    }
  }

  /** Test for issue with car where top would not be propably recognized, return zero successors state */
  eval("""
    (define (list-of-test cc) (lambda (v) (letrec (loop (lambda (lst) (if (null? lst) #t (and (cc (car lst)) (loop (cdr lst)))))) (loop v)))) 

    ((list-of-test int?) '(1 2 #t))""").tested { machine =>
    machine.summary.returnValues.get(ScMain) shouldEqual Some(machine.lattice.schemeLattice.boolTop)
  }
}
