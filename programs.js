const programs = [
      // These are all the ones that yield differences worth investigating
      // Different order of evaluation of let bindings?
      "test/R5RS/gabriel/dderiv.scm", // (let ((arg ((lambda unique_args_382 #f) 5 '())) (result ((lambda unique_args_374 '()) 0 '()))) (equal? '() result))
      "test/R5RS/scp1/cashdesk-counter.scm", // (letrec ((teller ((lambda unique_args_295 #f))) (_0 ((lambda unique_args_287 '()) 'toets)) (_3 teller)) '())
      "test/R5RS/scp1/twitter.scm", // (letrec ((res1 ((lambda unique_args_463 #f) 'username)) (_0 ((lambda unique_args_455 '()) 'output)) (_6 res1)) '())
      //
      // Bug: (eq?) and (eq? x) are valid in guile, but not in MAF. It's guile that deviates from R5RS
      "test/R5RS/various/values.scm", // (letrec ((string->number eq?) (_1 (string->number))) '())
      //
      // Bug: letrec can reference later bindings in the same letrec, does not work in MAF
      // It's actually guile that violates R5RS, as it states: "One restriction on letrec is very important: it must be possible to evaluate each <init> without assigning or referring to the value of any <variable>. If this restriction is violated, then it is an error. The restriction is necessary because Scheme passes arguments by value rather than by name. In the most common uses of letrec, all the <init>s are lambda expressions and the restriction is satisfied automatically. "
      "test/R5RS/WeiChenRompf2019/rsa.scm", // (letrec ((is-legal-public-exponent? e) (e 7)) '())
      //
      // Same bug: guile allows circular bindings, e.g., (letrec ((_0 _0)) _0), where _0 will have an unspecified value.
      "test/R5RS/scp1/parking-counter.scm",
      "test/R5RS/scp1/tree-with-branches.scm",
      "test/R5RS/various/eta.scm",
      "test/R5RS/various/four-in-a-row.scm",
      "test/R5RS/various/grid.scm",

      // The rest are due to either IO input (cat, wc, tail), or fractions (calc-e-and-cos, simpson-integral, third-root)
      // Note that there are some high variations due to missing fractions in MAF! For example on simpson-integral
      "test/R5RS/scp1/simpson-integral.scm",
       "test/R5RS/scp1/third-root.scm",
]

programs.forEach((program) => console.log(program))
