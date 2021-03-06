(letrec ((i 100)
         (thread (lambda (n)
                 (if (<= i 0)
                     #t
                     (begin (set! i (- i 1)) (thread n)))))
(t1 (fork (thread 1)))
(t2 (fork (thread 2)))
(t3 (fork (thread 3)))
(t4 (fork (thread 4)))
(t5 (fork (thread 5)))
(t6 (fork (thread 6)))
(t7 (fork (thread 7))))
(join t1)
(join t2)
(join t3)
(join t4)
(join t5)
(join t6)
(join t7))