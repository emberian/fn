; Driver for tools/bench/bp-drain-bench.lisp: N from the environment's
; argument list below; prints one line per drain.
(ld "bp-drain-bench.lisp")
(set-inhibit-output-lst '(proof-tree prove event summary))
(defun bn-report (tag n c)
  (declare (xargs :mode :program))
  (cw "BENCH ~s0 n=~x1 offers=~x2~%" tag n c))
(defmacro bn-timed (tag n form)
  `(mv-let (c s) (time$ ,form :msg "BENCHTIME ~s0 realtime ~st s runtime ~sc s alloc ~sa~%" :args (list ,tag))
     (declare (ignore s))
     (bn-report ,tag ,n c)))
(defun bn-run (n full)
  (declare (xargs :mode :program))
  (let ((st (time$ (if (<= n 1365) (bn-state n) (bn-state-copies n))
                   :msg "BENCHTIME setup realtime ~st s alloc ~sa~%")))
    (prog2$
     (cw "BENCH visits n=~x0 head=~x1 cursor=~x2~%" n
         (bn-count-head st nil 0) (bn-count-cursor st nil '(0 0 nil) 0))
     (prog2$
      (bn-timed (if full "head-full" "head-sel") n (bn-drain-head st nil full 0))
      (prog2$
       (bn-timed (if full "cursor-full" "cursor-sel") n (bn-drain-cursor st nil '(0 0 nil) full 0))
       (bn-timed (if full "transitions-full" "transitions-sel") n
                 (bn-transitions st (bn-keys 0 n nil) full 0)))))))
