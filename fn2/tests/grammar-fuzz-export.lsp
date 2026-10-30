; Writes the fuzz cases and the grammar's verdicts for tests/grammar-fuzz-oracle.py,
; one FUZZ-CASE row per case: (mask class seed octets events), EVENTS being
; (code s e answer) per framed command line, ANSWER the status code the
; connection's decision table (books/conn-answer.lisp) gives that line alone.
;   tools/acl2 < fn2/tests/grammar-fuzz-export.lsp > build/nntp-fuzz-cases.txt
(in-package "ACL2")
(set-cbd "fn2/tests/")
(include-book "grammar-fuzz")
(include-book "../books/conn-answer")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
; The decision table's status code for the line [s, e) of OCTETS alone.
(defun fn2-gfe-put (octets slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen 1 1 1 fn2-pool)
      (declare (ignore code)) (fn2-gfe-put (cdr octets) slot gen fn2-pool))))
(defun fn2-gfe-answer (line mask)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
        (mv-let (c1 slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
          (declare (ignore c1))
          (mv-let (c2 tslot tgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
            (declare (ignore c2))
            (let ((fn2-pool (fn2-gfe-put line slot gen fn2-pool)))
              (mv-let (code after pending fn2-pool)
                (fn2-answer 0 (len line) mask :none nil 0 0 slot gen tslot tgen 1 1 1 fn2-pool)
                (declare (ignore code after pending))
                (mv-let (ok0 d0) (fn2-gram-read tslot tgen 0 1 1 1 fn2-pool)
                  (mv-let (ok1 d1) (fn2-gram-read tslot tgen 1 1 1 1 fn2-pool)
                    (mv-let (ok2 d2) (fn2-gram-read tslot tgen 2 1 1 1 fn2-pool)
                      (mv (if (and ok0 ok1 ok2) (+ (* 100 (- d0 48)) (* 10 (- d1 48)) (- d2 48)) 0)
                          fn2-pool)))))))))
      result)))
(defun fn2-gfe-lines (evs octets mask)
  (declare (xargs :verify-guards nil))
  (if (atom evs) nil
    (append (and (eq (car (car evs)) :command)
                 (let ((s (nth 16 (car evs))) (e (nth 17 (car evs))))
                   (list (list (nth 1 (car evs)) s e
                               (fn2-gfe-answer (take (- e s) (nthcdr s octets)) mask)))))
            (fn2-gfe-lines (cdr evs) octets mask))))
(defun fn2-gfe-case (seed class mask)
  (declare (xargs :verify-guards nil))
  (let ((case (fn2-gf-case seed class mask)))
    (and case
         (cw "FUZZ-CASE ~x0~%"
             (list mask class seed (car case)
                   (fn2-gfe-lines (nth 3 (fn2-nntp-run (car case) nil mask)) (car case) mask))))))
(defun fn2-gfe-classes (classes seed mask)
  (declare (xargs :verify-guards nil))
  (if (atom classes) nil
    (prog2$ (fn2-gfe-case seed (car classes) mask) (fn2-gfe-classes (cdr classes) seed mask))))
(defun fn2-gfe-masks (masks seed)
  (declare (xargs :verify-guards nil))
  (if (atom masks) nil (prog2$ (fn2-gfe-classes *fn2-gf-classes* seed (car masks)) (fn2-gfe-masks (cdr masks) seed))))
(defun fn2-gfe-seeds (n seed)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix seed)))))
  (if (>= (nfix seed) (nfix n)) nil (prog2$ (fn2-gfe-masks *fn2-gf-masks* (nfix seed)) (fn2-gfe-seeds n (+ 1 (nfix seed))))))
(value-triple (cw "FUZZ-MASKS ~x0~%" (list *fn2-nntp-state-reader* *fn2-nntp-state-peer* *fn2-nntp-state-authenticated*)))
(value-triple (fn2-gfe-seeds 64 0))
(value-triple (cw "FUZZ-END~%"))
(good-bye)
