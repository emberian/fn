; Writes the fuzz cases and the grammar's verdicts for tests/grammar-fuzz-oracle.py,
; one FUZZ-CASE row per case: (mask class seed octets events), EVENTS being
; (code s e) per framed command line.
;   tools/acl2 < fn2/tests/grammar-fuzz-export.lsp > build/nntp-fuzz-cases.txt
(in-package "ACL2")
(set-cbd "fn2/tests/")
(include-book "grammar-fuzz")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(defun fn2-gfe-lines (evs)
  (declare (xargs :verify-guards nil))
  (if (atom evs) nil
    (append (and (eq (car (car evs)) :command)
                 (list (list (nth 1 (car evs)) (nth 16 (car evs)) (nth 17 (car evs)))))
            (fn2-gfe-lines (cdr evs)))))
(defun fn2-gfe-case (seed class mask)
  (declare (xargs :verify-guards nil))
  (let ((case (fn2-gf-case seed class mask)))
    (and case
         (cw "FUZZ-CASE ~x0~%"
             (list mask class seed (car case)
                   (fn2-gfe-lines (nth 3 (fn2-nntp-run (car case) nil mask))))))))
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
