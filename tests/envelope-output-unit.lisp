; Constraint semantics are tested independently of core/codec machinery.
(in-package "ACL2")
(include-book "../sim/envelope-output")
(defun fn2-envelope-output-resume-check (constraints peer cut)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-envelope-output-state
  (mv-let (ok fn2-envelope-output-state)
   (let* ((fn2-envelope-output-state (fn2-envelope-output-init constraints peer fn2-envelope-output-state))
          (fn2-envelope-output-state (fn2-envelope-output-run cut fn2-envelope-output-state))
          (fn2-envelope-output-state
           (fn2-envelope-output-run (fn2-envelope-output-budget constraints peer) fn2-envelope-output-state)))
    (mv (and (equal (fn2-eo-phase fn2-envelope-output-state) 10)
             (fn2-eo-result fn2-envelope-output-state)) fn2-envelope-output-state)) ok)))
(assert-event
 (and (fn2-envelope-output-matches-p '((:exact 3) (:exact 1 2)) '(1 2 3))
      (not (fn2-envelope-output-matches-p '((:exact 3) (:exact 1 2)) '(1 2)))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3 4))
      (not (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 4)))
      (not (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3 4 5)))))
; Both ambiguous cases are necessary: always taking zero or always taking the
; longest uncertain prefix is wrong. The general path evaluates rows instead.
(assert-event
 (and (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(1))
      (fn2-envelope-output-matches-p '((:exact 1 2) (:prefix 1)) '(1 1 2))
      (fn2-envelope-output-matches-p '((:exact 2) (:prefix 1) (:prefix 1)) '(1 2))
      (not (fn2-envelope-output-matches-p '((:exact 2) (:prefix 1) (:prefix 1)) '(1 3 2)))
      (fn2-envelope-output-resume-check '((:exact 1 2) (:prefix 1)) '(1 1 2) 7)
      (fn2-envelope-output-resume-check '((:prefix 3 4) (:exact 1 2)) '(1 2 3) 3)))
; Malformed observations and constraint storage must fail in every path.
(assert-event
 (and (not (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(1 . 7)))
      (not (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(256)))
      (not (fn2-envelope-output-matches-p '((:prefix 1 . 7)) nil))
      (not (fn2-envelope-output-matches-p '((:prefix 1 256)) nil))
      (not (fn2-envelope-output-matches-p '((:bogus 1)) '(1)))
      (not (fn2-envelope-output-matches-p '((:exact 1) . 7) '(1)))
      (not (fn2-envelope-output-matches-p '(7) nil))))
